(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac rclia := lia.
Ltac rcnia := nia.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section h.
Variable segs : list Segment.
Lemma interp_eff0_grows : forall t m c m',
interp_eff0 segs t m = MachineOk (c, m') -> mem_grows m m'.
Proof.
induction t as [c0| | | | | |n a k IH|n a v k IH]; intros m c1 m' H; cbn [interp_eff0] in H;
try discriminate.
- injection H as <- <-. apply mem_grows_refl.
- destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate]. eapply IH. exact H.
- destruct (store_ok segs m a (width_bytes n)); [|discriminate].
eapply mem_grows_trans; [apply write_to_mem_grows|]. eapply IH. exact H.
Qed.
Lemma decode_exec_grows : forall st w st',
decode_exec segs st w = MachineOk st' -> mem_grows (ms_mem st) (ms_mem st').
Proof.
intros st w st' H. rewrite decode_exec_compat in H.
destruct (is_ecall w).
- injection H as <-. cbn. apply mem_grows_refl.
- destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
destruct (interp_eff0 segs _ (ms_mem st)) as [[c m']| |] eqn:Hi; try discriminate.
injection H as <-. cbn. eapply interp_eff0_grows. exact Hi.
Qed.
Lemma fetch_failure_not_ok : forall m a st', fetch_failure segs m a = MachineOk st' -> False.
Proof.
intros m a st' H. unfold fetch_failure in H.
destruct (negb _); [discriminate|]. destruct (_ || _ || _)%bool; discriminate.
Qed.
Lemma step_mem_grows : forall st st',
RiscvSemantics.step segs st = MachineOk st' -> mem_grows (ms_mem st) (ms_mem st').
Proof.
intros st st' H. unfold RiscvSemantics.step, step_accesses in H.
destruct (fetch_word segs (ms_pc st)) as [w|].
{ eapply decode_exec_grows. unfold decode_exec. exact H. }
destruct (fetch_word_ov segs (ms_mem st) (ms_pc st)) as [w|].
{ eapply decode_exec_grows. unfold decode_exec. exact H. }
destruct (fetch_tail_any segs (ms_mem st) (ms_pc st)) as [w|].
{ eapply decode_exec_grows. unfold decode_exec. exact H. }
destruct (fetch_failure segs (ms_mem st) (ms_pc st)) eqn:Hf; try discriminate.
exfalso. eapply fetch_failure_not_ok. exact Hf.
Qed.
Lemma msteps_mem_grows : forall ms ms',
msteps segs ms ms' -> mem_grows (ms_mem ms) (ms_mem ms').
Proof.
intros ms ms' H. induction H as [ms | ms ms1 ms2 Hp Hs Hm IH].
- apply mem_grows_refl.
- eapply mem_grows_trans; [eapply step_mem_grows; exact Hs | exact IH].
Qed.
Lemma present_grows : forall m m' a, mem_grows m m' -> present m a -> present m' a.
Proof.
intros m m' a Hg [b Hb]. unfold present.
destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
exfalso. apply (Hg (Z_to_bv 64 a)); [rewrite Hb; discriminate | exact E].
Qed.
Definition Ereg (regs : bvmap 5 word) (extra : list word) : env :=
mkEnv (fun i => if (i <? 32)%nat then getr regs (Z_to_bv 5 (Z.of_nat i)) else nth (i - 32) extra (Z_to_bv 64 0))
(fun _ => []).
Definition sr_atoms : list sv := SLit 0 :: atom_regs 1 31.
Lemma ew_Ereg_reg : forall regs extra (r : reg), ew (Ereg regs extra) (Z.to_nat (bv_unsigned r)) = getr regs r.
Proof.
intros regs extra r. unfold Ereg. cbn [ew]. pose proof (u5_range r).
destruct (Z.to_nat (bv_unsigned r) <? 32)%nat eqn:E.
- f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
change (2 ^ Z.of_N 5)%Z with 32. rewrite Z2Nat.id by lia. rewrite Z.mod_small by lia. reflexivity.
- apply Nat.ltb_ge in E. lia.
Qed.
Lemma ew_Ereg_lt : forall regs extra i, (i < 32)%nat ->
ew (Ereg regs extra) i = getr regs (Z_to_bv 5 (Z.of_nat i)).
Proof. intros regs extra i Hi. unfold Ereg. cbn [ew]. destruct (i <? 32)%nat eqn:E; [reflexivity|]. apply Nat.ltb_ge in E. lia. Qed.
Lemma ew_Ereg_extra : forall regs extra j,
ew (Ereg regs extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof.
intros regs extra j. unfold Ereg. cbn [ew].
destruct (32 + j <? 32)%nat eqn:E; [apply Nat.ltb_lt in E; lia|]. f_equal. lia.
Qed.
Lemma ew_Ereg_nat : forall regs extra n (r : reg), Z.of_nat n = bv_unsigned r ->
ew (Ereg regs extra) n = getr regs r.
Proof.
intros regs extra n r H. rewrite <- (ew_Ereg_reg regs extra r). f_equal. lia.
Qed.
Lemma regs_ok_Ereg : forall regs extra, regs_ok (Ereg regs extra) sr_atoms regs.
Proof.
intros regs extra. apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr];
[ match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
cbn [sv_denot];
first [ rewrite getr_zero; reflexivity
| rewrite Z.add_0_r, ew_Ereg_lt by lia;
match goal with |- _ = Z_to_bv 64 (bv_unsigned (getr regs ?x)) =>
let y := eval vm_compute in x in change x with y end;
rewrite Z_to_bv_bv_unsigned; reflexivity ]
| ]).
destruct Hr.
Qed.
Definition RET_WORD : Z := 0x00008067.
Lemma decode_ret : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma SR_ret_at : forall tbl E ss ms md Q,
table_ok segs tbl ->
m_halted md = None -> m_vm_lazy md = [] ->
st_ok segs E ss ms -> ss_resv ss = None ->
clookup tbl (ss_pc ss) = Some RET_WORD ->
Q (mkCfg (mkst (ms_regs ms) (v_jalr (getr (ms_regs ms) 1) 0) (ms_mem ms) (seg_rom segs)) md) ->
SR segs (mkCfg ms md) Q.
Proof.
intros tbl E ss ms md Q Htbl Hh Hl HS Hrv Hpc HQ.
pose proof (st_ok_mkst segs E ss ms HS Hrv) as Hshape. rewrite Hshape.
eapply SR_step; [exact Hh | exact Hl | reflexivity | | apply SR_ret; exact HQ].
change 0 with (bv_signed (0%bv : bv 12)).
eapply (step_jalr_x0 segs _ _ _ _ (0x00008067%bv : bv 32) 1 (0%bv : bv 12)).
- rewrite <- (Z_to_bv_bv_unsigned 32 (0x00008067%bv : bv 32)). apply Htbl. exact Hpc.
- reflexivity.
- exact decode_ret.
- reflexivity.
Qed.
Definition val_mem (mem : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
forall k, (k < n)%nat -> mbyte segs mem (a + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v n k)).
Lemma val_mem_word_mem : forall mem a v, val_mem mem a 8 v <-> word_mem segs mem a v.
Proof. intros mem a v. unfold val_mem, word_mem. split; intros H k Hk; apply H; exact Hk. Qed.
Lemma le_byte_small : forall v n k, 0 <= v < 2 ^ (8 * Z.of_nat n) -> (k < n)%nat ->
Z_to_bv 8 (le_byte v n k) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
intros v n k Hv Hk. unfold le_byte. rewrite (Z.mod_small v) by exact Hv.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma chunk_ok_val : forall E mem base off (n : N) (e : sv) v,
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> (Z.of_N n <= 8) ->
val_mem mem (base + off) (N.to_nat n) v ->
chunk_ok segs E mem base (mkChunk off (CVal n e)).
Proof.
intros E mem base off n e v He Hv Hn H i Hi. cbn [c_off c_val c_len cv_len] in *.
pose proof (N_nat_Z n) as Hnn.
assert (Hv64 : 0 <= v < 2 ^ 64).
{ split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hv)|]. apply Z.pow_le_mono_r; lia. }
exists (Z_to_bv 8 (Z.shiftr v (8 * i))). split.
- cbn [cbyte]. rewrite He. unfold byte_of_word. rewrite Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
- specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia.
replace (base + off + i) with (base + off + i) by lia. rewrite H. f_equal.
rewrite le_byte_small; [| rewrite N_nat_Z; lia | lia]. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma val_of_chunk_ok : forall E mem base off (n : N) (e : sv) v,
chunk_ok segs E mem base (mkChunk off (CVal n e)) ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> (Z.of_N n <= 8) ->
val_mem mem (base + off) (N.to_nat n) v.
Proof.
intros E mem base off n e v H He Hv Hn k Hk. unfold chunk_ok in H. cbn [c_off c_val c_len cv_len] in H.
pose proof (N_nat_Z n) as Hnn.
assert (Hv64 : 0 <= v < 2 ^ 64).
{ split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hv)|]. apply Z.pow_le_mono_r; lia. }
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [cbyte] in Hb1. rewrite He in Hb1.
unfold byte_of_word in Hb1. rewrite Z_to_bv_unsigned in Hb1.
unfold bv_wrap, bv_modulus in Hb1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hb1. rewrite Z.mod_small in Hb1 by lia.
injection Hb1 as <-. rewrite Hb2. f_equal. symmetry. apply le_byte_small; [rewrite N_nat_Z; lia | lia].
Qed.
Lemma chunk_ok_zero : forall E mem base off len,
(forall i, 0 <= i < len -> mbyte segs mem (base + off + i) = Some (Z_to_bv 8 0)) ->
chunk_ok segs E mem base (mkChunk off (CZero len)).
Proof.
intros E mem base off len H i Hi. cbn [c_off c_val c_len cv_len cbyte] in *.
exists (Z_to_bv 8 0). split; [reflexivity | apply H; exact Hi].
Qed.
Lemma region_ok_transport : forall E E' mem mem' r,
region_ok segs E mem r ->
base_val E' (r_base r) = base_val E (r_base r) ->
(forall c, In c (r_chunks r) -> match c_val c with CVal _ e => sv_denot E' e = sv_denot E e | CData _ _ _ => False | _ => True end) ->
(forall a, base_val E (r_base r) + r_lo r <= a < base_val E (r_base r) + r_hi r ->
mbyte segs mem' a = mbyte segs mem a) ->
(forall a, base_val E (r_base r) + r_wlo r <= a < base_val E (r_base r) + r_whi r ->
writable_at segs mem a -> writable_at segs mem' a) ->
forallb (chunk_inside r) (r_chunks r) = true ->
region_ok segs E' mem' r.
Proof.
intros E E' mem mem' r HR Hb Hcv Hrd Hwr Hin. unfold region_ok in HR. cbv zeta in HR.
destruct HR as (Hlo & Hhi & Hw & Hcs).
unfold region_ok. cbv zeta. rewrite Hb. split; [exact Hlo|]. split; [exact Hhi|]. split.
- intros o Ho. apply Hwr; [lia|]. apply Hw. exact Ho.
- apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
pose proof (proj1 (forallb_forall _ _) Hin c Hc) as Hci. unfold chunk_inside in Hci.
apply andb_prop in Hci as [Hci Hc3]. apply andb_prop in Hci as [Hc1 Hc2].
apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. apply Z.leb_le in Hc3.
intros i Hi. destruct (Hck i Hi) as (b & Hb1 & Hb2). exists b. split.
+ specialize (Hcv c Hc). destruct (c_val c) as [w e|len|len|d s len]; cbn [cbyte] in *;
[rewrite Hcv; exact Hb1 | exact Hb1 | exact Hb1 | destruct Hcv].
+ rewrite Hrd; [exact Hb2|]. unfold c_len in *. lia.
Qed.
Lemma branch_ne_U : forall E a b,
branch_taken BC_NE (sv_denot E a) (sv_denot E b) = negb (U E a =? U E b).
Proof. intros E a b. reflexivity. Qed.
Lemma branch_eq_U : forall E a b,
branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = (U E a =? U E b).
Proof. intros E a b. reflexivity. Qed.
Lemma branch_ltu_U : forall E a b,
branch_taken BC_LTU (sv_denot E a) (sv_denot E b) = (U E a <? U E b).
Proof. intros E a b. cbn [branch_taken]. unfold bv_ltu, U. reflexivity. Qed.
Lemma branch_geu_U : forall E a b,
branch_taken BC_GEU (sv_denot E a) (sv_denot E b) = negb (U E a <? U E b).
Proof. intros E a b. cbn [branch_taken]. unfold bv_ltu, U. reflexivity. Qed.
Lemma U_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff n 0) = v.
Proof.
intros E n v H Hv. rewrite U_SOff, H, Z.add_0_r. rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma U_atom_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> U E (SOff n c) = v + c.
Proof.
intros E n v c H Hv Hc. rewrite U_SOff, H. rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma U_lit : forall E z, 0 <= z < 2 ^ 64 -> U E (SLit z) = z.
Proof. intros E z Hz. rewrite U_SLit. apply zcanon_id. unfold M64. lia. Qed.
Lemma U_and_lit : forall E a m, 0 <= m < 2 ^ 64 -> U E (SAlu ALU_AND a (SLit m)) = Z.land (U E a) m.
Proof.
intros E a m Hm. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (zcanon_id m) by (unfold M64; lia).
pose proof (Z_land_upper (U E a) m ltac:(lia)). apply zcanon_id. unfold M64. lia.
Qed.
Lemma U_zext : forall E w a, U E (SExt false w a) = U E a mod 2 ^ Z.of_N w.
Proof.
intros E w a. rewrite U_SExt. pose proof (U_range E a).
assert (0 < 2 ^ Z.of_N w) by (apply Z.pow_pos_nonneg; lia).
pose proof (Z.mod_pos_bound (U E a) (2 ^ Z.of_N w) ltac:(lia)).
pose proof (Z.mod_le (U E a) (2 ^ Z.of_N w) ltac:(lia) ltac:(lia)).
apply zcanon_id. unfold M64 in *. lia.
Qed.
Lemma land_mod256_4 : forall v, 0 <= v -> Z.land (v mod 256) 4 = Z.land v 4.
Proof.
intros v Hv. change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia.
rewrite <- Z.land_assoc. reflexivity.
Qed.
Lemma land_mod256_1 : forall v, 0 <= v -> Z.land (v mod 256) 1 = Z.land v 1.
Proof.
intros v Hv. change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia.
rewrite <- Z.land_assoc. reflexivity.
Qed.
Lemma regs_kept_of_st_ok : forall E ss ms regs0 extra (l : list reg),
st_ok segs E ss ms -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) l = true ->
forall r, In r l -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms regs0 extra l HS [HA _] Hl r Hr.
pose proof (proj1 (forallb_forall _ _) Hl r Hr) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
rewrite (st_ok_reg segs E ss ms r HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite HA. 2:{ pose proof (u5_range r). lia. }
rewrite ew_Ereg_reg, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma denot_add_mul3 : forall E n m i b,
ew E n = Z_to_bv 64 i -> 0 <= i < 256 -> ew E m = Z_to_bv 64 b -> 0 <= b -> b + 3 * i < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (b + 3 * i).
Proof.
intros E n m i b Hn Hi Hm Hb Hnw. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E n i Hn) by lia. rewrite (U_atom E m b Hm) by lia. rewrite U_SLit.
rewrite (zcanon_id 3) by (unfold M64; lia). rewrite (zcanon_id (i * 3)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma U_add_mul3 : forall E n m i b,
ew E n = Z_to_bv 64 i -> 0 <= i < 256 -> ew E m = Z_to_bv 64 b -> 0 <= b -> b + 3 * i < 2 ^ 64 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 3)) (SOff m 0)) = b + 3 * i.
Proof.
intros E n m i b Hn Hi Hm Hb Hnw. unfold U. rewrite (denot_add_mul3 E n m i b Hn Hi Hm Hb Hnw).
apply unsigned_lit_small. lia.
Qed.
Lemma SR_branch_J : forall E ss ms md Q c a b,
st_ok segs E ss ms ->
(branch_taken c (sv_denot E a) (sv_denot E b) = true -> st_ok segs E (add_cond ss (mkAC c a b)) ms ->
SR segs (mkCfg ms md) Q) ->
(branch_taken c (sv_denot E a) (sv_denot E b) = false -> st_ok segs E (add_cond ss (mkAC (neg_bc c) a b)) ms ->
SR segs (mkCfg ms md) Q) ->
SR segs (mkCfg ms md) Q.
Proof.
intros E ss ms md Q c a b HS Ht Hf.
destruct (branch_taken c (sv_denot E a) (sv_denot E b)) eqn:Hb.
- apply Ht; [reflexivity|]. apply st_ok_add_cond; [exact HS | exact Hb].
- apply Hf; [reflexivity|]. apply st_ok_add_cond_neg; [exact HS | exact Hb].
Qed.
Lemma entry_st_ok : forall pc regs extra (rs : smem) (fs : list (nat * afact)) mem,
regions_wf rs = true ->
Forall (region_ok segs (Ereg regs extra) mem) rs ->
pairwise_disjoint (Ereg regs extra) rs ->
atoms_ok (Ereg regs extra) fs ->
st_ok segs (Ereg regs extra) (mkSS pc sr_atoms rs None (mkFacts fs [] []))
(mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)).
Proof.
intros pc regs extra rs fs mem Hwf Hrs Hpd Hfs.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [apply regs_ok_Ereg|]. split.
- split; [exact Hwf|]. split; [exact Hrs | exact Hpd].
- split; [exact Hfs|]. split; exact I.
Qed.
Lemma regs_ok_pin : forall E sr regs (r : reg) e,
regs_ok E sr regs -> r <> 0%bv -> getr regs r = sv_denot E e -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e HR Hr0 He.
pose proof (regs_ok_set E sr regs r (getr regs r) e HR (eq_sym He)) as H.
destruct (bv_eqb r 0) eqn:Hb; [apply bv_eqb_eq in Hb; congruence|].
intros x. rewrite <- (H x). destruct (base.decide (x = r)) as [->|Hne].
- rewrite getr_same by exact Hr0. reflexivity.
- rewrite getr_other by exact Hne. reflexivity.
Qed.
Lemma entry_st_ok_gen : forall pc sr regs extra (rs : smem) (fs : list (nat * afact)) mem,
regs_ok (Ereg regs extra) sr regs ->
regions_wf rs = true ->
Forall (region_ok segs (Ereg regs extra) mem) rs ->
pairwise_disjoint (Ereg regs extra) rs ->
atoms_ok (Ereg regs extra) fs ->
st_ok segs (Ereg regs extra) (mkSS pc sr rs None (mkFacts fs [] []))
(mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)).
Proof.
intros pc sr regs extra rs fs mem Hsr Hwf Hrs Hpd Hfs.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact Hsr|]. split.
- split; [exact Hwf|]. split; [exact Hrs | exact Hpd].
- split; [exact Hfs|]. split; exact I.
Qed.
Lemma entry_st_ok_full : forall pc sr regs extra (rs : smem) (G : facts) mem,
regs_ok (Ereg regs extra) sr regs ->
regions_wf rs = true ->
Forall (region_ok segs (Ereg regs extra) mem) rs ->
pairwise_disjoint (Ereg regs extra) rs ->
facts_ok (Ereg regs extra) G ->
st_ok segs (Ereg regs extra) (mkSS pc sr rs None G)
(mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)).
Proof.
intros pc sr regs extra rs G mem Hsr Hwf Hrs Hpd HG.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact Hsr|]. split; [| exact HG].
split; [exact Hwf|]. split; [exact Hrs | exact Hpd].
Qed.
Lemma region_ok_stack : forall E mem n sp lo,
bv_unsigned (ew E n) = sp -> 0 <= sp + lo -> sp <= 2 ^ 64 ->
(forall a, sp + lo <= a < sp -> writable_at segs mem a) ->
region_ok segs E mem (YP09.mkRegion (Some n) lo 0 lo 0 []).
Proof.
intros E mem n sp lo Hn Hlo Hhi Hw. unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite Hn. split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply Hw. lia.
Qed.
Lemma env_agree_havoc_ge : forall k0 k E0 E ws,
(k0 <= k)%nat -> env_agree k0 E0 E -> env_agree k0 E0 (havoc E k ws).
Proof.
intros k0 k E0 E ws Hk [HA HD]. split.
- intros n Hn. rewrite ew_havoc_old by lia. apply HA. exact Hn.
- rewrite ed_havoc. exact HD.
Qed.
Lemma env_agree_le : forall k k' E E', (k' <= k)%nat -> env_agree k E E' -> env_agree k' E E'.
Proof. intros k k' E E' Hk [HA HD]. split; [intros n Hn; apply HA; lia | exact HD]. Qed.
Definition CALLEE_SAVED : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma regs_preserved_of_st_ok : forall E ss ms regs0 extra,
st_ok segs E ss ms -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
regs_preserved regs0 (ms_regs ms).
Proof.
intros E ss ms regs0 extra HS [HA _] Hcs r Hr.
assert (Hin : In (Z_to_bv 5 r : reg) CALLEE_SAVED).
{ unfold callee_saved in Hr. cbv [CALLEE_SAVED In].
assert (H : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct H as [->|H]; [repeat (first [left; apply bv_eq; reflexivity | right])|]).
subst. repeat (first [left; apply bv_eq; reflexivity | right]). }
pose proof (proj1 (forallb_forall _ _) Hcs _ Hin) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
rewrite (st_ok_reg segs E ss ms _ HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite HA. 2:{ pose proof (u5_range (Z_to_bv 5 r : reg)). lia. }
rewrite ew_Ereg_reg, Z_to_bv_bv_unsigned. reflexivity.
Qed.
End h.
Definition inFP (FP : list (Z * Z)) (a : Z) : Prop := exists r, In r FP /\ fst r <= a < snd r.
Lemma inFP_nil : forall a, ~ inFP [] a.
Proof. intros a (r & Hin & _). destruct Hin. Qed.
Lemma inFP_cons : forall lo hi FP a, inFP ((lo, hi) :: FP) a <-> (lo <= a < hi \/ inFP FP a).
Proof.
intros lo hi FP a. split.
- intros (r & [<-|Hin] & Hr); [left; exact Hr | right; exists r; auto].
- intros [H|(r & Hin & Hr)]; [exists (lo, hi); cbn; auto | exists r; cbn; auto].
Qed.
Lemma inFP_app : forall F1 F2 a, inFP (F1 ++ F2) a <-> (inFP F1 a \/ inFP F2 a).
Proof.
intros F1 F2 a. split.
- intros (r & Hin & Hr). apply in_app_iff in Hin as [Hin|Hin]; [left|right]; exists r; auto.
- intros [(r & Hin & Hr)|(r & Hin & Hr)]; exists r; split; auto; apply in_app_iff; auto.
Qed.
Lemma inFP_mono : forall F1 F2 a, incl F1 F2 -> inFP F1 a -> inFP F2 a.
Proof. intros F1 F2 a Hi (r & Hin & Hr). exists r. auto. Qed.
Definition rm1 {X : Type} (x : X) (l l' : list X) : Prop :=
exists b1 b2, l = b1 ++ x :: b2 /\ l' = b1 ++ b2.
Lemma rm1_In_back : forall {X} (x : X) l l' y, rm1 x l l' -> In y l' -> In y l.
Proof.
intros X x l l' y (b1 & b2 & -> & ->) H. apply in_app_iff in H as [H|H]; apply in_app_iff; [left|right; right]; auto.
Qed.
Lemma rm1_In_fwd : forall {X} (x : X) l l' y, rm1 x l l' -> In y l -> y = x \/ In y l'.
Proof.
intros X x l l' y (b1 & b2 & -> & ->) H. apply in_app_iff in H as [H|[<-|H]].
- right. apply in_app_iff. auto.
- left. reflexivity.
- right. apply in_app_iff. auto.
Qed.
Lemma rm1_In_x : forall {X} (x : X) l l', rm1 x l l' -> In x l.
Proof. intros X x l l' (b1 & b2 & -> & ->). apply in_app_iff. right. left. reflexivity. Qed.
Lemma rm1_perm : forall {X} (x : X) l l', rm1 x l l' -> Permutation l (x :: l').
Proof. intros X x l l' (b1 & b2 & -> & ->). apply Permutation_sym. apply Permutation_middle. Qed.
Lemma perm_rm1 : forall {X} (x : X) l l', Permutation l (x :: l') -> exists l'', rm1 x l l'' /\ Permutation l'' l'.
Proof.
intros X x l l' HP. destruct (Permutation_vs_cons_inv HP) as (b1 & b2 & ->).
exists (b1 ++ b2). split; [exists b1, b2; auto|].
apply (Permutation_app_inv b1 b2 [] l' x). exact HP.
Qed.
Lemma perm_after_rm1 : forall {X} (x : X) l l' rest,
Permutation l (x :: rest) -> rm1 x l l' -> Permutation l' rest.
Proof.
intros X x l l' rest HP (b1 & b2 & -> & ->).
apply (Permutation_app_inv b1 b2 [] rest x). exact HP.
Qed.
Record img_laws (B : malloc_syms) (MR : MR_t) : Prop := {
il_low : forall a, in_img B a -> a < alloc_ceiling;
il_blocks : forall L A mem md p n i,
MR L A mem md -> In (p, n) (user_blocks A) -> 0 <= i < n -> ~ in_img B (ptr_addr L p + i);
il_ctx : forall L A mem md a,
MR L A mem md -> in_img B a -> alloc_owned L A a -> ms_ctx B <= a < ms_ctx B + CTX_SIZE;
il_rodata : forall L A mem md a,
MR L A mem md -> ms_debruijn B - 108 <= a < ms_debruijn B ->
mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a)
}.
End g.
Arguments il_low {rc B MR}. Arguments il_blocks {rc B MR}. Arguments il_ctx {rc B MR}. Arguments il_rodata {rc B MR}.
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d0.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis errno_low : errno_addr B + 4 <= alloc_ceiling.
Hypothesis IMG : img_laws B MR.
Local Notation segs := (ms_segs B).
Definition heap_ok (L : layout) (A : astate) (mem : word -> option byte) (md : Model) : Prop :=
MR L A mem md /\ WF A /\ bounded A.
Lemma init_done_of_block : forall A b, WF A -> In b (user_blocks A) -> st_init_done A = true.
Proof.
intros A b HW Hin. destruct (st_init_done A) eqn:E; [reflexivity|]. exfalso.
destruct HW as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinit) & _).
destruct (Hinit E) as (Hm & _). unfold user_blocks, used_metas in Hin. rewrite Hm in Hin. cbn in Hin. exact Hin.
Qed.
Definition errno_ok (mem : word -> option byte) : Prop :=
forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at segs mem a.
Definition stack_ok (STK sp : Z) (mem : word -> option byte) : Prop :=
sp mod 16 = 0 /\ 0 <= STK /\ alloc_ceiling + STK <= sp /\ sp < 2 ^ 63 /\
(forall a, sp - STK <= a < sp -> writable_at segs mem a).
Definition fn_pre (STK : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
heap_ok L A mem md /\ YK0s.ret_ok (getr regs 1) /\ stack_ok STK (spZ regs) mem /\
getr regs 4 = Z_to_bv 64 (ms_tp B) /\ errno_ok mem.
Definition img_kept (mem mem' : word -> option byte) : Prop :=
forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
~ (errno_addr B <= a < errno_addr B + 4) ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a).
Lemma img_kept_refl : forall m, img_kept m m.
Proof. intros m a _ _ _ _. split; [reflexivity | tauto]. Qed.
Lemma img_kept_trans : forall m1 m2 m3, img_kept m1 m2 -> img_kept m2 m3 -> img_kept m1 m3.
Proof.
intros m1 m2 m3 H1 H2 a Ha Hs Hc He. destruct (H1 a Ha Hs Hc He) as [E1 E2]. destruct (H2 a Ha Hs Hc He) as [F1 F2].
split; [rewrite F1; exact E1 | rewrite E2; exact F2].
Qed.
Lemma img_not_owned : forall L A mem md a,
MR L A mem md -> in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) -> ~ owned B L A a.
Proof.
intros L A mem md a HM Ha Hs Hc [Ho|Ho]; [|exact (Hs Ho)]. exact (Hc (il_ctx IMG L A mem md a HM Ha Ho)).
Qed.
Definition journal (STK sp0 : Z) (FP : list (Z * Z))
(L : layout) (A : astate) (mem : word -> option byte) (md : Model)
(L' : layout) (A' : astate) (mem' : word -> option byte) (md' : Model) : Prop :=
heap_ok L' A' mem' md' /\
(exists vm', md' = with_vmmaps vm' md) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall a n i, In (a, n) (blocks L A) -> In (a, n) (blocks L' A') -> 0 <= i < n ->
~ inFP FP (a + i) -> mbyte segs mem' (a + i) = mbyte segs mem (a + i)) /\
(forall a n i, In (a, n) (blocks L A) -> ~ In (a, n) (blocks L' A') -> 0 <= i < n -> inFP FP (a + i)) /\
stack_ok STK sp0 mem' /\ errno_ok mem' /\
img_kept mem mem'.
Lemma blocks_In : forall L A a n, In (a, n) (blocks L A) <-> exists p, ptr_addr L p = a /\ In (p, n) (user_blocks A).
Proof.
intros L A a n. unfold blocks. rewrite in_map_iff. split.
- intros ([p m] & H & Hin). cbn in H. injection H as <- <-. exists p. auto.
- intros (p & <- & Hin). exists (p, n). auto.
Qed.
Lemma heap_blocks : forall L A mem md a n i,
heap_ok L A mem md -> In (a, n) (blocks L A) -> 0 <= i < n ->
present mem (a + i) /\ 4096 <= a /\ a + n <= alloc_ceiling /\ ~ owned B L A (a + i).
Proof.
intros L A mem md a n i (HM & _) Hin Hi. apply blocks_In in Hin as (p & <- & Hin).
exact (mr_blocks B MR LAWS L A mem md p n i HM Hin Hi).
Qed.
Lemma heap_blocks_range : forall L A mem md a n,
heap_ok L A mem md -> In (a, n) (blocks L A) -> 0 < n -> 4096 <= a /\ a + n <= alloc_ceiling /\ a mod 16 = 0.
Proof.
intros L A mem md a n (HM & HW & _) Hin Hn. apply blocks_In in Hin as (p & <- & Hin).
pose proof (mr_blocks_aligned B MR LAWS L A mem md p n HM Hin) as Hal.
destruct (mr_blocks B MR LAWS L A mem md p n 0 HM Hin ltac:(lia)) as (_ & H1 & H2 & _). auto.
Qed.
Lemma heap_owned_low : forall L A mem md a, heap_ok L A mem md -> owned B L A a -> 0 <= a < alloc_ceiling.
Proof. intros L A mem md a (HM & _) Ho. exact (mr_owned_low B MR LAWS L A mem md a HM Ho). Qed.
Lemma heap_model : forall L A mem md, heap_ok L A mem md ->
m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [].
Proof. intros L A mem md (HM & _). exact (mr_model B MR LAWS L A mem md HM). Qed.
Lemma present_writable : forall mem a, present mem a -> writable_at segs mem a.
Proof.
intros mem a [b Hb]. unfold writable_at, wview. rewrite Hb. discriminate.
Qed.
Lemma with_vmmaps_self : forall md, md = with_vmmaps (m_vmmaps md) md.
Proof. intros md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.
Lemma with_vmmaps_twice : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. intros v1 v2 md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.
Lemma journal_init : forall STK FP L A regs mem md,
fn_pre STK L A regs mem md -> journal STK (spZ regs) FP L A mem md L A mem md.
Proof.
intros STK FP L A regs mem md (HH & Hra & Hst & Htp & Herr).
split; [exact HH|]. split; [exists (m_vmmaps md); apply with_vmmaps_self|].
split; [intros a Ha Hna; split; [reflexivity | tauto]|].
split; [intros; reflexivity|]. split; [intros a n i H1 H2; exfalso; exact (H2 H1)|].
split; [exact Hst|]. split; [exact Herr | apply img_kept_refl].
Qed.
Lemma mbyte_eq_of : forall (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte segs m' a = mbyte segs m a.
Proof. intros m m' a H. unfold mbyte. rewrite H. reflexivity. Qed.
Lemma writable_iff_of : forall (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> (writable_at segs m a <-> writable_at segs m' a).
Proof. intros m m' a H. unfold writable_at, wview. rewrite H. tauto. Qed.
Lemma pairwise_in2 : forall {X} (R : X -> X -> Prop) l x y,
pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
intros X R l. induction l as [|z l IH]; intros x y HP Hx Hy Hne; cbn in *; [destruct Hx|].
destruct HP as [Hz HP]. destruct Hx as [<-|Hx], Hy as [<-|Hy].
- congruence.
- left. apply Hz. exact Hy.
- right. apply Hz. exact Hx.
- apply IH; assumption.
Qed.
Lemma heap_sep_in2 : forall L A mem md x y,
heap_ok L A mem md -> In x (blocks L A) -> In y (blocks L A) -> x <> y ->
fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
intros L A mem md x y (HM & _) Hx Hy Hne.
destruct (pairwise_in2 _ _ x y (mr_blocks_disjoint B MR LAWS L A mem md HM) Hx Hy Hne) as [H|H];
unfold ranges_disjoint in H; lia.
Qed.
Definition wr_byte (STK sp0 : Z) (FP : list (Z * Z)) (bl0 blc : list (Z * Z)) (a : Z) : Prop :=
(sp0 - STK <= a < sp0) \/
(inFP FP a /\ exists b n, In (b, n) blc /\ b <= a < b + n) \/
(exists b n, In (b, n) blc /\ ~ In (b, n) bl0 /\ b <= a < b + n).
Lemma wr_byte_low : forall STK sp0 FP (L : layout) (A : astate) Lc Ac memc mdc a,
heap_ok Lc Ac memc mdc -> wr_byte STK sp0 FP (blocks L A) (blocks Lc Ac) a ->
(sp0 - STK <= a < sp0) \/ (a < alloc_ceiling /\ ~ owned B Lc Ac a /\
exists b n, In (b, n) (blocks Lc Ac) /\ b <= a < b + n /\
(inFP FP a \/ ~ In (b, n) (blocks L A))).
Proof.
intros STK sp0 FP L A Lc Ac memc mdc a HH [Hs | [(Hfp & b & n & Hin & Hr) | (b & n & Hin & Hn0 & Hr)]].
- left. exact Hs.
- right. destruct (heap_blocks Lc Ac memc mdc b n (a - b) HH Hin ltac:(lia)) as (_ & _ & Hc & Hno).
replace (b + (a - b)) with a in Hno by lia. split; [lia|]. split; [exact Hno|]. exists b, n. auto.
- right. destruct (heap_blocks Lc Ac memc mdc b n (a - b) HH Hin ltac:(lia)) as (_ & _ & Hc & Hno).
replace (b + (a - b)) with a in Hno by lia. split; [lia|]. split; [exact Hno|]. exists b, n. auto.
Qed.
Lemma journal_exec : forall STK sp0 FP L A mem md Lc Ac memc mdc memc' (W : Z -> Prop),
journal STK sp0 FP L A mem md Lc Ac memc mdc ->
(forall x : word, ~ W (bv_unsigned x) -> memc' x = memc x) ->
mem_grows memc memc' ->
(forall a, W a -> wr_byte STK sp0 FP (blocks L A) (blocks Lc Ac) a) ->
journal STK sp0 FP L A mem md Lc Ac memc' mdc.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc memc' W
(HH & Hvm & Hhigh & Hblk & Hgone & Hst & Herr & Himg) Hfr Hgr HW0.
clear errno_low.
pose proof alloc_ceiling_val as Hac.
destruct Hst as (Hal & Hstk0 & Hceil & H63 & Hstw).
assert (HW : forall a, W a -> _) by (intros a Ha; exact (wr_byte_low STK sp0 FP L A Lc Ac memc mdc a HH (HW0 a Ha))).
clear HW0.
assert (HWlow : forall a, W a -> a < sp0 /\ ~ owned B Lc Ac a).
{ intros a Ha. destruct (HW a Ha) as [Hs | (Hc & Hno & _)].
- split; [lia|]. intros Ho. pose proof (heap_owned_low _ _ _ _ a HH Ho). lia.
- split; [lia | exact Hno]. }
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ W a -> memc' (Z_to_bv 64 a) = memc (Z_to_bv 64 a)).
{ intros a Ha HWa. apply Hfr. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact HWa. }
split.
{ destruct HH as (HM & HW' & HB). split; [|split; assumption].
destruct (mr_model B MR LAWS _ _ _ _ HM) as (Hh & Hl & Hmat).
eapply (mr_frame B MR LAWS); [exact HM | | | | reflexivity | exact Hh | exact Hl | exact Hmat].
- intros a Ho. apply mbyte_eq_of. pose proof (mr_owned_low B MR LAWS _ _ _ _ a HM Ho).
apply Heqw; [lia|]. intros HWa. exact (proj2 (HWlow a HWa) Ho).
- intros a Ho Hp. eapply present_grows; eauto.
- intros p n i Hin Hi. eapply present_grows; [exact Hgr|].
exact (proj1 (mr_blocks B MR LAWS _ _ _ _ p n i HM Hin Hi)). }
split; [exact Hvm|]. split.
{ intros a Ha Hna. assert (E1 : memc' (Z_to_bv 64 a) = memc (Z_to_bv 64 a)).
{ apply Heqw; [lia|]. intros HWa.
destruct (HW a HWa) as [Hs | (Hc & _)]; [exact (Hna Hs) | lia]. }
destruct (Hhigh a Ha Hna) as [H1 H2]. split.
- rewrite <- H1. apply mbyte_eq_of. exact E1.
- rewrite H2. apply writable_iff_of. exact E1. }
split.
{ intros a n i H1 H2 Hi Hnf. rewrite <- (Hblk a n i H1 H2 Hi Hnf). apply mbyte_eq_of.
destruct (heap_blocks Lc Ac memc mdc a n i HH H2 Hi) as (_ & Hlo & Hhi & _).
apply Heqw; [lia|]. intros HWa. destruct (HW _ HWa) as [Hs | (_ & _ & b & m & Hbin & Hr & [Hfp | Hnot])]; [lia | exact (Hnf Hfp) |].
assert (Hne : (b, m) <> (a, n)) by (intros E; rewrite E in Hnot; exact (Hnot H1)).
destruct (heap_sep_in2 Lc Ac memc mdc (b, m) (a, n) HH Hbin H2 Hne) as [Hd|Hd]; cbn [fst snd] in Hd; lia. }
split; [exact Hgone|]. split.
{ split; [exact Hal|]. split; [exact Hstk0|]. split; [exact Hceil|]. split; [exact H63|].
intros a Ha. eapply writable_at_grows; [exact Hgr|]. apply Hstw. exact Ha. }
split; [intros a Ha; eapply writable_at_grows; [exact Hgr|]; apply Herr; exact Ha|].
eapply img_kept_trans; [exact Himg|]. intros a Ha Hs Hc He.
assert (E1 : memc' (Z_to_bv 64 a) = memc (Z_to_bv 64 a)).
{ pose proof (il_low IMG a Ha) as Hlow.
assert (Ha0 : 0 <= a).
{ destruct Ha as [_ (sg & _ & Hr)]. pose proof (bv_unsigned_in_range _ (fst sg)). lia. }
apply Heqw; [lia|]. intros HWa. destruct (HW a HWa) as [Hsk | (_ & _ & b & m & Hbin & Hr & _)]; [lia|].
apply blocks_In in Hbin as (q & Hq & Hqin).
apply (il_blocks IMG Lc Ac memc mdc q m (a - b) (proj1 HH) Hqin ltac:(lia)). rewrite Hq.
replace (b + (a - b)) with a by lia. exact Ha. }
split; [apply mbyte_eq_of; exact E1 | apply writable_iff_of; exact E1].
Qed.
Lemma sptr_eq_dec : forall p q : sptr, {p = q} + {p <> q}.
Proof. intros [r o] [r' o']. destruct (Nat.eq_dec r r'); [|right; congruence].
destruct (Z.eq_dec o o'); [left; congruence | right; congruence]. Defined.
Lemma spn_eq_dec : forall x y : sptr * Z, {x = y} + {x <> y}.
Proof. intros [p n] [q m]. destruct (sptr_eq_dec p q); [|right; congruence].
destruct (Z.eq_dec n m); [left; congruence | right; congruence]. Defined.
Lemma zz_eq_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. intros [p n] [q m]. destruct (Z.eq_dec p q); [|right; congruence].
destruct (Z.eq_dec n m); [left; congruence | right; congruence]. Defined.
Lemma journal_call : forall STK sp0 FP L A mem md Lc Ac memc mdc regs_c (Efp : Z -> Prop) L2 A2 regs2 mem2 md2,
journal STK sp0 FP L A mem md Lc Ac memc mdc ->
call_post B MR Lc Ac regs_c memc mdc Efp L2 A2 regs2 mem2 md2 ->
sp0 - STK <= spZ regs_c - ALLOC_STACK -> spZ regs_c <= sp0 ->
(forall a, Efp a -> exists b n, In (b, n) (blocks Lc Ac) /\ b <= a < b + n /\ (inFP FP a \/ ~ In (b, n) (blocks L A))) ->
(forall p n i, In (p, n) (user_blocks Ac) -> ~ In (p, n) (user_blocks A2) -> 0 <= i < n ->
Efp (ptr_addr Lc p + i)) ->
journal STK sp0 FP L A mem md L2 A2 mem2 md2.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs_c Efp L2 A2 regs2 mem2 md2
HJ0 (HM2 & HW2 & HB2 & Hle & Hstab & Hregs & (vm2 & Hvm2) & Hfr & Hkeep & Hscr)
Hlo Hhi HE1 Hg.
pose proof HJ0 as (HH & Hvm & Hhigh & Hblk & Hgone & Hst & Herr & Himg).
assert (HE0 : forall a, Efp a -> a < alloc_ceiling /\
(inFP FP a \/ exists b n, In (b, n) (blocks Lc Ac) /\ ~ In (b, n) (blocks L A) /\ b <= a < b + n)).
{ intros a Ha. destruct (HE1 a Ha) as (b & n & Hbin & Hr & Hor).
destruct (heap_blocks Lc Ac memc mdc b n (a - b) HH Hbin ltac:(lia)) as (_ & _ & Hc & _).
split; [lia|]. destruct Hor as [Hf|Hn]; [left; exact Hf | right; exists b, n; auto]. }
pose proof alloc_ceiling_val as Hac. pose proof errno_low as Hel.
destruct Hst as (Hal & Hstk0 & Hceil & H63 & Hstw).
assert (HH2 : heap_ok L2 A2 mem2 md2) by (split; [exact HM2 | split; assumption]).
assert (HE : forall a a0 n0, Efp a -> In (a0, n0) (blocks L A) -> In (a0, n0) (blocks Lc Ac) -> a0 <= a < a0 + n0 ->
inFP FP a).
{ intros a a0 n0 Ha H0 Hc Hr. destruct (HE0 a Ha) as [_ [Hfp | (b & m & Hbin & Hbn & Hbr)]]; [exact Hfp|].
assert (Hne : (b, m) <> (a0, n0)) by (intros E; rewrite E in Hbn; exact (Hbn H0)).
destruct (heap_sep_in2 Lc Ac memc mdc (b, m) (a0, n0) HH Hbin Hc Hne) as [Hd|Hd]; cbn [fst snd] in Hd; lia. }
assert (ALLOC_STACK = 8192) as Has by reflexivity.
assert (Hfree : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs_c - ALLOC_STACK <= a < spZ regs_c) ->
mbyte segs mem2 a = mbyte segs memc a /\ (writable_at segs memc a <-> writable_at segs mem2 a)).
{ intros a Ha Hns. apply Hfr.
- left. exact Ha.
- intros Ho. pose proof (heap_owned_low _ _ _ _ a HH Ho). lia.
- intros Ho. pose proof (heap_owned_low _ _ _ _ a HH2 Ho). lia.
- unfold scratch. intros [Hs|Hs]; [exact (Hns Hs) | lia].
- intros He. destruct (HE0 a He). lia. }
split; [exact HH2|]. split.
{ exists vm2. rewrite Hvm2. destruct Hvm as [vm ->]. apply with_vmmaps_twice. }
split.
{ intros a Ha Hna. destruct (Hfree a ltac:(lia) ltac:(lia)) as [E1 E2]. destruct (Hhigh a Ha Hna) as [F1 F2].
split; [rewrite E1; exact F1 | rewrite F2; exact E2]. }
split.
{ intros a n i H1 H2 Hi Hnf.
destruct (in_dec zz_eq_dec (a, n) (blocks Lc Ac)) as [Hc|Hc].
- rewrite <- (Hblk a n i H1 Hc Hi Hnf).
pose proof Hc as Hc0. apply blocks_In in Hc as (p & Hp & Hpc).
destruct (in_dec spn_eq_dec (p, n) (user_blocks A2)) as [Hp2|Hp2].
+ rewrite <- Hp. apply (Hkeep p n i Hpc Hp2 Hi).
+ exfalso. apply Hnf. apply (HE (a + i) a n); [rewrite <- Hp; apply (Hg p n i Hpc Hp2 Hi) | exact H1 | exact Hc0 | lia].
- exfalso. exact (Hnf (Hgone a n i H1 Hc Hi)). }
split.
{ intros a n i H1 H2 Hi.
destruct (in_dec zz_eq_dec (a, n) (blocks Lc Ac)) as [Hc|Hc]; [|exact (Hgone a n i H1 Hc Hi)].
pose proof Hc as Hc0. apply blocks_In in Hc as (p & Hp & Hpc).
destruct (in_dec spn_eq_dec (p, n) (user_blocks A2)) as [Hp2|Hp2].
- exfalso. apply H2. apply blocks_In. exists p. split; [|exact Hp2]. rewrite (Hstab p n Hpc Hp2). exact Hp.
- apply (HE (a + i) a n); [rewrite <- Hp; apply (Hg p n i Hpc Hp2 Hi) | exact H1 | exact Hc0 | lia]. }
split.
{ split; [exact Hal|]. split; [exact Hstk0|]. split; [exact Hceil|]. split; [exact H63|].
intros a Ha. destruct (Z_lt_le_dec a (spZ regs_c - ALLOC_STACK)) as [Hb|Hb].
- apply (proj1 (proj2 (Hfree a ltac:(lia) ltac:(lia)))). apply Hstw. exact Ha.
- destruct (Z_lt_le_dec a (spZ regs_c)) as [Hb2|Hb2].
+ apply Hscr. unfold scratch. left. lia.
+ apply (proj1 (proj2 (Hfree a ltac:(lia) ltac:(lia)))). apply Hstw. exact Ha. }
split; [intros a Ha; apply Hscr; unfold scratch; right; exact Ha|].
eapply img_kept_trans; [exact Himg|]. intros a Ha Hs Hc He.
pose proof (il_low IMG a Ha) as Hlow.
apply Hfr.
- right. exact Ha.
- exact (img_not_owned Lc Ac memc mdc a (proj1 HH) Ha Hs Hc).
- exact (img_not_owned L2 A2 mem2 md2 a HM2 Ha Hs Hc).
- unfold scratch. intros [Hsk|Hsk]; [lia | exact (He Hsk)].
- intros Hea. destruct (HE1 a Hea) as (b & n & Hbin & Hr & _).
apply blocks_In in Hbin as (q & Hq & Hqin).
apply (il_blocks IMG Lc Ac memc mdc q n (a - b) (proj1 HH) Hqin ltac:(lia)). rewrite Hq.
replace (b + (a - b)) with a by lia. exact Ha.
Qed.
Lemma fn_pre_of_journal : forall STK sp0 FP L A mem md Lc Ac regs_c memc mdc STK1,
journal STK sp0 FP L A mem md Lc Ac memc mdc ->
YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 -> 0 <= STK1 ->
sp0 - STK <= spZ regs_c - STK1 -> spZ regs_c <= sp0 ->
getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
fn_pre STK1 Lc Ac regs_c memc mdc.
Proof.
intros STK sp0 FP L A mem md Lc Ac regs_c memc mdc STK1 (HH & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & H63 & Hstw) & Herr & _)
Hra Hal16 Hstk1 Hlo Hhi Htp.
split; [exact HH|]. split; [exact Hra|]. split; [| split; [exact Htp | exact Herr]].
split; [exact Hal16|]. split; [exact Hstk1|]. split; [lia|]. split; [lia|].
intros a Ha. apply Hstw. lia.
Qed.
Lemma journal_sub : forall STK sp0 FP L A mem md Lc Ac memc mdc STK1 sp1 FP1 L2 A2 mem2 md2,
journal STK sp0 FP L A mem md Lc Ac memc mdc ->
journal STK1 sp1 FP1 Lc Ac memc mdc L2 A2 mem2 md2 ->
sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
(forall a, inFP FP1 a -> inFP FP a /\ a < alloc_ceiling) ->
journal STK sp0 FP L A mem md L2 A2 mem2 md2.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc STK1 sp1 FP1 L2 A2 mem2 md2
(HH & Hvm & Hhigh & Hblk & Hgone & Hst & Herr & Himg)
(HH2 & Hvm2 & Hhigh2 & Hblk2 & Hgone2 & Hst2 & Herr2 & Himg2) Hlo Hhi HF.
pose proof alloc_ceiling_val as Hac.
destruct Hst as (Hal & Hstk0 & Hceil & H63 & Hstw). destruct Hst2 as (Hal2 & Hstk2 & Hceil2 & H632 & Hstw2).
split; [exact HH2|]. split.
{ destruct Hvm2 as [vm2 ->]. destruct Hvm as [vm ->]. exists vm2. apply with_vmmaps_twice. }
split.
{ intros a Ha Hna. destruct (Hhigh2 a Ha ltac:(lia)) as [E1 E2]. destruct (Hhigh a Ha Hna) as [F1 F2].
split; [rewrite E1; exact F1 | rewrite F2; exact E2]. }
split.
{ intros a n i H1 H2 Hi Hnf.
destruct (in_dec zz_eq_dec (a, n) (blocks Lc Ac)) as [Hc|Hc].
- rewrite <- (Hblk a n i H1 Hc Hi Hnf). apply (Hblk2 a n i Hc H2 Hi).
intros Hf. exact (Hnf (proj1 (HF _ Hf))).
- exfalso. exact (Hnf (Hgone a n i H1 Hc Hi)). }
split.
{ intros a n i H1 H2 Hi.
destruct (in_dec zz_eq_dec (a, n) (blocks Lc Ac)) as [Hc|Hc]; [|exact (Hgone a n i H1 Hc Hi)].
apply (proj1 (HF _ (Hgone2 a n i Hc H2 Hi))). }
split.
{ split; [exact Hal|]. split; [exact Hstk0|]. split; [exact Hceil|]. split; [exact H63|].
intros a Ha. destruct (Z_lt_le_dec a (sp1 - STK1)) as [Hb|Hb].
- apply (proj1 (proj2 (Hhigh2 a ltac:(lia) ltac:(lia)))). apply Hstw. exact Ha.
- destruct (Z_lt_le_dec a sp1) as [Hb2|Hb2].
+ apply Hstw2. lia.
+ apply (proj1 (proj2 (Hhigh2 a ltac:(lia) ltac:(lia)))). apply Hstw. exact Ha. }
split; [exact Herr2 | eapply img_kept_trans; [exact Himg | exact Himg2]].
Qed.
Lemma pairwise_app_mid : forall {X} (R : X -> X -> Prop) b1 x b2 y,
pairwise R (b1 ++ x :: b2) -> In y (b1 ++ b2) -> R x y \/ R y x.
Proof.
intros X R b1. induction b1 as [|z b1 IH]; intros x b2 y HP Hin; cbn in *.
- left. apply (proj1 HP). exact Hin.
- destruct Hin as [<-|Hin].
+ right. apply (proj1 HP). apply in_app_iff. right. left. reflexivity.
+ apply (IH x b2 y (proj2 HP) Hin).
Qed.
Lemma heap_sep : forall L A mem md b1 x b2 y,
heap_ok L A mem md -> blocks L A = b1 ++ x :: b2 -> In y (b1 ++ b2) ->
fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
intros L A mem md b1 x b2 y (HM & _) HB Hin.
pose proof (mr_blocks_disjoint B MR LAWS L A mem md HM) as HP. rewrite HB in HP.
destruct (pairwise_app_mid _ b1 x b2 y HP Hin) as [H|H]; unfold ranges_disjoint in H; lia.
Qed.
Lemma heap_sep_perm : forall L A mem md x rest y,
heap_ok L A mem md -> Permutation (blocks L A) (x :: rest) -> In y rest ->
fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
intros L A mem md x rest y HH HP Hin.
destruct (Permutation_vs_cons_inv HP) as (b1 & b2 & HB).
eapply (heap_sep L A mem md b1 x b2 y HH HB).
apply (Permutation_in y (l:=rest)); [|exact Hin]. apply Permutation_sym.
apply (Permutation_app_inv b1 b2 [] rest x). rewrite <- HB. exact HP.
Qed.
Lemma blocks_perm_in : forall L A (x : Z * Z) rest y,
Permutation (blocks L A) (x :: rest) -> (y = x \/ In y rest) -> In y (blocks L A).
Proof.
intros L A x rest y HP Hy. apply (Permutation_in y (Permutation_sym HP)). destruct Hy as [->|Hy]; [left; reflexivity | right; exact Hy].
Qed.
Lemma regs_preserved_trans : forall r1 r2 r3,
regs_preserved r1 r2 -> regs_preserved r2 r3 -> regs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). apply H1. exact Hr. Qed.
Lemma map_addr_stable : forall (L L' : layout) (l l' : list (sptr * Z)),
incl l l' ->
(forall q m, In (q, m) l' -> ptr_addr L' q = ptr_addr L q) ->
map (fun b : sptr * Z => (ptr_addr L' (fst b), snd b)) l = map (fun b : sptr * Z => (ptr_addr L (fst b), snd b)) l.
Proof.
intros L L' l l' Hi Hs. induction l as [|[q m] l IH]; [reflexivity|]. cbn [map fst snd].
rewrite (Hs q m) by (apply Hi; left; reflexivity). rewrite IH; [reflexivity|]. intros x Hx. apply Hi. right. exact Hx.
Qed.
Theorem cg_free : free_realizes B MR ->
forall STK sp0 FP L A mem md Lc Ac regs_c memc mdc p n,
journal STK sp0 FP L A mem md Lc Ac memc mdc ->
In (p, n) (user_blocks Ac) -> getr regs_c 10 = Z_to_bv 64 (ptr_addr Lc p) ->
YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 ->
sp0 - STK <= spZ regs_c - ALLOC_STACK -> spZ regs_c <= sp0 ->
getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
(In (ptr_addr Lc p, n) (blocks L A) -> forall i, 0 <= i < n -> inFP FP (ptr_addr Lc p + i)) ->
SR segs (mkCfg (mkst regs_c (Z_to_bv 64 (ms_free B)) memc (seg_rom segs)) mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 (getr regs_c 1) mem2 (seg_rom segs)) md2 /\
journal STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved regs_c regs2 /\
rm1 (ptr_addr Lc p, n) (blocks Lc Ac) (blocks L2 A2) /\
(forall a m i, In (a, m) (blocks L2 A2) -> 0 <= i < m ->
mbyte segs mem2 (a + i) = mbyte segs memc (a + i)) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs_c - ALLOC_STACK <= a < spZ regs_c) ->
mbyte segs mem2 a = mbyte segs memc a /\ (writable_at segs memc a <-> writable_at segs mem2 a)) /\
st_init_done A2 = true).
Proof.
intros HFR STK sp0 FP L A mem md Lc Ac regs_c memc mdc p n HJ Hin Ha0 Hra Hal16 Hlo Hhi Htp HFP.
pose proof HJ as (HH & Hvm & Hhigh & Hblk & Hgone & Hst & Herr & Himg).
pose proof alloc_ceiling_val as Hac. pose proof errno_low as Hel.
assert (ALLOC_STACK = 8192) as Has by reflexivity.
destruct Hst as (Hal & Hstk0 & Hceil & H63 & Hstw).
destruct HH as (HM & HW & HB).
assert (Hpre : call_pre B MR Lc Ac regs_c memc mdc).
{ split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact Hra|].
split; [exact Hal16|]. split; [lia|]. split; [lia|]. split.
{ intros a Ha. apply Hstw. lia. }
split; [exact Htp|]. split; [exact Herr|].
intros Hf. rewrite (init_done_of_block Ac (p, n) HW Hin) in Hf. discriminate. }
eapply SR_mono; [eapply (free_SR B MR HFR); [exact Hpre | exact Hin | exact Ha0]|].
intros c' ([[] A2] & tr & Hcp & (L2 & regs2 & mem2 & md2 & -> & Hpost & (l1 & l2 & E1 & E2))). cbn [snd] in *.
pose proof (free_keeps_init_done (Some p) Ac tr tt A2 (init_done_of_block Ac (p, n) HW Hin) (cpath_yields _ _ _ Hcp)) as Hid2.
pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hregs & Hvm2 & Hfr & Hkeep & Hscr).
assert (HH2 : heap_ok L2 A2 mem2 md2) by (split; [exact HM2 | split; assumption]).
assert (Hsub : forall q m, In (q, m) (user_blocks A2) -> In (q, m) (user_blocks Ac)).
{ intros q m Hq. rewrite E2 in Hq. rewrite E1. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff; [left|right; right]; exact Hq. }
pose proof (mr_blocks B MR LAWS Lc Ac memc mdc p n) as Hpb.
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split.
{ eapply journal_call; [exact HJ | exact Hpost | exact Hlo | exact Hhi | |].
- intros a Ha. cbn beta in Ha. exists (ptr_addr Lc p), n.
split; [apply blocks_In; exists p; auto|]. split; [lia|].
destruct (in_dec zz_eq_dec (ptr_addr Lc p, n) (blocks L A)) as [H0|H0]; [|right; exact H0].
left. replace a with (ptr_addr Lc p + (a - ptr_addr Lc p)) by lia. apply (HFP H0). lia.
- intros q m i Hq Hnq Hi. cbn beta. rewrite E1 in Hq. rewrite E2 in Hnq.
apply in_app_iff in Hq as [Hq|[Hq|Hq]].
+ exfalso. apply Hnq. apply in_app_iff. left. exact Hq.
+ injection Hq as -> ->. lia.
+ exfalso. apply Hnq. apply in_app_iff. right. exact Hq. }
split; [exact Hregs|]. split.
{ exists (map (fun b : sptr * Z => (ptr_addr Lc (fst b), snd b)) l1), (map (fun b : sptr * Z => (ptr_addr Lc (fst b), snd b)) l2).
unfold blocks. rewrite E1, E2, !map_app. cbn [map fst snd]. split; [reflexivity|].
rewrite (map_addr_stable Lc L2 l1 (user_blocks A2)); [| rewrite E2; intros x Hx; apply in_app_iff; left; exact Hx | intros q m Hq; apply (Hstab q m); [apply Hsub; exact Hq | exact Hq]].
rewrite (map_addr_stable Lc L2 l2 (user_blocks A2)); [| rewrite E2; intros x Hx; apply in_app_iff; right; exact Hx | intros q m Hq; apply (Hstab q m); [apply Hsub; exact Hq | exact Hq]].
reflexivity. }
split.
{ intros a m i Ham Hi. apply blocks_In in Ham as (q & Hq & Hqin).
rewrite (Hstab q m (Hsub q m Hqin) Hqin) in Hq. rewrite <- Hq. apply (Hkeep q m i); [apply Hsub; exact Hqin | exact Hqin | exact Hi]. }
split; [|exact Hid2].
intros a Ha Hns. apply Hfr.
- left. lia.
- intros Ho. pose proof (mr_owned_low B MR LAWS _ _ _ _ a HM Ho). lia.
- intros Ho. pose proof (mr_owned_low B MR LAWS _ _ _ _ a HM2 Ho). lia.
- unfold scratch. intros [Hs|Hs]; [exact (Hns Hs) | lia].
- cbn beta. intros He. destruct (Hpb 0 HM Hin ltac:(lia)) as (_ & _ & Hc & _). lia.
Qed.
Theorem cg_malloc : malloc_realizes B MR ->
forall STK sp0 FP L A mem md Lc Ac regs_c memc mdc n,
journal STK sp0 FP L A mem md Lc Ac memc mdc ->
st_init_done Ac = true ->
getr regs_c 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 ->
sp0 - STK <= spZ regs_c - ALLOC_STACK -> spZ regs_c <= sp0 ->
getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
SR segs (mkCfg (mkst regs_c (Z_to_bv 64 (ms_malloc B)) memc (seg_rom segs)) mdc)
(fun c' => exists L2 A2 regs2 mem2 md2 (res : Z),
c' = mkCfg (mkst regs2 (getr regs_c 1) mem2 (seg_rom segs)) md2 /\
journal STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved regs_c regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
((res = 0 /\ blocks L2 A2 = blocks Lc Ac)
\/ (res <> 0 /\ res mod 16 = 0 /\
(exists b1 b2, blocks L2 A2 = b1 ++ (res, n) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
(forall blc i, In (res, n) blc -> 0 <= i < n -> wr_byte STK sp0 FP (blocks L A) blc (res + i)))) /\
(forall a m i, In (a, m) (blocks Lc Ac) -> 0 <= i < m ->
mbyte segs mem2 (a + i) = mbyte segs memc (a + i)) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs_c - ALLOC_STACK <= a < spZ regs_c) ->
mbyte segs mem2 a = mbyte segs memc a /\ (writable_at segs memc a <-> writable_at segs mem2 a))).
Proof.
intros HMA STK sp0 FP L A mem md Lc Ac regs_c memc mdc n HJ Hid Ha0 Hn Hra Hal16 Hlo Hhi Htp.
pose proof HJ as (HH & Hvm & Hhigh & Hblk & Hgone & Hst & Herr & Himg).
pose proof alloc_ceiling_val as Hac. pose proof errno_low as Hel.
assert (ALLOC_STACK = 8192) as Has by reflexivity.
destruct Hst as (Hal & Hstk0 & Hceil & H63 & Hstw).
destruct HH as (HM & HW & HB).
assert (Hpre : call_pre B MR Lc Ac regs_c memc mdc).
{ split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact Hra|].
split; [exact Hal16|]. split; [lia|]. split; [lia|]. split.
{ intros a Ha. apply Hstw. lia. }
split; [exact Htp|]. split; [exact Herr|].
intros Hf. rewrite Hid in Hf. discriminate. }
eapply SR_mono; [eapply (malloc_SR B MR HMA); [exact Hpre | exact Ha0 | exact Hn]|].
intros c' ([p A2] & tr & Hcp & (L2 & regs2 & mem2 & md2 & -> & Hpost & Hres)). cbn [fst snd] in *.
pose proof (malloc_keeps_init_done n Ac tr p A2 Hid (cpath_yields _ _ _ Hcp)) as Hid2.
pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hregs & Hvm2 & Hfr & Hkeep & Hscr).
assert (HH2 : heap_ok L2 A2 mem2 md2) by (split; [exact HM2 | split; assumption]).
assert (Hsub : forall q m, In (q, m) (user_blocks Ac) -> In (q, m) (user_blocks A2)).
{ intros q m Hq. destruct p as [p0|].
- destruct Hres as (_ & _ & (l1 & l2 & E1 & E2) & _). rewrite E1. rewrite E2 in Hq.
apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff; [left; exact Hq | right; right; exact Hq].
- destruct Hres as [_ E]. rewrite E. exact Hq. }
assert (HJ2 : journal STK sp0 FP L A mem md L2 A2 mem2 md2).
{ eapply journal_call; [exact HJ | exact Hpost | exact Hlo | exact Hhi | intros a Ha; destruct Ha |].
intros q m i Hq Hnq Hi. exact (Hnq (Hsub q m Hq)). }
assert (Hkeepc : forall a m i, In (a, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte segs mem2 (a + i) = mbyte segs memc (a + i)).
{ intros a m i Ham Hi. apply blocks_In in Ham as (q & Hq & Hqin). rewrite <- Hq.
apply (Hkeep q m i Hqin (Hsub q m Hqin) Hi). }
assert (Hhighc : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs_c - ALLOC_STACK <= a < spZ regs_c) ->
mbyte segs mem2 a = mbyte segs memc a /\ (writable_at segs memc a <-> writable_at segs mem2 a)).
{ intros a Ha Hns. apply Hfr.
- left. lia.
- intros Ho. pose proof (mr_owned_low B MR LAWS _ _ _ _ a HM Ho). lia.
- intros Ho. pose proof (mr_owned_low B MR LAWS _ _ _ _ a HM2 Ho). lia.
- unfold scratch. intros [Hs|Hs]; [exact (Hns Hs) | lia].
- intros F; exact F. }
assert (Hmapc : map (fun b : sptr * Z => (ptr_addr L2 (fst b), snd b)) (user_blocks Ac) = blocks Lc Ac).
{ unfold blocks. apply (map_addr_stable Lc L2 (user_blocks Ac) (user_blocks Ac)); [intros x Hx; exact Hx|].
intros q m Hq. exact (Hstab q m Hq (Hsub q m Hq)). }
exists L2, A2, regs2, mem2, md2.
destruct p as [p0|].
- destruct Hres as (Hr10 & Hnz & (l1 & l2 & E1 & E2) & _).
exists (ptr_addr L2 p0). split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact Hregs|].
split; [exact Hr10|]. split; [| split; [exact Hkeepc | exact Hhighc]].
right. split; [exact Hnz|].
assert (Hin2 : In (p0, n) (user_blocks A2)) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
split; [exact (mr_blocks_aligned B MR LAWS L2 A2 mem2 md2 p0 n HM2 Hin2)|].
assert (HB2eq : blocks L2 A2 = map (fun b : sptr * Z => (ptr_addr L2 (fst b), snd b)) l1 ++ (ptr_addr L2 p0, n) ::
map (fun b : sptr * Z => (ptr_addr L2 (fst b), snd b)) l2).
{ unfold blocks. rewrite E1, map_app. reflexivity. }
assert (HBceq : blocks Lc Ac = map (fun b : sptr * Z => (ptr_addr L2 (fst b), snd b)) l1 ++
map (fun b : sptr * Z => (ptr_addr L2 (fst b), snd b)) l2).
{ rewrite <- Hmapc, E2, map_app. reflexivity. }
split; [eexists _, _; split; [exact HB2eq | exact HBceq]|].
intros blc i Hinb Hi.
assert (Hin2' : In (ptr_addr L2 p0, n) (blocks L2 A2)) by (apply blocks_In; exists p0; auto).
destruct (in_dec zz_eq_dec (ptr_addr L2 p0, n) (blocks L A)) as [H0|H0].
+ right. left. split; [| exists (ptr_addr L2 p0), n; split; [exact Hinb | lia]].
apply (Hgone _ _ i H0); [|exact Hi].
intros Hc. rewrite HBceq in Hc.
pose proof (mr_blocks_disjoint B MR LAWS L2 A2 mem2 md2 HM2) as HP. rewrite HB2eq in HP.
destruct (pairwise_app_mid _ _ _ _ _ HP Hc) as [Hd|Hd]; unfold ranges_disjoint in Hd; cbn [fst snd] in Hd; lia.
+ right. right. exists (ptr_addr L2 p0), n. split; [exact Hinb|]. split; [exact H0 | lia].
- destruct Hres as [Hr10 E].
exists 0. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact Hregs|].
split; [exact Hr10|]. split; [| split; [exact Hkeepc | exact Hhighc]].
left. split; [reflexivity|]. rewrite <- Hmapc. unfold blocks. rewrite E. reflexivity.
Qed.
Theorem cg_free_null : free_null_realizes B ->
forall regs mem md,
YK0s.ret_ok (getr regs 1) -> getr regs 10 = Z_to_bv 64 0 -> m_halted md = None -> m_vm_lazy md = [] ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
(fun c' => c' = mkCfg (mkst regs (getr regs 1) mem (seg_rom segs)) md).
Proof. intros HFN. exact HFN. Qed.
End d0.
Section e0.
Variable segs : list Segment.
Definition CLOB : list reg := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Lemma not_clob_cases : forall r : reg, reg_in r CLOB = false -> r = 0%bv \/ callee_saved (bv_unsigned r).
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin. unfold callee_saved.
repeat (destruct Hin as [<-|Hin];
[first [ left; reflexivity
| vm_compute in Hr; discriminate
| right;
match goal with |- context [bv_unsigned ?x] =>
let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
lia ] |]).
destruct Hin.
Qed.
Lemma regs_preserved_frame : forall regs regs',
regs_preserved regs regs' -> forall r, reg_in r CLOB = false -> getr regs' r = getr regs r.
Proof.
intros regs regs' HP r Hr. destruct (not_clob_cases r Hr) as [-> | Hcs].
- rewrite !getr_zero. reflexivity.
- specialize (HP (bv_unsigned r) Hcs). rewrite Z_to_bv_bv_unsigned in HP. exact HP.
Qed.
Definition region_kept (E : env) (mem mem' : word -> option byte) (r : YP09.region) : Prop :=
(forall a, base_val E (r_base r) + r_lo r <= a < base_val E (r_base r) + r_hi r ->
mbyte segs mem' a = mbyte segs mem a) /\
(forall a, base_val E (r_base r) + r_wlo r <= a < base_val E (r_base r) + r_whi r ->
writable_at segs mem a -> writable_at segs mem' a).
Definition no_cdata (rs : smem) : bool :=
forallb (fun r => forallb (fun c => match c_val c with CData _ _ _ => false | _ => true end) (r_chunks r)) rs.
Lemma mem_ok_kept : forall E mem mem' rs,
mem_ok segs E mem rs -> no_cdata rs = true ->
Forall (region_kept E mem mem') rs -> mem_ok segs E mem' rs.
Proof.
intros E mem mem' rs (Hwf & Hok & Hpd) Hnc Hk. split; [exact Hwf|]. split; [|exact Hpd].
apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) Hok r Hr) as HR.
pose proof (proj1 (Forall_forall _ _) Hk r Hr) as [K1 K2].
pose proof (regions_wf_In rs r Hwf Hr) as Hrwf. apply region_wf_facts in Hrwf as (_ & _ & Hci).
unfold no_cdata in Hnc. pose proof (proj1 (forallb_forall _ _) Hnc r Hr) as Hncr. cbn beta in Hncr.
eapply region_ok_transport; [exact HR | reflexivity | | exact K1 | exact K2 | exact Hci].
intros c Hc. pose proof (proj1 (forallb_forall _ _) Hncr c Hc) as Hcc. cbn beta in Hcc.
destruct (c_val c); [reflexivity | exact I | exact I | discriminate].
Qed.
Definition trim_lo (r : YP09.region) (lo : Z) : YP09.region :=
YP09.mkRegion (r_base r) (Z.max lo (r_lo r)) (r_hi r) (Z.max lo (r_wlo r)) (r_whi r)
(List.filter (fun c => lo <=? c_off c) (r_chunks r)).
Lemma subregion_trim_lo : forall r lo, subregion (trim_lo r lo) r.
Proof.
intros r lo. unfold subregion, trim_lo. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; lia|].
intros c Hc. apply filter_In in Hc. tauto.
Qed.
Definition ss_after_stretch (ss : sstate) (rs : smem) (k : nat) (clob : list reg) (pc : Z) : sstate :=
mkSS pc (sr_sets (ss_regs ss) (junk_upd k clob)) rs None (ss_facts ss).
Theorem st_ok_after_stretch : forall k E ss ms regs' mem' rs pc (clob : list reg),
st_ok segs E ss ms ->
ss_resv ss = None ->
ss_atoms_lt k ss = true ->
regions_wf rs = true -> no_cdata rs = true -> mem_atoms_lt k rs = true ->
submem rs (ss_mem ss) ->
reg_nodup clob = true -> forallb (fun r : reg => negb (bv_eqb r 0)) clob = true ->
(forall r, reg_in r clob = false -> getr regs' r = getr (ms_regs ms) r) ->
Forall (region_kept E (ms_mem ms) mem') rs ->
st_ok segs (havoc E k (map (getr regs') clob)) (ss_after_stretch ss rs k clob pc)
(mkst regs' (Z_to_bv 64 pc) mem' (seg_rom segs)).
Proof.
intros k E ss ms regs' mem' rs pc clob HS Hrv Hat Hwf Hnc Hmat Hsub Hnd Hnz Hsame Hk.
pose proof (st_ok_mkst segs E ss ms HS Hrv) as Hshape. rewrite Hshape in HS.
pose proof (st_ok_splice_havoc segs k E ss (ms_regs ms) regs' (Z_to_bv 64 (ss_pc ss)) pc
(ms_mem ms) mem' rs [] clob HS Hat) as H.
cbn [map app] in H. apply H.
- exact Hnd.
- exact Hnz.
- reflexivity.
- exact Hmat.
- exact Hsame.
- constructor.
- apply (mem_ok_kept E (ms_mem ms) mem' rs); [| exact Hnc | exact Hk].
eapply mem_ok_sub; [exact Hsub | exact Hwf | exact (st_ok_mem_ok segs E ss _ HS)].
Qed.
Lemma region_kept_outside : forall E (mem mem' : word -> option byte) r d n,
(forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> mem' x = mem x) ->
mem_grows mem mem' ->
0 <= base_val E (r_base r) + r_lo r ->
(base_val E (r_base r) + r_hi r <= d \/ d + n <= base_val E (r_base r) + r_lo r) ->
base_val E (r_base r) + r_hi r <= 2 ^ 64 ->
r_lo r <= r_wlo r -> r_whi r <= r_hi r ->
region_kept E mem mem' r.
Proof.
intros E mem mem' r d n Hout Hgr Hlo Hdis Hhi Hw1 Hw2. split; intros a Ha.
- unfold mbyte. rewrite (Hout (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. lia.
- apply (writable_at_grows segs mem mem'); assumption.
Qed.
Definition ss_after_call (ss : sstate) (rs : smem) (k : nat) (retpc : Z) : sstate :=
mkSS retpc (sr_sets (ss_regs ss) (junk_upd k CLOB)) rs None (ss_facts ss).
Theorem st_ok_after_call : forall k E ss ms regs' mem' rs retpc,
st_ok segs E ss ms ->
ss_resv ss = None ->
ss_atoms_lt k ss = true ->
regions_wf rs = true -> no_cdata rs = true -> mem_atoms_lt k rs = true ->
submem rs (ss_mem ss) ->
sr_get (ss_regs ss) 1 = SLit retpc ->
regs_preserved (ms_regs ms) regs' ->
Forall (region_kept E (ms_mem ms) mem') rs ->
st_ok segs (havoc E k (map (getr regs') CLOB)) (ss_after_call ss rs k retpc)
(mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom segs)).
Proof.
intros k E ss ms regs' mem' rs retpc HS Hrv Hat Hwf Hnc Hmat Hsub Hra HP Hk.
pose proof (st_ok_mkst segs E ss ms HS Hrv) as Hshape.
rewrite Hshape in HS.
pose proof (st_ok_splice_havoc segs k E ss (ms_regs ms) regs' (Z_to_bv 64 (ss_pc ss)) retpc
(ms_mem ms) mem' rs [] CLOB HS Hat) as H.
cbn [map app] in H. apply H.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- reflexivity.
- exact Hmat.
- apply regs_preserved_frame. exact HP.
- constructor.
- apply (mem_ok_kept E (ms_mem ms) mem' rs); [| exact Hnc | exact Hk].
eapply mem_ok_sub; [exact Hsub | exact Hwf | exact (st_ok_mem_ok segs E ss _ HS)].
Qed.
Lemma region_kept_stack : forall E mem mem' n lo hi wlo whi cs sp xlo xhi,
bv_unsigned (ew E n) = sp ->
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (xlo <= x < xhi) ->
mbyte segs mem' x = mbyte segs mem x /\ (writable_at segs mem x <-> writable_at segs mem' x)) ->
alloc_ceiling <= sp + lo -> sp + hi <= 2 ^ 64 -> xhi <= sp + lo -> lo <= wlo -> whi <= hi ->
region_kept E mem mem' (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E mem mem' n lo hi wlo whi cs sp xlo xhi Hn Hfr Hlo Hhi Hx Hwlo Hwhi.
split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; rewrite Hn; intros a Ha.
- apply (proj1 (Hfr a ltac:(lia) ltac:(lia))).
- apply (proj1 (proj2 (Hfr a ltac:(lia) ltac:(lia)))).
Qed.
Lemma region_kept_block_ro : forall E mem mem' n lo hi wlo whi cs b m (bl : list (Z * Z)),
bv_unsigned (ew E n) = b -> In (b, m) bl ->
(forall b' m' i, In (b', m') bl -> 0 <= i < m' -> mbyte segs mem' (b' + i) = mbyte segs mem (b' + i)) ->
0 <= lo -> hi <= m -> whi <= wlo ->
region_kept E mem mem' (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E mem mem' n lo hi wlo whi cs b m bl Hn Hin Hk Hlo Hhi Hro.
split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; rewrite Hn; intros a Ha; [|lia].
replace a with (b + (a - b)) by lia. apply (Hk b m (a - b) Hin). lia.
Qed.
Lemma region_kept_pointwise : forall E mem mem' n lo hi wlo whi cs b,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> mbyte segs mem' a = mbyte segs mem a) ->
whi <= wlo ->
region_kept E mem mem' (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E mem mem' n lo hi wlo whi cs b Hn Hk Hro.
split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; rewrite Hn; intros a Ha; [apply Hk; lia | lia].
Qed.
End e0.
Section f0.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis errno_low : errno_addr B + 4 <= alloc_ceiling.
Hypothesis IMG : img_laws B MR.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok (ms_segs B) tbl.
Local Notation segs := (ms_segs B).
Definition wr_ok (E : env) (rs : smem) (STK sp0 : Z) (FP : list (Z * Z)) (bl0 blc : list (Z * Z)) : Prop :=
forall a, in_wrange E rs a -> wr_byte STK sp0 FP bl0 blc a.
Lemma wr_ok_nil : forall E STK sp0 FP bl0 blc, wr_ok E [] STK sp0 FP bl0 blc.
Proof. intros E STK sp0 FP bl0 blc a (r & Hin & _). destruct Hin. Qed.
Lemma wr_ok_cons_ro : forall E r rs STK sp0 FP bl0 blc,
r_whi r <= r_wlo r -> wr_ok E rs STK sp0 FP bl0 blc -> wr_ok E (r :: rs) STK sp0 FP bl0 blc.
Proof.
intros E r rs STK sp0 FP bl0 blc Hro H a (r' & [<-|Hin] & Ha); [lia|]. apply H. exists r'. auto.
Qed.
Lemma wr_ok_cons_stack : forall E r rs STK sp0 FP bl0 blc n,
r_base r = Some n -> bv_unsigned (ew E n) = sp0 -> - STK <= r_wlo r -> r_whi r <= 0 ->
wr_ok E rs STK sp0 FP bl0 blc -> wr_ok E (r :: rs) STK sp0 FP bl0 blc.
Proof.
intros E r rs STK sp0 FP bl0 blc n Hb Hn Hlo Hhi H a (r' & [<-|Hin] & Ha).
- left. rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. lia.
- apply H. exists r'. auto.
Qed.
Lemma wr_ok_cons_block : forall E r rs STK sp0 FP bl0 blc n b m,
r_base r = Some n -> bv_unsigned (ew E n) = b -> In (b, m) blc ->
0 <= r_wlo r -> r_whi r <= m -> (forall a, b + r_wlo r <= a < b + r_whi r -> inFP FP a) ->
wr_ok E rs STK sp0 FP bl0 blc -> wr_ok E (r :: rs) STK sp0 FP bl0 blc.
Proof.
intros E r rs STK sp0 FP bl0 blc n b m Hb Hn Hin Hlo Hhi Hfp H a (r' & [<-|Hin'] & Ha).
- right. left. rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. split; [apply Hfp; lia|].
exists b, m. split; [exact Hin | lia].
- apply H. exists r'. auto.
Qed.
Lemma wr_ok_cons_inblock : forall E r rs STK sp0 FP bl0 blc n p b m,
r_base r = Some n -> bv_unsigned (ew E n) = p -> In (b, m) blc ->
b <= p + r_wlo r -> p + r_whi r <= b + m -> (forall a, p + r_wlo r <= a < p + r_whi r -> inFP FP a) ->
wr_ok E rs STK sp0 FP bl0 blc -> wr_ok E (r :: rs) STK sp0 FP bl0 blc.
Proof.
intros E r rs STK sp0 FP bl0 blc n p b m Hb Hn Hin Hlo Hhi Hfp H a (r' & [<-|Hin'] & Ha).
- right. left. rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. split; [apply Hfp; lia|].
exists b, m. split; [exact Hin | lia].
- apply H. exists r'. auto.
Qed.
Lemma wr_ok_cons_tmp : forall E r rs STK sp0 FP bl0 blc n b m,
r_base r = Some n -> bv_unsigned (ew E n) = b -> In (b, m) blc -> ~ In (b, m) bl0 ->
0 <= r_wlo r -> r_whi r <= m ->
wr_ok E rs STK sp0 FP bl0 blc -> wr_ok E (r :: rs) STK sp0 FP bl0 blc.
Proof.
intros E r rs STK sp0 FP bl0 blc n b m Hb Hn Hin Hn0 Hlo Hhi H a (r' & [<-|Hin'] & Ha).
- right. right. rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha.
exists b, m. split; [exact Hin | split; [exact Hn0 | lia]].
- apply H. exists r'. auto.
Qed.
Lemma SR_run_J : forall n E ss ss' st ms STK sp0 FP L A mem md Lc Ac mdc Q,
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
wr_ok E (ss_mem ss) STK sp0 FP (blocks L A) (blocks Lc Ac) ->
(forall ms', st_ok segs E ss' ms' -> journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') -> mem_grows (ms_mem ms) (ms_mem ms') ->
SR segs (mkCfg ms' mdc) Q) ->
SR segs (mkCfg ms mdc) Q.
Proof.
intros n E ss ss' st ms STK sp0 FP L A mem md Lc Ac mdc Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_run_gen segs tbl tbl_ok n E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & Hfr).
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
apply (SR_msteps segs ms ms' mdc Q Hh Hl Hms). apply Hk.
- destruct st; [exact HS' | destruct Hst | exact HS'].
- eapply (journal_exec B MR LAWS IMG); [exact HJ | exact Hfr | apply (msteps_mem_grows segs); exact Hms | exact Hwr].
- exact Hfr.
- apply (msteps_mem_grows segs). exact Hms.
Qed.
Lemma SR_run_to_J : forall n stop E ss ss' st ms STK sp0 FP L A mem md Lc Ac mdc Q,
st_ok segs E ss ms ->
sym_run_toN segs tbl n stop ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
wr_ok E (ss_mem ss) STK sp0 FP (blocks L A) (blocks Lc Ac) ->
(forall ms', st_ok segs E ss' ms' -> journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') -> mem_grows (ms_mem ms) (ms_mem ms') ->
SR segs (mkCfg ms' mdc) Q) ->
SR segs (mkCfg ms mdc) Q.
Proof.
intros n stop E ss ss' st ms STK sp0 FP L A mem md Lc Ac mdc Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_run_to_gen segs tbl tbl_ok n stop E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & Hfr).
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
apply (SR_msteps segs ms ms' mdc Q Hh Hl Hms). apply Hk.
- destruct st; [exact HS' | destruct Hst | exact HS'].
- eapply (journal_exec B MR LAWS IMG); [exact HJ | exact Hfr | apply (msteps_mem_grows segs); exact Hms | exact Hwr].
- exact Hfr.
- apply (msteps_mem_grows segs). exact Hms.
Qed.
Lemma jfree : free_realizes B MR ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc a n (o : Z) spw tpw raw,
st_ok segs E ss ms -> ss_pc ss = ms_free B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
In (a, n) (blocks Lc Ac) ->
getr (ms_regs ms) 10 = Z_to_bv 64 a ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ALLOC_STACK - o <= STK ->
getr (ms_regs ms) 4 = tpw -> tpw = Z_to_bv 64 (ms_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
(In (a, n) (blocks L A) -> forall i, 0 <= i < n -> inFP FP (a + i)) ->
SR segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\
rm1 (a, n) (blocks Lc Ac) (blocks L2 A2) /\
(forall b m i, In (b, m) (blocks L2 A2) -> 0 <= i < m ->
mbyte segs mem2 (b + i) = mbyte segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 + o - ALLOC_STACK <= x < sp0 + o) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x))).
Proof.
intros HFR E ss ms STK sp0 FP L A mem md Lc Ac mdc a n o spw tpw raw
HS Hpc Hrv HJ Hin Ha0 Hsp HE2 Hspw Hal Hneg Hbud Htp Htpw Hra Hraw HFP.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof alloc_ceiling_val as Hac. assert (ALLOC_STACK = 8192) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. cbn [sv_denot]. rewrite HE2, Hspw. apply unsigned_lit_small. lia. }
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hpc.
apply blocks_In in Hin as (p & Hp & Hpin).
eapply SR_mono.
{ eapply (cg_free B MR LAWS errno_low IMG HFR STK sp0 FP L A mem md Lc Ac (ms_regs ms) (ms_mem ms) mdc p n HJ Hpin).
- rewrite Hp. exact Ha0.
- rewrite Hra. exact Hraw.
- rewrite Hsp'. rewrite Z.add_mod, Hal16, Hal by lia. reflexivity.
- rewrite Hsp'. lia.
- rewrite Hsp'. lia.
- rewrite Htp. exact Htpw.
- rewrite Hp. exact HFP. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hrm & Hkeep & Hhi).
exists L2, A2, regs2, mem2, md2. rewrite Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
rewrite Hp in Hrm. split; [exact Hrm|]. split; [exact Hkeep|].
intros x Hx Hnx. apply Hhi; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
Lemma jmalloc : malloc_realizes B MR ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc n (o : Z) spw tpw raw,
st_ok segs E ss ms -> ss_pc ss = ms_malloc B -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
st_init_done Ac = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ALLOC_STACK - o <= STK ->
getr (ms_regs ms) 4 = tpw -> tpw = Z_to_bv 64 (ms_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SR segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2 (res : Z),
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\
regs_preserved (ms_regs ms) regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
((res = 0 /\ blocks L2 A2 = blocks Lc Ac)
\/ (res <> 0 /\ res mod 16 = 0 /\
(exists b1 b2, blocks L2 A2 = b1 ++ (res, n) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
(forall blc i, In (res, n) blc -> 0 <= i < n -> wr_byte STK sp0 FP (blocks L A) blc (res + i)))) /\
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m ->
mbyte segs mem2 (b + i) = mbyte segs (ms_mem ms) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 + o - ALLOC_STACK <= x < sp0 + o) ->
mbyte segs mem2 x = mbyte segs (ms_mem ms) x /\
(writable_at segs (ms_mem ms) x <-> writable_at segs mem2 x))).
Proof.
intros HMA E ss ms STK sp0 FP L A mem md Lc Ac mdc n o spw tpw raw
HS Hpc Hrv HJ Hid Ha0 Hn Hsp HE2 Hspw Hal Hneg Hbud Htp Htpw Hra Hraw.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof alloc_ceiling_val as Hac. assert (ALLOC_STACK = 8192) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. cbn [sv_denot]. rewrite HE2, Hspw. apply unsigned_lit_small. lia. }
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hpc.
eapply SR_mono.
{ eapply (cg_malloc B MR LAWS errno_low IMG HMA STK sp0 FP L A mem md Lc Ac (ms_regs ms) (ms_mem ms) mdc n HJ Hid Ha0 Hn).
- rewrite Hra. exact Hraw.
- rewrite Hsp'. rewrite Z.add_mod, Hal16, Hal by lia. reflexivity.
- rewrite Hsp'. lia.
- rewrite Hsp'. lia.
- rewrite Htp. exact Htpw. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hr10 & Hres & Hkeep & Hhi).
exists L2, A2, regs2, mem2, md2, res. rewrite Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|].
split; [exact HP2|]. split; [exact Hr10|]. split; [exact Hres|]. split; [exact Hkeep|].
intros x Hx Hnx. apply Hhi; [exact Hx|]. rewrite Hsp'. exact Hnx.
Qed.
Lemma wr_ok_cons_gen : forall E r rs STK sp0 FP bl0 blc k b,
r_base r = Some k -> bv_unsigned (ew E k) = b ->
(forall a, b + r_wlo r <= a < b + r_whi r -> wr_byte STK sp0 FP bl0 blc a) ->
wr_ok E rs STK sp0 FP bl0 blc -> wr_ok E (r :: rs) STK sp0 FP bl0 blc.
Proof.
intros E r rs STK sp0 FP bl0 blc k b Hb Hk Hw H a (r' & [<-|Hin] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hk in Ha. apply Hw. lia.
- apply H. exists r'. auto.
Qed.
Lemma jcall : forall E ss ms STK sp0 FP L A mem md Lc Ac mdc STK1 FP1
(K : layout -> astate -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) raw,
st_ok segs E ss ms -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
getr (ms_regs ms) 1 = raw ->
(fn_pre B MR STK1 Lc Ac (ms_regs ms) (ms_mem ms) mdc ->
SR segs (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs)) mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK1 (spZ (ms_regs ms)) FP1 Lc Ac (ms_mem ms) mdc L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\ K L2 A2 regs2 mem2 md2)) ->
YK0s.ret_ok raw -> spZ (ms_regs ms) mod 16 = 0 -> 0 <= STK1 ->
sp0 - STK <= spZ (ms_regs ms) - STK1 -> spZ (ms_regs ms) <= sp0 ->
getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp B) ->
(forall a, inFP FP1 a -> inFP FP a /\ a < alloc_ceiling) ->
SR segs (mkCfg ms mdc)
(fun c' => exists L2 A2 regs2 mem2 md2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
journal B MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
journal B MR STK1 (spZ (ms_regs ms)) FP1 Lc Ac (ms_mem ms) mdc L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\ K L2 A2 regs2 mem2 md2).
Proof.
intros E ss ms STK sp0 FP L A mem md Lc Ac mdc STK1 FP1 K raw HS Hrv HJ Hra Hcallee Hraw Hal16 Hstk1 Hlo Hhi Htp HF.
rewrite (st_ok_mkst segs E ss ms HS Hrv).
eapply SR_mono.
{ apply Hcallee. eapply (fn_pre_of_journal B MR); [exact HJ | rewrite Hra; exact Hraw | exact Hal16 | exact Hstk1 | exact Hlo | exact Hhi | exact Htp]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK).
exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
eapply (journal_sub B MR); [exact HJ | exact HJ1 | exact Hlo | exact Hhi | exact HF].
Qed.
Lemma jfree_null : free_null_realizes B ->
forall E ss ms md raw,
st_ok segs E ss ms -> ss_pc ss = ms_free B -> ss_resv ss = None ->
m_halted md = None -> m_vm_lazy md = [] ->
getr (ms_regs ms) 10 = Z_to_bv 64 0 ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SR segs (mkCfg ms md) (fun c' => c' = mkCfg (mkst (ms_regs ms) raw (ms_mem ms) (seg_rom segs)) md).
Proof.
intros HFN E ss ms md raw HS Hpc Hrv Hh Hl Ha0 Hra Hraw.
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hpc. cbn [ms_regs ms_mem mkst]. rewrite <- Hra.
apply (cg_free_null B HFN); [rewrite Hra; exact Hraw | exact Ha0 | exact Hh | exact Hl].
Qed.
Definition memcpy_spec (pcm : Z) : Prop :=
forall (bs : list byte) (d s n : word) (mem rom : word -> option byte) (regs : bvmap 5 word),
getr regs 10 = d -> getr regs 11 = s -> getr regs 12 = n ->
bv_unsigned n = Z.of_nat (length bs) ->
rdn segs mem s (length bs) = Some bs ->
store_ok segs mem d (length bs) = true ->
bv_unsigned d + Z.of_nat (length bs) <= 2 ^ 64 ->
bv_unsigned s + Z.of_nat (length bs) <= 2 ^ 64 ->
(bv_unsigned d + Z.of_nat (length bs) <= bv_unsigned s \/ bv_unsigned s + Z.of_nat (length bs) <= bv_unsigned d) ->
exists regs',
msteps segs (mkst regs (Z_to_bv 64 pcm) mem rom) (mkst regs' (v_jalr (getr regs 1) 0) (wbytes mem d bs) rom)
/\ getr regs' 10 = d
/\ (forall r : reg, r <> 5%bv -> r <> 6%bv -> r <> 7%bv -> r <> 11%bv -> r <> 12%bv ->
r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> r <> 28%bv ->
getr regs' r = getr regs r).
Definition MEMCPY_CLOB : list reg := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28]%bv.
Lemma memcpy_clob_in : forall r : reg,
r <> 5%bv -> r <> 6%bv -> r <> 7%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv ->
r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> r <> 28%bv -> reg_in r MEMCPY_CLOB = false.
Proof.
intros r. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [intros; first [reflexivity | congruence] |]). destruct Hin.
Qed.
Lemma memcpy_clob_out : forall r : reg, reg_in r MEMCPY_CLOB = false ->
r <> 5%bv /\ r <> 6%bv /\ r <> 7%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\
r <> 15%bv /\ r <> 16%bv /\ r <> 17%bv /\ r <> 28%bv.
Proof.
intros r Hr. repeat split; intros ->; vm_compute in Hr; discriminate.
Qed.
Lemma rdn_of_present : forall (m : word -> option byte) n a,
(forall i, 0 <= i < Z.of_nat n -> present m (a + i)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
exists bs, rdn segs m (Z_to_bv 64 a) n = Some bs /\ length bs = n.
Proof.
intros m n. induction n as [|n IH]; intros a Hp Ha Hnw.
- exists []. split; reflexivity.
- destruct (Hp 0 ltac:(lia)) as [b Hb]. rewrite Z.add_0_r in Hb.
destruct (IH (a + 1)) as (bs & Hbs & Hlen); [intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply Hp; lia | lia | lia |].
exists (b :: bs). split; [|cbn; lia]. cbn [rdn]. rewrite Hb.
replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)); [rewrite Hbs; reflexivity|].
apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_unsigned 1) with 1. rewrite <- Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma store_ok_of_present : forall (m : word -> option byte) n a,
(forall i, 0 <= i < Z.of_nat n -> present m (a + i)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
store_ok segs m (Z_to_bv 64 a) n = true.
Proof.
intros m n a Hp Ha Hnw. destruct n as [|n']; [reflexivity|].
apply store_ok_of_all; [rewrite unsigned_lit_small by lia; lia|].
intros x Hx. rewrite unsigned_lit_small in Hx by lia.
destruct (Hp (bv_unsigned x - a) ltac:(lia)) as [b Hb]. replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in Hb by lia.
rewrite Z_to_bv_bv_unsigned in Hb. unfold wview. rewrite Hb. discriminate.
Qed.
Lemma jmemcpy : forall pcm, memcpy_spec pcm ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc d src n raw,
st_ok segs E ss ms -> ss_pc ss = pcm -> ss_resv ss = None ->
journal B MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 11 = Z_to_bv 64 src -> getr (ms_regs ms) 12 = Z_to_bv 64 n ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
0 <= n -> 0 <= d -> 0 <= src -> d + n < 2 ^ 64 -> src + n < 2 ^ 64 ->
(forall i, 0 <= i < n -> present (ms_mem ms) (d + i)) ->
(forall i, 0 <= i < n -> present (ms_mem ms) (src + i)) ->
(d + n <= src \/ src + n <= d) ->
(forall a, d <= a < d + n -> wr_byte STK sp0 FP (blocks L A) (blocks Lc Ac) a) ->
SR segs (mkCfg ms mdc)
(fun c' => exists regs2 mem2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) mdc /\
journal B MR STK sp0 FP L A mem md Lc Ac mem2 mdc /\
getr regs2 10 = Z_to_bv 64 d /\
(forall r, reg_in r MEMCPY_CLOB = false -> getr regs2 r = getr (ms_regs ms) r) /\
(forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> mem2 x = ms_mem ms x) /\
mem_grows (ms_mem ms) mem2 /\
(forall i, 0 <= i < n -> mbyte segs mem2 (d + i) = mbyte segs (ms_mem ms) (src + i))).
Proof.
intros pcm HM E ss ms STK sp0 FP L A mem md Lc Ac mdc d src n raw HS Hpc Hrv HJ H10 H11 H12 H1 Hraw
Hn Hd Hs Hdn Hsn Hpd Hps Hdisj HW.
destruct (rdn_of_present (ms_mem ms) (Z.to_nat n) src ltac:(intros i Hi; apply Hps; lia) Hs ltac:(lia)) as (bs & Hbs & Hlen).
pose proof (store_ok_of_present (ms_mem ms) (Z.to_nat n) d ltac:(intros i Hi; apply Hpd; lia) Hd ltac:(lia)) as Hst.
rewrite <- Hlen in Hst.
destruct (HM bs (Z_to_bv 64 d) (Z_to_bv 64 src) (Z_to_bv 64 n) (ms_mem ms) (seg_rom segs) (ms_regs ms) H10 H11 H12)
as (regs2 & Hms & Ha0 & Hfr).
{ rewrite unsigned_lit_small by lia. lia. }
{ rewrite Hlen. exact Hbs. }
{ exact Hst. }
{ rewrite unsigned_lit_small by lia. lia. }
{ rewrite unsigned_lit_small by lia. lia. }
{ rewrite !unsigned_lit_small by lia. lia. }
rewrite (st_ok_mkst segs E ss ms HS Hrv), Hpc.
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply SR_msteps; [exact Hh | exact Hl | exact Hms |].
apply SR_ret. exists regs2, (wbytes (ms_mem ms) (Z_to_bv 64 d) bs). rewrite H1, Hraw.
assert (Hout : forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> wbytes (ms_mem ms) (Z_to_bv 64 d) bs x = ms_mem ms x).
{ intros x Hx. destruct Hx as [Hx|Hx].
- apply wbytes_below; rewrite unsigned_lit_small by lia; lia.
- apply wbytes_above. rewrite unsigned_lit_small by lia. lia. }
split; [reflexivity|]. split.
{ eapply (journal_exec B MR LAWS IMG) with (W := fun a => d <= a < d + n); [exact HJ | | apply wbytes_grows | exact HW].
intros x Hx. apply Hout. lia. }
split; [exact Ha0|]. split.
{ intros r Hr. destruct (memcpy_clob_out r Hr) as (?&?&?&?&?&?&?&?&?&?&?). apply Hfr; assumption. }
split; [exact Hout|]. split; [apply wbytes_grows|].
intros i Hi. rewrite (wbytes_mbyte segs bs (ms_mem ms) d (d + i)) by lia.
replace ((d <=? d + i) && (d + i <? d + Z.of_nat (length bs))) with true.
2:{ symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
apply rdn_mbytes in Hbs. destruct Hbs as [_ Hb].
replace (Z.to_nat (d + i - d)) with (Z.to_nat i) by lia.
rewrite <- (Hb (Z.to_nat i)) by lia.
replace (src + Z.of_nat (Z.to_nat i)) with (src + i) by lia. reflexivity.
Qed.
End f0.
Section g0.
Variable segs : list Segment.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Definition all_ro (rs : smem) : bool := forallb (fun r => r_whi r <=? r_wlo r) rs.
Lemma frame_of_ro : forall E rs m m', all_ro rs = true -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hro Hfr x. apply Hfr. intros (r & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hro r Hin) as Hr'. cbn beta in Hr'. apply Z.leb_le in Hr'. lia.
Qed.
Lemma pure_run_to : forall n stop E ss ss' st ms ms0 (mem0 : word -> option byte),
st_ok segs E ss ms -> sym_run_toN segs tbl n stop ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
all_ro (ss_mem ss) = true ->
msteps segs ms0 ms -> (forall x, ms_mem ms x = mem0 x) ->
exists ms', st_ok segs E ss' ms' /\ msteps segs ms0 ms' /\ (forall x, ms_mem ms' x = mem0 x).
Proof.
intros n stop E ss ss' st ms ms0 mem0 HS Hrun Hst Hro Hacc Hmem.
destruct (msteps_run_to_gen segs tbl tbl_ok n stop E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & Hfr).
exists ms'. split; [destruct st; [exact HS' | destruct Hst | exact HS']|].
split; [eapply msteps_trans; [exact Hacc | exact Hms]|].
intros x. rewrite (frame_of_ro E _ _ _ Hro Hfr x). apply Hmem.
Qed.
Lemma pure_run : forall n E ss ss' st ms ms0 (mem0 : word -> option byte),
st_ok segs E ss ms -> sym_runN segs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
all_ro (ss_mem ss) = true ->
msteps segs ms0 ms -> (forall x, ms_mem ms x = mem0 x) ->
exists ms', st_ok segs E ss' ms' /\ msteps segs ms0 ms' /\ (forall x, ms_mem ms' x = mem0 x).
Proof.
intros n E ss ss' st ms ms0 mem0 HS Hrun Hst Hro Hacc Hmem.
destruct (msteps_run_gen segs tbl tbl_ok n E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & Hfr).
exists ms'. split; [destruct st; [exact HS' | destruct Hst | exact HS']|].
split; [eapply msteps_trans; [exact Hacc | exact Hms]|].
intros x. rewrite (frame_of_ro E _ _ _ Hro Hfr x). apply Hmem.
Qed.
Lemma pure_ret : forall E ss ms ms0,
st_ok segs E ss ms -> ss_resv ss = None -> clookup tbl (ss_pc ss) = Some RET_WORD ->
msteps segs ms0 ms ->
msteps segs ms0 (mkst (ms_regs ms) (v_jalr (getr (ms_regs ms) 1) 0) (ms_mem ms) (seg_rom segs)).
Proof.
intros E ss ms ms0 HS Hrv Hpc Hacc.
eapply msteps_trans; [exact Hacc|].
rewrite (st_ok_mkst segs E ss ms HS Hrv) at 1.
eapply msteps_one; [reflexivity|].
change 0 with (bv_signed (0%bv : bv 12)).
eapply (step_jalr_x0 segs _ _ _ _ (0x00008067%bv : bv 32) 1 (0%bv : bv 12)).
- rewrite <- (Z_to_bv_bv_unsigned 32 (0x00008067%bv : bv 32)). apply tbl_ok. exact Hpc.
- reflexivity.
- exact (decode_ret).
- reflexivity.
Qed.
Lemma frame_of_nil : forall E m m' x, frame_of E [] m m' -> m' x = m x.
Proof. intros E m m' x H. apply H. intros (r & Hin & _). destruct Hin. Qed.
Lemma frame_of_one : forall E m m' r lo hi x,
frame_of E [r] m m' ->
lo <= base_val E (r_base r) + r_wlo r -> base_val E (r_base r) + r_whi r <= hi ->
(bv_unsigned x < lo \/ hi <= bv_unsigned x) -> m' x = m x.
Proof.
intros E m m' r lo hi x H Hlo Hhi Hx. apply H. intros (r' & [<-|[]] & Hr). lia.
Qed.
End g0.
End u.
Ltac jrun LAWS tblok HS HJ :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in
let IMG := lazymatch goal with IMG : img_laws _ _ |- _ => IMG end in
eapply (SR_run_J _ _ LAWS IMG _ tblok FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
clear Hrun;
[ | clear HS HJ;
try match type of ms with machine_state => clear ms | _ => idtac end;
let HF := fresh "HF" in let HG := fresh "HG" in
intros ms' HS HJ HF HG;
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
let rsv := eval vm_compute in rs in change (frame_of E1 rsv m1 m2) in HF end ]
end
end
end.
Ltac jrun_to LAWS tblok HS HJ stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toN segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in
let IMG := lazymatch goal with IMG : img_laws _ _ |- _ => IMG end in
eapply (SR_run_to_J _ _ LAWS IMG _ tblok FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
clear Hrun;
[ | clear HS HJ;
try match type of ms with machine_state => clear ms | _ => idtac end;
let HF := fresh "HF" in let HG := fresh "HG" in
intros ms' HS HJ HF HG;
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
let rsv := eval vm_compute in rs in change (frame_of E1 rsv m1 m2) in HF end ]
end
end
end.
Ltac jbranch tbl HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let why := sym_why segs tbl ss in
lazymatch why with
| SR_branch ?c ?a ?b =>
apply (SR_branch_J segs E ss ms _ _ c a b HS); clear HS;
let Hc := fresh "Hc" in intros Hc HS
| _ => fail "jbranch: state is not stuck at a branch:" why
end
end.
Ltac zlit_tac := cbv; first [reflexivity | discriminate | lia | (intros; discriminate)].
Ltac wr_ok_tac :=
lazymatch goal with |- wr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc =>
let rs' := eval vm_compute in rs in change (wr_ok E rs' stk sp0 fp b0 bc) end;
repeat first
[ apply wr_ok_nil
| apply wr_ok_cons_ro; [zlit_tac|]
| eapply wr_ok_cons_stack; [reflexivity | | zlit_tac | zlit_tac |] ].
Ltac ew_havoc := repeat (rewrite ew_havoc_old; [|cbv; lia]).
Tactic Notation "jreg" constr(HS) constr(r) "as" ident(Hr) :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
pose proof (st_ok_reg segs E ss ms r HS) as Hr;
eval_sr_get_in Hr; cbn [sv_denot] in Hr;
repeat (rewrite ew_havoc_old in Hr; [|cbv; lia]);
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hr
end.
Ltac jafter_call HS k regs2 mem2 HP HS2 :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let rs := eval vm_compute in (ss_mem ss) in
let retpc := eval vm_compute in (match sr_get (ss_regs ss) 1 with SLit z => z | _ => 0 end) in
pose proof (st_ok_after_call segs k E ss ms regs2 mem2 rs retpc HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) (submem_refl rs) ltac:(vm_compute; reflexivity) HP) as HS2;
let ss2 := eval vm_compute in (ss_after_call ss rs k retpc) in
change (ss_after_call ss rs k retpc) with ss2 in HS2
end.
Ltac submem_tac :=
repeat first [ apply submem_nil
| apply submem_keep; [apply subregion_refl|]
| apply submem_drop ].
Ltac jafter_call_keep HS k regs2 mem2 HP idxs HS2 :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
let retpc := eval vm_compute in (match sr_get (ss_regs ss) 1 with SLit z => z | _ => 0 end) in
pose proof (st_ok_after_call segs k E ss ms regs2 mem2 rs retpc HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) HP) as HS2;
let ss2 := eval vm_compute in (ss_after_call ss rs k retpc) in
change (ss_after_call ss rs k retpc) with ss2 in HS2
end.
Ltac jafter_call2 HS k regs2 mem2 HP stklo idxs HS2 :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let m := eval vm_compute in (ss_mem ss) in
let rs := lazymatch m with
| ?r0 :: ?rest => let kept := eval vm_compute in (pick rest idxs) in constr:(trim_lo r0 stklo :: kept)
end in
let retpc := eval vm_compute in (match sr_get (ss_regs ss) 1 with SLit z => z | _ => 0 end) in
pose proof (st_ok_after_call segs k E ss ms regs2 mem2 rs retpc HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_trim_lo | submem_tac])
ltac:(vm_compute; reflexivity) HP) as HS2;
let rsv := eval vm_compute in rs in
change rs with rsv in HS2;
let ss2 := eval vm_compute in (ss_after_call ss rsv k retpc) in
change (ss_after_call ss rsv k retpc) with ss2 in HS2
end.
Ltac prun_to tblok HS Hacc Hmem stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toN segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let H := fresh in
pose proof (pure_run_to segs tbl tblok FUEL stop E ss ss' st ms _ _ HS Hrun I ltac:(vm_compute; reflexivity) Hacc Hmem) as H;
clear Hrun HS Hacc Hmem;
try match type of ms with machine_state => clear ms | _ => idtac end;
let ms' := fresh "ms" in
destruct H as (ms' & HS & Hacc & Hmem)
end
end
end.
Ltac prun tblok HS Hacc Hmem :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let H := fresh in
pose proof (pure_run segs tbl tblok FUEL E ss ss' st ms _ _ HS Hrun I ltac:(vm_compute; reflexivity) Hacc Hmem) as H;
clear Hrun HS Hacc Hmem;
try match type of ms with machine_state => clear ms | _ => idtac end;
let ms' := fresh "ms" in
destruct H as (ms' & HS & Hacc & Hmem)
end
end
end.
Ltac pbranch tbl HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let why := sym_why segs tbl ss in
lazymatch why with
| SR_branch ?c ?a ?b =>
let Hc := fresh "Hc" in let HS' := fresh "HS" in
destruct (branch_taken c (sv_denot E a) (sv_denot E b)) eqn:Hc;
[ pose proof (st_ok_add_cond segs E ss ms c a b HS Hc) as HS'
| pose proof (st_ok_add_cond_neg segs E ss ms c a b HS Hc) as HS' ];
clear HS; rename HS' into HS
| _ => fail "pbranch: state is not stuck at a branch:" why
end
end.
Ltac jafter_stretch HS k regs2 mem2 clob newpc HS2 :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let rs := eval vm_compute in (ss_mem ss) in
pose proof (st_ok_after_stretch segs k E ss ms regs2 mem2 rs newpc clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) (submem_refl rs) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs k clob newpc) in
change (ss_after_stretch ss rs k clob newpc) with ss2 in HS2
end.
Ltac wr_norm :=
lazymatch goal with |- wr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc =>
let rs' := eval vm_compute in rs in change (wr_ok E rs' stk sp0 fp b0 bc) end.
Section h0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma reg_in_cons_false : forall (r x : reg) l, reg_in r (x :: l) = false -> reg_in r l = false.
Proof. intros r x l H. cbn [reg_in] in H |- *. destruct (bv_eqb r x); [discriminate|exact H]. Qed.
End h0.
