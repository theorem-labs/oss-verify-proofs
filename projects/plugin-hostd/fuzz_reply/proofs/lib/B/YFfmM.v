(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/YFfmM.v (commit 237eb205ab7b, H4 srrm M walk (image-specific files); file sha256 88bcd8920c6c) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/YFfmM.v at commit c83cc72b041, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10-30: new file (lane B1, slice H4, row srrm-walk; the memset leaf on the SRr_stepM engine).
   rule 24: no function proved (srrm-walk bookkeeping: the memset leaf of the secondary recycle walk, already proved by
   YFfm.memset_stretch_nw, re-run on the materialized-page engine).

   WHAT.  [memset_stretch_nwM] proves DMrcSecMat.memset_nwM_t: YFfm.memset_stretch_nw, with one more continuation
   premise, every page materialized after the memset was materialized before it or is the page of a byte of the
   stretch [d, d + len).

   HOW.  YE3d.tfib_memset gives only a plain msteps chain, and an arbitrary chain may leave the memset code (its last
   jalr returns to the caller) and come back, so its accesses are not bounded by the code.  So the chain is built again
   here, step by step, as a chain that records each step's access report and that report's bound ([fmA_mst]): the
   proof of YE3d (Section g) is copied with its step tactics wrapped.  A step of a non-memory instruction (branch, ALU,
   lui, mul, jalr) reports no access ([fmA_acc_nil]); a store reports exactly its address range ([fmA_acc_store]),
   and every store of the memset writes inside [d, d + len) (the bound the copied proof already checks for store_ok).
   Instruction fetches are not data accesses.  The chain is then fed to YA0nM.SRr_mstepsM, whose mat_in fact gives the
   new premise. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f YG0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0l YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YE3d YFeq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0x YA0nM.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DMrcSecMat.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The access report of one step, for the instruction kinds the memset runs. *)
Definition fmA_nonmem (i : Instr.instr) : bool :=
match i with
| Instr.Branch _ _ _ _ | Instr.Op _ _ _ _ | Instr.OpImm _ _ _ _ | Instr.Op32 _ _ _ _ | Instr.ShiftImm _ _ _ _
| Instr.Lui _ _ | Instr.Mul _ _ _ _ | Instr.Jalr _ _ _ => true
| _ => false
end.

Definition fmA_msz (sz : Instr.msize) : nat :=
match sz with Instr.SZ1 => 1 | Instr.SZ2 => 2 | Instr.SZ4 => 4 | Instr.SZ8 => 8 end%nat.

Ltac fmA_unfold Hf He Hd Hr :=
unfold RiscvSemantics.step_accesses in Hr; cbn [ms_pc ms_pc_val mkst] in Hr; rewrite Hf in Hr; cbv beta iota in Hr;
unfold RiscvSemantics.decode_exec_accesses in Hr; rewrite He in Hr; cbv beta iota in Hr; rewrite Hd in Hr;
cbv beta iota in Hr.

Section a. Context {fx : YK11.FPState}.
(* A branch, ALU, lui, mul or jalr step reports no memory access. *)
Lemma fmA_acc_nil : forall segs regs pc mem rom w i ms',
fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) -> fmA_nonmem i = true ->
RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk ms' ->
step_accesses segs (mkst regs pc mem rom) = MachineOk (@mkAccessReport _ ms' []).
Proof.
intros segs regs pc mem rom w i ms' Hf He Hd Hn Hs.
destruct (step_report segs _ _ Hs) as [rs Hr]. rewrite Hr.
enough (E : rs = []) by (rewrite E; reflexivity).
fmA_unfold Hf He Hd Hr.
destruct i; try discriminate Hn;
cbv beta iota zeta delta [RiscvSemantics.interp_eff_accesses Sem.exec] in Hr;
cbn [access_value accessed_ranges] in Hr;
injection Hr as _ Hrs; symmetry; exact Hrs.
Qed.

(* A store step reports exactly its address range. *)
Lemma fmA_acc_store : forall segs regs pc mem rom w sz rs1 rs2 imm a ms',
fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Instr.Store sz rs1 rs2 imm, 4%Z) ->
v_addi (getr regs rs1) (bv_signed imm) = a ->
RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk ms' ->
step_accesses segs (mkst regs pc mem rom) = MachineOk (@mkAccessReport _ ms' [(a, fmA_msz sz)]).
Proof.
intros segs regs pc mem rom w sz rs1 rs2 imm a ms' Hf He Hd Ha Hs.
destruct (step_report segs _ _ Hs) as [rs Hr]. rewrite Hr.
enough (E : rs = [(a, fmA_msz sz)]) by (rewrite E; reflexivity).
fmA_unfold Hf He Hd Hr. subst a. rewrite <- b_addsext.
destruct sz;
cbv beta iota zeta delta [RiscvSemantics.interp_eff_accesses Sem.exec Sem.store_val] in Hr;
(lazymatch type of Hr with
 | context [RiscvSemantics.store_ok ?s ?m ?x ?n] => destruct (RiscvSemantics.store_ok s m x n)
 end; cbn [access_value accessed_ranges] in Hr; [|discriminate Hr]);
injection Hr as _ Hrs; rewrite <- Hrs; reflexivity.
Qed.
End a.

(* Every byte of every access lies in [lo, hi). *)
Definition fmA_accsB (lo hi : Z) (rs : list (word * nat)) : Prop :=
forall a n k, In (a, n) rs -> (k < n)%nat -> lo <= bv_unsigned a + Z.of_nat k < hi.

Lemma fmA_accsB_nil : forall lo hi, fmA_accsB lo hi [].
Proof. intros lo hi a n k []. Qed.

Lemma fmA_accsB_one : forall lo hi a n, lo <= a -> a + Z.of_nat n <= hi -> 0 <= lo -> hi <= 2 ^ 64 ->
fmA_accsB lo hi [(Z_to_bv 64 a, n)].
Proof.
intros lo hi a n H1 H2 H3 H4 a' n' k [E|[]] Hk. injection E as <- <-.
assert (Hw : bv_wrap 64 a = a) by (apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia).
rewrite Z_to_bv_unsigned, Hw. lia.
Qed.

Lemma fmA_accsB_app : forall lo hi r1 r2, fmA_accsB lo hi r1 -> fmA_accsB lo hi r2 -> fmA_accsB lo hi (r1 ++ r2).
Proof.
intros lo hi r1 r2 H1 H2 a n k Hin Hk. apply in_app_or in Hin as [Hin|Hin]; [exact (H1 a n k Hin Hk) | exact (H2 a n k Hin Hk)].
Qed.

(* A chain whose every step's access report lies in [lo, hi). *)
Inductive fmA_mst (segs : list Segment) (lo hi : Z) : machine_state -> machine_state -> Prop :=
| fmA_mst_refl : forall s, fmA_mst segs lo hi s s
| fmA_mst_step : forall s s1 s2 rs, ms_svc_pending s = None ->
    step_accesses segs s = MachineOk (@mkAccessReport _ s1 rs) -> fmA_accsB lo hi rs ->
    fmA_mst segs lo hi s1 s2 -> fmA_mst segs lo hi s s2.

Lemma fmA_mst_trans : forall segs lo hi s t u, fmA_mst segs lo hi s t -> fmA_mst segs lo hi t u -> fmA_mst segs lo hi s u.
Proof.
intros segs lo hi s t u H. induction H as [s | s s1 s2 rs Hsvc Hst HB H IH]; intros Hu; [exact Hu|].
eapply fmA_mst_step; [exact Hsvc | exact Hst | exact HB | exact (IH Hu)].
Qed.

Lemma fmA_mst_acc : forall segs lo hi s t, fmA_mst segs lo hi s t ->
exists accs, msteps_acc segs s t accs /\ fmA_accsB lo hi accs.
Proof.
intros segs lo hi s t H. induction H as [s | s s1 s2 rs Hsvc Hst HB H [accs [Ha HBa]]].
- exists []. split; [apply msta_refl | apply fmA_accsB_nil].
- exists (rs ++ accs). split; [eapply msta_step; eassumption | apply fmA_accsB_app; assumption].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The memset chain on [fmA_mst]: YE3d's environment and its step tactics, each step also proving its report's bound. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0w.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1w.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0f YO0g YO0a YO0c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac chain_stepA := eapply fmA_mst_step.
Ltac norm_pcA := try lazymatch goal with |- fmA_mst _ _ _ ?st _ => norm_pc_state st end.
Ltac step_simplA := reduce_bv_eqb_ifs; rewrite ?skipn_O; norm_pcA.
Ltac accs_one := apply fmA_accsB_one; [lia | cbn [fmA_msz]; lia | lia | lia].
Ltac stepivA F D vv tac :=
chain_stepA;
[ reflexivity
| eapply fmA_acc_nil; [ exact F | reflexivity | exact D | reflexivity |
lazymatch type of D with
| decode_any _ = Some (OpImm ALU_ADD _ _ _, _) =>
eapply step_addi_at with (v := vv)
| decode_any _ = Some (OpImm ALU_AND _ _ _, _) =>
eapply step_andi_at with (v := vv)
| decode_any _ = Some (ShiftImm ALU_SLL _ _ _, _) =>
eapply step_slli_at with (v := vv)
| decode_any _ = Some (ShiftImm ALU_SRL _ _ _, _) =>
eapply step_srli_at with (v := vv)
| decode_any _ = Some (Op ALU_ADD _ _ _, _) =>
eapply step_add_at with (v := vv)
| decode_any _ = Some (Op ALU_SUB _ _ _, _) =>
eapply step_sub_at with (v := vv)
| decode_any _ = Some (Lui _ _, _) =>
eapply step_lui_at with (v := vv)
| _ => eapply step_addi_at with (v := vv)
end;
[ exact F | reflexivity | exact D | reflexivity | tac ] ]
| apply fmA_accsB_nil
| step_simplA ].
Ltac sv F D vv := let F' := litF F in stepivA F' D vv val.
Ltac svor F0 D vv := let F := litF F0 in
chain_stepA;
[ reflexivity
| eapply fmA_acc_nil; [ exact F | reflexivity | exact D | reflexivity |
eapply step_or_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | val ] ]
| apply fmA_accsB_nil
| step_simplA ].
Ltac stepbt F0 D := let F := litF F0 in
chain_stepA;
[ reflexivity
| eapply fmA_acc_nil; [ exact F | reflexivity | exact D | reflexivity |
eapply step_branch_tk_gen; [ exact F | reflexivity | exact D | brc ] ]
| apply fmA_accsB_nil
| step_simplA ].
Ltac stepbf F0 D := let F := litF F0 in
chain_stepA;
[ reflexivity
| eapply fmA_acc_nil; [ exact F | reflexivity | exact D | reflexivity |
eapply step_branch_ft_gen; [ exact F | reflexivity | exact D | brc ] ]
| apply fmA_accsB_nil
| step_simplA ].
Ltac stepret F0 D := let F := litF F0 in
chain_stepA;
[ reflexivity
| eapply fmA_acc_nil; [ exact F | reflexivity | exact D | reflexivity |
eapply step_jalr_x0; [ exact F | reflexivity | exact D | gr; reflexivity ] ]
| apply fmA_accsB_nil
| step_simplA; imm_norm ].

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variables d cw : word.
Variable n : nat.
Variables mem rom : word -> option byte.
Definition D : Z := bv_unsigned d.
Definition N : Z := Z.of_nat n.
Definition C : Z := bv_unsigned cw mod 256.
Definition cb : byte := Z_to_bv 8 C.
Definition c32w : word := Z_to_bv 64 (c32_of C).
Definition c64w : word := Z_to_bv 64 (c64_of C).
Hypothesis Hdst : store_ok tfibsegs mem d n = true.
Hypothesis Hnd : bv_unsigned d + Z.of_nat n <= 2^64.
Hypothesis HN64 : Z.of_nat n < 2^64.
Lemma D_facts : D = bv_unsigned d /\ N = Z.of_nat n /\ 0 <= D < 2^64 /\ 0 <= N < 2^64 /\ D + N <= 2^64 /\ 0 <= C < 256.
Proof.
pose proof (u64_range d). unfold D, N, C.
pose proof (Z.mod_pos_bound (bv_unsigned cw) 256 ltac:(lia)). lia.
Qed.
Ltac dfacts := pose proof D_facts as HDF; destruct HDF as (HD_ & HN_ & HDr & HNr & HDN & HCr).
Definition inv (m : word -> option byte) : Prop :=
mem_grows mem m /\
forall x, m x = mem x \/ (D <= bv_unsigned x < D + N /\ m x = Some cb).
Definition cov (m : word -> option byte) (a k : Z) : Prop :=
forall x : word, a <= bv_unsigned x < a + k -> m x = Some cb.
Definition fill (m : word -> option byte) (a : Z) (k : nat) : word -> option byte :=
wbytes m (Z_to_bv 64 a) (repeat cb k).
Lemma inv_mem : inv mem.
Proof. split; [apply mem_grows_refl|]. intros x. left. reflexivity. Qed.
Lemma fill_spec : forall m a k x, 0 <= a -> (0 < k)%nat -> a + Z.of_nat k <= 2^64 ->
fill m a k x = if (a <=? bv_unsigned x) && (bv_unsigned x <? a + Z.of_nat k) then Some cb else m x.
Proof.
intros m a k x Ha Hk0 Hk. unfold fill. rewrite wbytes_repeat_spec by (rewrite u_Z2bv by lia; lia).
rewrite u_Z2bv by lia. reflexivity.
Qed.
Lemma inv_fill : forall m a k, inv m -> (0 < k)%nat -> D <= a -> a + Z.of_nat k <= D + N -> inv (fill m a k).
Proof.
intros m a k [Hg Hi] Hk0 Ha Hk. dfacts. split.
- eapply mem_grows_trans; [exact Hg|]. unfold fill. apply wbytes_grows.
- intros x. rewrite fill_spec by lia.
destruct (_ && _) eqn:E.
+ apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. right. split; [lia|reflexivity].
+ apply Hi.
Qed.
Lemma cov_fill_new : forall m a k, 0 <= a -> (0 < k)%nat -> a + Z.of_nat k <= 2^64 -> cov (fill m a k) a (Z.of_nat k).
Proof.
intros m a k Ha Hk0 Hk x Hx. rewrite fill_spec by lia.
replace (_ && _) with true; [reflexivity|].
symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.
Lemma cov_fill_keep : forall m a k a' k', 0 <= a -> (0 < k)%nat -> a + Z.of_nat k <= 2^64 ->
cov m a' k' -> cov (fill m a k) a' k'.
Proof.
intros m a k a' k' Ha Hk0 Hk Hc x Hx. rewrite fill_spec by lia.
destruct (_ && _); [reflexivity|]. apply Hc. exact Hx.
Qed.
Definition covP (m : word -> option byte) (P : Z -> Prop) : Prop :=
forall x : word, D <= bv_unsigned x < D + N -> P (bv_unsigned x) -> m x = Some cb.
Lemma covP_fill : forall m a k (P Q : Z -> Prop), 0 <= a -> (0 < k)%nat -> a + Z.of_nat k <= 2^64 ->
covP m P ->
(forall z, D <= z < D + N -> Q z -> P z \/ a <= z < a + Z.of_nat k) ->
covP (fill m a k) Q.
Proof.
intros m a k P Q Ha Hk0 Hk Hc HQ x Hx HQx. rewrite fill_spec by lia.
destruct (_ && _) eqn:E; [reflexivity|].
destruct (HQ _ Hx HQx) as [HP|Hin]; [apply Hc; assumption|].
exfalso. apply andb_false_iff in E. destruct E as [E|E]; [apply Z.leb_gt in E|apply Z.ltb_ge in E]; lia.
Qed.
Lemma covP_weaken : forall m (P Q : Z -> Prop),
covP m P -> (forall z, D <= z < D + N -> Q z -> P z) -> covP m Q.
Proof. intros m P Q Hc HQ x Hx HQx. apply Hc; [exact Hx|]. apply HQ; assumption. Qed.
Definition post (m' : word -> option byte) : Prop :=
(forall x : word, D <= bv_unsigned x < D + N -> m' x = Some cb) /\
(forall x : word, ~ (D <= bv_unsigned x < D + N) -> m' x = mem x).
Lemma post_of_inv : forall m, inv m -> covP m (fun _ => True) -> post m.
Proof.
intros m [Hg Hi] Hc. split.
- intros x Hx. apply Hc; [exact Hx|exact I].
- intros x Hx. destruct (Hi x) as [E|[Hr E]]; [exact E|]. exfalso. apply Hx. exact Hr.
Qed.
Lemma fill_ok : forall m a k, inv m -> (0 < k)%nat -> D <= a -> a + Z.of_nat k <= D + N ->
store_ok tfibsegs m (Z_to_bv 64 a) k = true.
Proof.
intros m a k [Hg _] Hk0 Ha Hk. dfacts.
eapply store_ok_mono; [exact Hg|].
eapply (store_ok_sub tfibsegs mem d _ n); [lia | exact Hdst | |]; rewrite u_Z2bv by lia; lia.
Qed.
Lemma cb_of_cw : Z_to_bv 8 (bv_unsigned cw) = cb.
Proof.
unfold cb, C. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma sb_bytes : word_to_le_bytes 1 cw = repeat cb 1.
Proof. unfold word_to_le_bytes. cbn [Z_to_le_bytes repeat]. rewrite cb_of_cw. reflexivity. Qed.
Lemma sb_bytes1 : word_to_le_bytes 1 cw = [cb].
Proof. exact sb_bytes. Qed.
Lemma sw_bytes : word_to_le_bytes 4 c32w = repeat cb 4.
Proof. dfacts. unfold c32w, cb. apply (proj1 (proj2 (fill_facts C ltac:(lia)))). Qed.
Lemma sd_bytes : word_to_le_bytes 8 c64w = repeat cb 8.
Proof. dfacts. unfold c64w, cb. apply (proj1 (proj2 (proj2 (fill_facts C ltac:(lia))))). Qed.
Lemma c32_range : 0 <= c32_of C < 2^32.
Proof. dfacts. unfold c32_of. lia. Qed.
Lemma c64_range : 0 <= c64_of C < 2^64.
Proof. dfacts. unfold c64_of. lia. Qed.
Lemma slli56_val : v_slli cw 56 = Z_to_bv 64 (C * 2^56).
Proof.
dfacts. unfold v_slli, C. apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite Z.shiftl_mul_pow2 by lia.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
pose proof (u64_range cw). rewrite (Z.div_mod (bv_unsigned cw) 256) at 1 by lia.
replace ((256 * (bv_unsigned cw / 256) + bv_unsigned cw mod 256) * 2^56)
with (bv_unsigned cw mod 256 * 2^56 + (bv_unsigned cw / 256) * 2^64) by lia.
rewrite Z.mod_add by lia.
pose proof (Z.mod_pos_bound (bv_unsigned cw) 256 ltac:(lia)).
rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma mulhu_val : v_mulhu (Z_to_bv 64 (C * 2^56)) (Z_to_bv 64 0x101010100) = c32w.
Proof.
dfacts. unfold v_mulhu, c32w. f_equal. rewrite !u_Z2bv by lia.
apply (fill_facts C). lia.
Qed.
Lemma c64_val : v_or (v_slli c32w 32) (v_srli (v_slli c32w 32) 32) = c64w.
Proof.
dfacts. pose proof c32_range. pose proof c64_range.
unfold v_or, v_slli, v_srli, c32w, c64w. f_equal.
rewrite !Z.shiftl_mul_pow2 by lia. rewrite (u_Z2bv (c32_of C)) by lia.
rewrite (u_Z2bv (c32_of C * 2^32)) by lia.
assert (Hs : 0 <= Z.shiftr (c32_of C * 2^32) 32 < 2^64).
{ rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
rewrite u_Z2bv by lia.
apply (fill_facts C). lia.
Qed.
Lemma negand3_val : v_andi (v_subw (Z_to_bv 64 0) d) 3 = Z_to_bv 64 ((- D) mod 4).
Proof.
dfacts. unfold v_andi, v_subw. f_equal.
rewrite Z_to_bv_unsigned, wrap64_swrap32.
change (bv_wrap 64 3) with (Z.ones 2). rewrite land_sx32_small by (split; [easy|reflexivity]).
rewrite Z.land_ones by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0. unfold D. f_equal.
Qed.
Lemma andm4_val : forall z, 0 <= z < 2^64 -> v_andi (Z_to_bv 64 z) (-4) = Z_to_bv 64 (z - z mod 4).
Proof.
intros z Hz. unfold v_andi. f_equal. rewrite u_Z2bv by lia.
change (bv_wrap 64 (-4)) with (2^64 - 2^2). rewrite land_neg_pow2_u64 by lia. reflexivity.
Qed.
Lemma and4_val : forall z, 0 <= z < 2^64 -> v_andi (Z_to_bv 64 z) 4 = Z_to_bv 64 (Z.land z 4).
Proof. intros z Hz. unfold v_andi. f_equal. rewrite u_Z2bv by lia. reflexivity. Qed.
Definition keep (r : reg) : Prop :=
r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv.
Definition fin (regs : bvmap 5 word) (pc : word) (m : word -> option byte) : Prop :=
exists regs' m',
fmA_mst tfibsegs D (D + N) (mkst regs pc m rom) (mkst regs' (v_jalr (getr regs 1) 0) m' rom)
/\ post m'
/\ forall r, keep r -> getr regs' r = getr regs r.
Lemma keep_1 : keep 1.
Proof. unfold keep. repeat split; reg_neq_tac. Qed.
Lemma fin_steps : forall regs pc m regs2 pc2 m2,
fmA_mst tfibsegs D (D + N) (mkst regs pc m rom) (mkst regs2 pc2 m2 rom) ->
(forall r, keep r -> getr regs2 r = getr regs r) ->
fin regs2 pc2 m2 -> fin regs pc m.
Proof.
intros regs pc m regs2 pc2 m2 Hms Hfr (regs' & m' & Hms' & Hp & Hfr').
exists regs', m'. split; [|split; [exact Hp|]].
- eapply fmA_mst_trans; [exact Hms|]. rewrite <- (Hfr 1%bv keep_1). exact Hms'.
- intros r Hr. rewrite (Hfr' r Hr). apply Hfr. exact Hr.
Qed.
Lemma fin_pc : forall regs (pc pc' : word) m,
bv_unsigned pc = bv_unsigned pc' -> fin regs pc' m -> fin regs pc m.
Proof. intros regs pc pc' m H Hf. replace pc with pc' by (apply bv_eq; symmetry; exact H). exact Hf. Qed.
Ltac frame :=
let r := fresh "r" in let Hr := fresh "Hkeep" in
intros r Hr; unfold keep in Hr;
destruct Hr as (?&?&?&?&?&?);
rewrite ?getr_other by assumption; reflexivity.
Ltac fin_apply L :=
eapply fin_pc; [ | eapply L ]; [ vm_compute; reflexivity | .. ].
Lemma ret_0f4 : forall regs m, inv m -> covP m (fun _ => True) ->
fin regs (Z_to_bv 64 (tfib_A_musl_memset + 0xf4)) m.
Proof.
intros regs m Hi Hc. exists regs, m. split; [|split; [apply post_of_inv; assumption|intros; reflexivity]].
norm_pcA. stepret F_0f4 D_0f4. apply fmA_mst_refl.
Qed.
Lemma store_ok_fill : forall m a' k' a k,
store_ok tfibsegs m a k = true -> store_ok tfibsegs (fill m a' k') a k = true.
Proof. intros. eapply store_ok_mono; [|eassumption]. unfold fill. apply wbytes_grows. Qed.
Lemma covP_fill' : forall m a k (P : Z -> Prop), 0 <= a -> (0 < k)%nat -> a + Z.of_nat k <= 2^64 ->
covP m P -> covP (fill m a k) (fun z => P z \/ a <= z < a + Z.of_nat k).
Proof. intros m a k P Ha Hk0 Hk Hc. eapply covP_fill; [exact Ha|exact Hk0|exact Hk|exact Hc|]. intros z _ Hz. exact Hz. Qed.
Ltac solve_ok := repeat apply store_ok_fill; apply fill_ok; [assumption | cbv; lia | lia | lia].
Ltac fold_fill k :=
lazymatch goal with
| |- context [wbytes ?m' (Z_to_bv 64 ?a') (repeat cb k)] =>
change (wbytes m' (Z_to_bv 64 a') (repeat cb k)) with (fill m' a' k)
end.
Ltac stepsd F0 D0 addr :=
let F := litF F0 in
chain_stepA;
[ reflexivity
| eapply fmA_acc_store with (a := Z_to_bv 64 addr); [ exact F | reflexivity | exact D0 | val |
eapply step_sd_at with (a := Z_to_bv 64 addr) (v := c64w);
[ exact F | reflexivity | exact D0 | val | gr; rwH; reflexivity | solve_ok ] ]
| accs_one
| step_simplA; rewrite sd_bytes; fold_fill 8%nat ].
Ltac stepsw F0 D0 addr :=
let F := litF F0 in
chain_stepA;
[ reflexivity
| eapply fmA_acc_store with (a := Z_to_bv 64 addr); [ exact F | reflexivity | exact D0 | val |
eapply step_sw_at with (a := Z_to_bv 64 addr) (v := c32w);
[ exact F | reflexivity | exact D0 | val | gr; rwH; reflexivity | solve_ok ] ]
| accs_one
| step_simplA; rewrite sw_bytes; fold_fill 4%nat ].
Ltac stepsb F0 D0 addr :=
let F := litF F0 in
chain_stepA;
[ reflexivity
| eapply fmA_acc_store with (a := Z_to_bv 64 addr); [ exact F | reflexivity | exact D0 | val |
eapply step_sb_l with (a := addr) (b := cb);
[ exact F | reflexivity | exact D0 | val | gr; rwH; apply sb_bytes1 | solve_ok ] ]
| accs_one
| step_simplA;
lazymatch goal with
| |- context [wbytes ?m' (Z_to_bv 64 ?a') [cb]] =>
change (wbytes m' (Z_to_bv 64 a') [cb]) with (fill m' a' 1)
end ].
Ltac inv_tac := repeat (apply inv_fill; [|cbv; lia|lia|lia]); assumption.
Lemma loop_0d8 : forall (q : nat) regs m (s r : Z),
inv m ->
getr regs 11 = Z_to_bv 64 s ->
getr regs 12 = c64w ->
getr regs 13 = Z_to_bv 64 31 ->
getr regs 14 = Z_to_bv 64 r ->
32 * (Z.of_nat q + 1) <= r < 32 * (Z.of_nat q + 2) ->
D <= s -> s + 32 * (Z.of_nat q + 1) <= D + N ->
covP m (fun z => z < s \/ s + 32 * (Z.of_nat q + 1) <= z) ->
fin regs (Z_to_bv 64 (tfib_A_musl_memset + 0xd8)) m.
Proof.
induction q as [|q IH]; intros regs m s r Hinv H11 H12 H13 H14 Hr Hs HsN Hcov; dfacts.
-
eapply fin_steps.
+ norm_pcA.
stepsd F_0d8 D_0d8 s.
stepsd F_0dc D_0dc (s + 8).
stepsd F_0e0 D_0e0 (s + 16).
stepsd F_0e4 D_0e4 (s + 24).
sv F_0e8 D_0e8 (Z_to_bv 64 (r - 32)).
sv F_0ec D_0ec (Z_to_bv 64 (s + 32)).
stepbf F_0f0 D_0f0.
apply fmA_mst_refl.
+ frame.
+ fin_apply ret_0f4.
* inv_tac.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov.
-- cbn beta. intros z Hz _. lia.
- eapply fin_steps.
+ norm_pcA.
stepsd F_0d8 D_0d8 s.
stepsd F_0dc D_0dc (s + 8).
stepsd F_0e0 D_0e0 (s + 16).
stepsd F_0e4 D_0e4 (s + 24).
sv F_0e8 D_0e8 (Z_to_bv 64 (r - 32)).
sv F_0ec D_0ec (Z_to_bv 64 (s + 32)).
stepbt F_0f0 D_0f0.
apply fmA_mst_refl.
+ frame.
+ fin_apply (fun regs m => IH regs m (s + 32) (r - 32)).
* inv_tac.
* gr. reflexivity.
* gr. exact H12.
* gr. exact H13.
* gr. reflexivity.
* lia.
* lia.
* lia.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov.
-- cbn beta. intros z Hz HH. lia.
Qed.
Lemma step_subw_at : forall segs regs pc mm rr w rd rs1 rs2 v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op32 ALU_SUB rd rs1 rs2, 4%Z) ->
bv_eqb rd 0 = false ->
v_subw (getr regs rs1) (getr regs rs2) = v ->
RiscvSemantics.step segs (mkst regs pc mm rr) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mm rr).
Proof.
intros * Hf He Hd Hrd Hv.
rewrite (step_subw segs regs pc mm rr w rd rs1 rs2 Hf He Hd), Hrd, Hv. reflexivity.
Qed.
Lemma step_mulhu_at : forall segs regs pc mm rr w rd rs1 rs2 v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul M_MULHU rd rs1 rs2, 4%Z) ->
bv_eqb rd 0 = false ->
v_mulhu (getr regs rs1) (getr regs rs2) = v ->
RiscvSemantics.step segs (mkst regs pc mm rr) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mm rr).
Proof.
intros * Hf He Hd Hrd Hv.
rewrite (step_mulhu segs regs pc mm rr w rd rs1 rs2 Hf He Hd), Hrd, Hv. reflexivity.
Qed.
Ltac svt F D vv tac := let F' := litF F in stepivA F' D vv tac.
Ltac svat L F0 D vv tac :=
let F := litF F0 in
chain_stepA;
[ reflexivity
| eapply fmA_acc_nil; [ exact F | reflexivity | exact D | reflexivity |
eapply L with (v := vv); [ exact F | reflexivity | exact D | reflexivity | tac ] ]
| apply fmA_accsB_nil
| step_simplA ].
Lemma blk_0c4 : forall regs m (s1 n2 k2 e1 j2 : Z),
inv m ->
getr regs 11 = Z_to_bv 64 s1 ->
getr regs 12 = c32w ->
getr regs 14 = Z_to_bv 64 n2 ->
getr regs 15 = Z_to_bv 64 k2 ->
32 <= n2 -> n2 = 4 * j2 -> 0 <= k2 ->
D <= s1 -> s1 + k2 + n2 = e1 -> e1 <= D + N ->
covP m (fun z => z < s1 + k2 \/ e1 - 28 <= z) ->
fin regs (Z_to_bv 64 (tfib_A_musl_memset + 0xc4)) m.
Proof.
intros regs m s1 n2 k2 e1 j2 Hinv H11 H12 H14 H15 Hn2 Hj2 Hk2 Hs1 He1 He1N Hcov. dfacts.
pose proof c32_range as Hc32.
pose proof (Z.div_mod n2 32 ltac:(lia)) as Hqr. pose proof (Z.mod_pos_bound n2 32 ltac:(lia)) as Hrr.
set (qq := n2 / 32) in *. set (rr := n2 mod 32) in *.
eapply fin_steps.
- norm_pcA.
svt F_0c4 D_0c4 (v_slli c32w 32) ltac:(gr; rwH; reflexivity).
svt F_0c8 D_0c8 (Z_to_bv 64 (s1 + k2)) val.
svt F_0cc D_0cc (v_srli (v_slli c32w 32) 32) ltac:(gr; rwH; reflexivity).
svor F_0d0 D_0d0 c64w. { apply c64_val. }
svt F_0d4 D_0d4 (Z_to_bv 64 31) val.
apply fmA_mst_refl.
- frame.
- fin_apply (fun regs m => loop_0d8 (Z.to_nat (qq - 1)) regs m (s1 + k2) n2).
+ exact Hinv.
+ gr. reflexivity.
+ gr. reflexivity.
+ gr. reflexivity.
+ gr. exact H14.
+ rewrite Z2Nat.id by lia. lia.
+ lia.
+ rewrite Z2Nat.id by lia. lia.
+ rewrite Z2Nat.id by lia. eapply covP_weaken; [exact Hcov|]. cbn beta. intros z Hz HH. lia.
Qed.
Lemma blk_090 : forall regs m (s1 n1 e1 j1 : Z),
inv m ->
getr regs 11 = Z_to_bv 64 s1 ->
getr regs 12 = c32w ->
getr regs 13 = Z_to_bv 64 e1 ->
getr regs 14 = Z_to_bv 64 n1 ->
25 <= n1 -> n1 = 4 * j1 ->
D <= s1 -> s1 + n1 = e1 -> e1 <= D + N ->
covP m (fun z => z < s1 + 12 \/ e1 - 12 <= z) ->
fin regs (Z_to_bv 64 (tfib_A_musl_memset + 0x90)) m.
Proof.
intros regs m s1 n1 e1 j1 Hinv H11 H12 H13 H14 Hn1 Hj1 Hs1 He1 He1N Hcov. dfacts.
destruct (land4_cases s1) as [Ht|Ht].
all: destruct (Z_lt_le_dec (n1 - (24 + Z.land s1 4)) 32) as [Hsmall|Hbig].
-
eapply fin_steps.
+ norm_pcA.
stepsw F_090 D_090 (s1 + 12).
stepsw F_094 D_094 (s1 + 16).
stepsw F_098 D_098 (s1 + 20).
stepsw F_09c D_09c (s1 + 24).
svt F_0a0 D_0a0 (Z_to_bv 64 (Z.land s1 4)) ltac:(gr; rwH; apply and4_val; lia).
svt F_0a4 D_0a4 (Z_to_bv 64 32) val.
svt F_0a8 D_0a8 (Z_to_bv 64 (24 + Z.land s1 4)) val.
svt F_0ac D_0ac (Z_to_bv 64 (n1 - (24 + Z.land s1 4))) val.
stepsw F_0b0 D_0b0 (e1 - 28).
stepsw F_0b4 D_0b4 (e1 - 24).
stepsw F_0b8 D_0b8 (e1 - 20).
stepsw F_0bc D_0bc (e1 - 16).
stepbt F_0c0 D_0c0.
apply fmA_mst_refl.
+ frame.
+ fin_apply ret_0f4.
* inv_tac.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov.
-- cbn beta. intros z Hz _. lia.
-
eapply fin_steps.
+ norm_pcA.
stepsw F_090 D_090 (s1 + 12).
stepsw F_094 D_094 (s1 + 16).
stepsw F_098 D_098 (s1 + 20).
stepsw F_09c D_09c (s1 + 24).
svt F_0a0 D_0a0 (Z_to_bv 64 (Z.land s1 4)) ltac:(gr; rwH; apply and4_val; lia).
svt F_0a4 D_0a4 (Z_to_bv 64 32) val.
svt F_0a8 D_0a8 (Z_to_bv 64 (24 + Z.land s1 4)) val.
svt F_0ac D_0ac (Z_to_bv 64 (n1 - (24 + Z.land s1 4))) val.
stepsw F_0b0 D_0b0 (e1 - 28).
stepsw F_0b4 D_0b4 (e1 - 24).
stepsw F_0b8 D_0b8 (e1 - 20).
stepsw F_0bc D_0bc (e1 - 16).
stepbf F_0c0 D_0c0.
apply fmA_mst_refl.
+ frame.
+ fin_apply (fun regs m => blk_0c4 regs m s1 (n1 - (24 + Z.land s1 4)) (24 + Z.land s1 4) e1 (j1 - 6)).
* inv_tac.
* gr. exact H11.
* gr. exact H12.
* gr. reflexivity.
* gr. reflexivity.
* lia.
* lia.
* lia.
* lia.
* lia.
* lia.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov.
-- cbn beta. intros z Hz HH. lia.
-
eapply fin_steps.
+ norm_pcA.
stepsw F_090 D_090 (s1 + 12).
stepsw F_094 D_094 (s1 + 16).
stepsw F_098 D_098 (s1 + 20).
stepsw F_09c D_09c (s1 + 24).
svt F_0a0 D_0a0 (Z_to_bv 64 (Z.land s1 4)) ltac:(gr; rwH; apply and4_val; lia).
svt F_0a4 D_0a4 (Z_to_bv 64 32) val.
svt F_0a8 D_0a8 (Z_to_bv 64 (24 + Z.land s1 4)) val.
svt F_0ac D_0ac (Z_to_bv 64 (n1 - (24 + Z.land s1 4))) val.
stepsw F_0b0 D_0b0 (e1 - 28).
stepsw F_0b4 D_0b4 (e1 - 24).
stepsw F_0b8 D_0b8 (e1 - 20).
stepsw F_0bc D_0bc (e1 - 16).
stepbt F_0c0 D_0c0.
apply fmA_mst_refl.
+ frame.
+ fin_apply ret_0f4.
* inv_tac.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov.
-- cbn beta. intros z Hz _. lia.
-
eapply fin_steps.
+ norm_pcA.
stepsw F_090 D_090 (s1 + 12).
stepsw F_094 D_094 (s1 + 16).
stepsw F_098 D_098 (s1 + 20).
stepsw F_09c D_09c (s1 + 24).
svt F_0a0 D_0a0 (Z_to_bv 64 (Z.land s1 4)) ltac:(gr; rwH; apply and4_val; lia).
svt F_0a4 D_0a4 (Z_to_bv 64 32) val.
svt F_0a8 D_0a8 (Z_to_bv 64 (24 + Z.land s1 4)) val.
svt F_0ac D_0ac (Z_to_bv 64 (n1 - (24 + Z.land s1 4))) val.
stepsw F_0b0 D_0b0 (e1 - 28).
stepsw F_0b4 D_0b4 (e1 - 24).
stepsw F_0b8 D_0b8 (e1 - 20).
stepsw F_0bc D_0bc (e1 - 16).
stepbf F_0c0 D_0c0.
apply fmA_mst_refl.
+ frame.
+ fin_apply (fun regs m => blk_0c4 regs m s1 (n1 - (24 + Z.land s1 4)) (24 + Z.land s1 4) e1 (j1 - 7)).
* inv_tac.
* gr. exact H11.
* gr. exact H12.
* gr. reflexivity.
* gr. reflexivity.
* lia.
* lia.
* lia.
* lia.
* lia.
* lia.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov.
-- cbn beta. intros z Hz HH. lia.
Qed.
Lemma blk_078 : forall regs m (s1 n1 e1 j1 : Z),
inv m ->
getr regs 11 = Z_to_bv 64 s1 ->
getr regs 12 = c32w ->
getr regs 13 = Z_to_bv 64 e1 ->
getr regs 14 = Z_to_bv 64 n1 ->
9 <= n1 -> n1 = 4 * j1 ->
D <= s1 -> s1 + n1 = e1 -> e1 <= D + N ->
covP m (fun z => z < s1 + 4 \/ e1 - 4 <= z) ->
fin regs (Z_to_bv 64 (tfib_A_musl_memset + 0x78)) m.
Proof.
intros regs m s1 n1 e1 j1 Hinv H11 H12 H13 H14 Hn1 Hj1 Hs1 He1 He1N Hcov. dfacts.
destruct (Z_lt_le_dec n1 25) as [Hsmall|Hbig].
- eapply fin_steps.
+ norm_pcA.
stepsw F_078 D_078 (s1 + 4).
stepsw F_07c D_07c (s1 + 8).
svt F_080 D_080 (Z_to_bv 64 25) val.
stepsw F_084 D_084 (e1 - 12).
stepsw F_088 D_088 (e1 - 8).
stepbt F_08c D_08c.
apply fmA_mst_refl.
+ frame.
+ fin_apply ret_0f4.
* inv_tac.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov.
-- cbn beta. intros z Hz _. lia.
- eapply fin_steps.
+ norm_pcA.
stepsw F_078 D_078 (s1 + 4).
stepsw F_07c D_07c (s1 + 8).
svt F_080 D_080 (Z_to_bv 64 25) val.
stepsw F_084 D_084 (e1 - 12).
stepsw F_088 D_088 (e1 - 8).
stepbf F_08c D_08c.
apply fmA_mst_refl.
+ frame.
+ fin_apply (fun regs m => blk_090 regs m s1 n1 e1 j1).
* inv_tac.
* gr. exact H11.
* gr. exact H12.
* gr. exact H13.
* gr. exact H14.
* lia.
* lia.
* lia.
* lia.
* lia.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov.
-- cbn beta. intros z Hz HH. lia.
Qed.
Lemma blk_040 : forall regs m,
inv m ->
getr regs 10 = Z_to_bv 64 D ->
getr regs 11 = cw ->
getr regs 12 = Z_to_bv 64 N ->
getr regs 15 = Z_to_bv 64 9 ->
9 <= N ->
covP m (fun z => z < D + 4 \/ D + N - 4 <= z) ->
fin regs (Z_to_bv 64 (tfib_A_musl_memset + 0x40)) m.
Proof.
intros regs m Hinv H10 H11 H12 H15 HN9 Hcov. dfacts.
pose proof (Z.mod_pos_bound (- D) 4 ltac:(lia)) as Hk.
set (k := (- D) mod 4) in *.
assert (Hk4 : (D + k) mod 4 = 0).
{ subst k. rewrite Zplus_mod_idemp_r. replace (D + - D) with 0 by lia. reflexivity. }
pose proof (Z.mod_pos_bound (N - k) 4 ltac:(lia)) as Hr1.
pose proof (Z.div_mod (N - k) 4 ltac:(lia)) as Hq1.
set (r1 := (N - k) mod 4) in *. set (j1 := (N - k) / 4) in *.
set (s1 := D + k). set (n1 := N - k - r1). set (e1 := s1 + n1).
destruct (Z_lt_le_dec n1 9) as [Hsmall|Hbig].
- eapply fin_steps.
+ norm_pcA.
svat step_subw_at F_040 D_040 (v_subw (Z_to_bv 64 0) d) ltac:(gr; rwH; rewrite HD_, Z_to_bv_bv_unsigned; reflexivity).
svt F_044 D_044 (Z_to_bv 64 (C * 2^56)) ltac:(gr; rwH; apply slli56_val).
svt F_048 D_048 (Z_to_bv 64 0x10101000) val.
svt F_04c D_04c (Z_to_bv 64 k) ltac:(gr; apply negand3_val).
svt F_050 D_050 (Z_to_bv 64 0x101010000) ltac:(gr; apply bv_eq; vm_compute; reflexivity).
svt F_054 D_054 (Z_to_bv 64 (N - k)) val.
svt F_058 D_058 (Z_to_bv 64 s1) val.
svt F_05c D_05c (Z_to_bv 64 0x101010100) val.
svt F_060 D_060 (Z_to_bv 64 n1) ltac:(gr; rewrite andm4_val by lia; subst n1 r1; reflexivity).
svat step_mulhu_at F_064 D_064 c32w ltac:(gr; apply mulhu_val).
stepsw F_068 D_068 s1.
svt F_06c D_06c (Z_to_bv 64 e1) val.
stepsw F_070 D_070 (e1 - 4).
stepbt F_074 D_074.
apply fmA_mst_refl.
+ frame.
+ fin_apply ret_0f4.
* inv_tac.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov.
-- cbn beta. intros z Hz _. lia.
- eapply fin_steps.
+ norm_pcA.
svat step_subw_at F_040 D_040 (v_subw (Z_to_bv 64 0) d) ltac:(gr; rwH; rewrite HD_, Z_to_bv_bv_unsigned; reflexivity).
svt F_044 D_044 (Z_to_bv 64 (C * 2^56)) ltac:(gr; rwH; apply slli56_val).
svt F_048 D_048 (Z_to_bv 64 0x10101000) val.
svt F_04c D_04c (Z_to_bv 64 k) ltac:(gr; apply negand3_val).
svt F_050 D_050 (Z_to_bv 64 0x101010000) ltac:(gr; apply bv_eq; vm_compute; reflexivity).
svt F_054 D_054 (Z_to_bv 64 (N - k)) val.
svt F_058 D_058 (Z_to_bv 64 s1) val.
svt F_05c D_05c (Z_to_bv 64 0x101010100) val.
svt F_060 D_060 (Z_to_bv 64 n1) ltac:(gr; rewrite andm4_val by lia; subst n1 r1; reflexivity).
svat step_mulhu_at F_064 D_064 c32w ltac:(gr; apply mulhu_val).
stepsw F_068 D_068 s1.
svt F_06c D_06c (Z_to_bv 64 e1) val.
stepsw F_070 D_070 (e1 - 4).
stepbf F_074 D_074.
apply fmA_mst_refl.
+ frame.
+ fin_apply (fun regs m => blk_078 regs m s1 n1 e1 j1).
* inv_tac.
* gr. reflexivity.
* gr. reflexivity.
* gr. reflexivity.
* gr. reflexivity.
* lia.
* lia.
* lia.
* lia.
* lia.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov.
-- cbn beta. intros z Hz HH. lia.
Qed.
Lemma entry_000 : forall regs,
getr regs 10 = Z_to_bv 64 D -> getr regs 11 = cw -> getr regs 12 = Z_to_bv 64 N ->
fin regs (Z_to_bv 64 (tfib_A_musl_memset + 0x0)) mem.
Proof.
intros regs H10 H11 H12. dfacts. pose proof inv_mem as Hinv.
assert (Hcov0 : covP mem (fun z => False)) by (intros x _ HF; destruct HF).
destruct (Z.eq_dec N 0) as [HN0|HN0].
{
eapply fin_steps.
+ norm_pcA. stepbt F_000 D_000. apply fmA_mst_refl.
+ intros; reflexivity.
+ fin_apply ret_0f4; [exact Hinv|]. intros x Hx _. exfalso. lia. }
destruct (Z_lt_le_dec N 3) as [HN3|HN3].
{
eapply fin_steps.
+ norm_pcA. stepbf F_000 D_000.
stepsb F_004 D_004 D.
svt F_008 D_008 (Z_to_bv 64 (D + N)) val.
svt F_00c D_00c (Z_to_bv 64 3) val.
stepsb F_010 D_010 (D + N - 1).
stepbt F_014 D_014. apply fmA_mst_refl.
+ frame.
+ fin_apply ret_0f4.
* inv_tac.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov0.
-- cbn beta. intros z Hz _. lia. }
destruct (Z_lt_le_dec N 7) as [HN7|HN7].
{
eapply fin_steps.
+ norm_pcA. stepbf F_000 D_000.
stepsb F_004 D_004 D.
svt F_008 D_008 (Z_to_bv 64 (D + N)) val.
svt F_00c D_00c (Z_to_bv 64 3) val.
stepsb F_010 D_010 (D + N - 1).
stepbf F_014 D_014.
stepsb F_018 D_018 (D + 1).
stepsb F_01c D_01c (D + 2).
svt F_020 D_020 (Z_to_bv 64 7) val.
stepsb F_024 D_024 (D + N - 3).
stepsb F_028 D_028 (D + N - 2).
stepbt F_02c D_02c. apply fmA_mst_refl.
+ frame.
+ fin_apply ret_0f4.
* inv_tac.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov0.
-- cbn beta. intros z Hz _. lia. }
destruct (Z_lt_le_dec N 9) as [HN9|HN9].
{
eapply fin_steps.
+ norm_pcA. stepbf F_000 D_000.
stepsb F_004 D_004 D.
svt F_008 D_008 (Z_to_bv 64 (D + N)) val.
svt F_00c D_00c (Z_to_bv 64 3) val.
stepsb F_010 D_010 (D + N - 1).
stepbf F_014 D_014.
stepsb F_018 D_018 (D + 1).
stepsb F_01c D_01c (D + 2).
svt F_020 D_020 (Z_to_bv 64 7) val.
stepsb F_024 D_024 (D + N - 3).
stepsb F_028 D_028 (D + N - 2).
stepbf F_02c D_02c.
stepsb F_030 D_030 (D + 3).
svt F_034 D_034 (Z_to_bv 64 9) val.
stepsb F_038 D_038 (D + N - 4).
stepbt F_03c D_03c. apply fmA_mst_refl.
+ frame.
+ fin_apply ret_0f4.
* inv_tac.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov0.
-- cbn beta. intros z Hz _. lia. }
eapply fin_steps.
+ norm_pcA. stepbf F_000 D_000.
stepsb F_004 D_004 D.
svt F_008 D_008 (Z_to_bv 64 (D + N)) val.
svt F_00c D_00c (Z_to_bv 64 3) val.
stepsb F_010 D_010 (D + N - 1).
stepbf F_014 D_014.
stepsb F_018 D_018 (D + 1).
stepsb F_01c D_01c (D + 2).
svt F_020 D_020 (Z_to_bv 64 7) val.
stepsb F_024 D_024 (D + N - 3).
stepsb F_028 D_028 (D + N - 2).
stepbf F_02c D_02c.
stepsb F_030 D_030 (D + 3).
svt F_034 D_034 (Z_to_bv 64 9) val.
stepsb F_038 D_038 (D + N - 4).
stepbf F_03c D_03c. apply fmA_mst_refl.
+ frame.
+ fin_apply blk_040.
* inv_tac.
* gr. exact H10.
* gr. exact H11.
* gr. exact H12.
* gr. reflexivity.
* lia.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov0.
-- cbn beta. intros z Hz HH. lia.
Qed.
Lemma post_wbytes : forall m', post m' -> m' = wbytes mem d (repeat cb n).
Proof.
intros m' [Hin Hout]. dfacts. apply functional_extensionality. intros x.
rewrite wbytes_repeat_spec by lia. rewrite <- HD_, <- HN_.
destruct (_ && _) eqn:E.
- apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. apply Hin. lia.
- apply Hout. intros Hx. apply andb_false_iff in E. destruct E as [E|E]; [apply Z.leb_gt in E|apply Z.ltb_ge in E]; lia.
Qed.
End g.
Theorem tfib_memsetA :
forall (d c nw : word) (n : nat) (mem rom : word -> option byte) (regs : bvmap 5 word),
getr regs 10 = d -> getr regs 11 = c -> getr regs 12 = nw ->
bv_unsigned nw = Z.of_nat n ->
store_ok tfibsegs mem d n = true ->
bv_unsigned d + Z.of_nat n <= 2^64 ->
exists regs',
fmA_mst tfibsegs (bv_unsigned d) (bv_unsigned d + Z.of_nat n) (mkst regs (Z_to_bv 64 tfib_A_musl_memset) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0)
(wbytes mem d (repeat (Z_to_bv 8 (bv_unsigned c mod 256)) n)) rom)
/\ getr regs' 10 = d
/\ (forall r : reg, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv ->
r <> 16%bv -> getr regs' r = getr regs r).
Proof.
intros d c nw n mem rom regs H10 H11 H12 Hn Hdst Hnd.
pose proof (u64_range nw) as Hnw.
assert (H10' : getr regs 10 = Z_to_bv 64 (D d)) by (rewrite H10; unfold D; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (H12' : getr regs 12 = Z_to_bv 64 (N n)) by (rewrite H12; unfold N; rewrite <- Hn, Z_to_bv_bv_unsigned; reflexivity).
destruct (entry_000 d c n mem rom Hdst Hnd ltac:(lia) regs H10' H11 H12') as (regs' & m' & Hms & Hpost & Hfr).
pose proof (post_wbytes d c n mem rom Hnd ltac:(lia) m' Hpost) as Em. subst m'.
exists regs'. split; [|split].
- change (Z_to_bv 64 tfib_A_musl_memset) with (Z_to_bv 64 (tfib_A_musl_memset + 0x0)). exact Hms.
- rewrite Hfr; [exact H10|]. unfold keep. repeat split; reg_neq_tac.
- intros. apply Hfr. unfold keep. repeat split; assumption.
Qed.
End f.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The memset leaf on the M engine: YFfm.memset_stretch_nw's proof, the chain now tfib_memsetA through
   YA0nM.SRr_mstepsM.  YFfm's environment again. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0x YA0nM.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f YG0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0l YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YE3d YFeq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Close Scope bv_scope.
Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem memset_stretch_nwM : forall W, DMrcSecMat.memset_nwM_t W.
Proof.
intros W k E ss ms md d len retpc Q HS Hrv Hpc Hat Hnc H10 H12 H1 Hlen Hd Hdl Hrpc Hrpc' Hpres Hext Hext64 HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H W) (ms_mem ms)).
assert (SOK : store_ok tfibsegs mr (Z_to_bv 64 d) (Z.to_nat len) = true).
{ apply store_ok_of_all; rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); [lia|]. intros x Hx.
pose proof (apresent_writable (w_H W) (ms_mem ms) (bv_unsigned x) ltac:(pose proof (u64_range x); unfold TFIB_IMG_END in *; lia) (Hpres (bv_unsigned x) ltac:(lia))) as Hw.
unfold writable_at in Hw. rewrite Z_to_bv_bv_unsigned in Hw. exact Hw. }
destruct (tfib_memsetA (Z_to_bv 64 d) (getr (ms_regs ms) 11) (Z_to_bv 64 len) (Z.to_nat len) mr (seg_rom tfibsegs) (ms_regs ms)
H10 eq_refl H12 ltac:(rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia) SOK
ltac:(rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia))
as (regs' & Hms & H10' & Hfr).
set (bs := repeat (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256)) (Z.to_nat len)) in Hms.
assert (Hlenbs : Z.of_nat (length bs) = len) by (subst bs; rewrite repeat_length; lia).
destruct (fmA_mst_acc _ _ _ _ _ Hms) as (accs & Hacc & HB).
assert (HB' : forall a nb kb, In (a, nb) accs -> (kb < nb)%nat -> d <= bv_unsigned a + Z.of_nat kb < d + len).
{ intros a nb kb Hin Hk. pose proof (HB a nb kb Hin Hk) as X.
rewrite unsigned_lit_small in X by (unfold TFIB_IMG_END in *; lia). rewrite Z2Nat.id in X by lia. exact X. }
clear HB.
eapply (SRr_mstepsM tfibsegs Hwx W _ _ accs Hacc _ md Q). { rewrite restrict_mkst_fx. reflexivity. }
intros model' Hsame Hcln Hmi. rewrite (same_but_materialized_wvb md model' Hsame).
rewrite H1. replace (v_jalr (Z_to_bv 64 retpc) 0) with (Z_to_bv 64 retpc).
2:{ unfold v_jalr, jalr_tgtZ. rewrite unsigned_lit_small by lia. f_equal. rewrite Z.add_0_r.
change (-2) with (- 2 ^ 1). rewrite land_neg_pow2 by lia. change (2 ^ 1) with 2.
replace (retpc mod 2) with 0; [lia|]. symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4); [exists 2; reflexivity|].
apply Znumtheory.Zmod_divide; [lia | exact Hrpc]. }
change (unrestrict (w_H W) (ms_mem ms) (mkst regs' (Z_to_bv 64 retpc) (wbytes mr (Z_to_bv 64 d) bs) (seg_rom tfibsegs)))
with (mkst regs' (Z_to_bv 64 retpc) (munrestrict (w_H W) (ms_mem ms) (wbytes mr (Z_to_bv 64 d) bs)) (seg_rom tfibsegs)).
set (m1 := wbytes mr (Z_to_bv 64 d) bs) in *. set (m1full := munrestrict (w_H W) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H W) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H W) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. exact Em. }
assert (FR1 : forall x : word, ~ (d <= bv_unsigned x < d + len) -> m1 x = mr x).
{ intros x Hx. subst m1. destruct (Z_lt_le_dec (bv_unsigned x) d).
- apply wbytes_below; rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia.
- apply wbytes_above; rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia. }
assert (GR1 : mem_grows mr m1) by (subst m1; apply wbytes_grows).
apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
apply (st_ok_after_stretch tfibsegs k E ss (restrict (w_H W) ms) regs' m1 (ss_mem ss) retpc [11; 12; 13; 14; 15; 16]%bv HS Hrv);
[ unfold ss_atoms_lt; rewrite Hr', Hm', HG, Hrv'; reflexivity
| exact (proj1 (st_ok_mem_ok tfibsegs E ss _ HS)) | exact Hnc | exact Hm' | apply submem_refl | reflexivity | reflexivity | | ].
+ intros r Hr. cbn [ms_regs restrict]. apply reg_in_false in Hr. cbn [In] in Hr.
destruct (base.decide (r = 10%bv)) as [->|N10]; [rewrite H10', H10; reflexivity|].
apply Hfr; intros ->; apply Hr; tauto.
+ apply Forall_forall. intros r Hr. cbn [ms_mem restrict]. fold mr. split.
* intros a Ha. unfold mbyte. rewrite (FR1 (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by (exact (Hext64 r a Hr Ha)). destruct (Hext r Hr) as [X|[X|X]]; lia.
* intros a Ha Hw. apply (writable_at_grows tfibsegs mr m1 a GR1 Hw).
- exact H10'.
- intros x Hx. subst m1full. unfold munrestrict. destruct (w_H W x) eqn:Hh; [reflexivity|].
rewrite (FR1 x Hx). subst mr. unfold mrestrict. rewrite Hh. reflexivity.
- intros a [Hh [b Hb]]. split; [exact Hh|]. subst m1full. unfold munrestrict. rewrite Hh.
assert (NN : m1 (Z_to_bv 64 a) <> None) by (apply GR1; subst mr; unfold mrestrict; rewrite Hh, Hb; discriminate).
destruct (m1 (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply NN; reflexivity].
- intros x Hx. destruct (Hpres (bv_unsigned x) Hx) as [Hh _]. rewrite Z_to_bv_bv_unsigned in Hh.
subst m1full. unfold munrestrict. rewrite Hh. subst m1 bs. rewrite wbytes_repeat_spec by (rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia).
rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia).
replace ((d <=? bv_unsigned x) && (bv_unsigned x <? d + Z.of_nat (Z.to_nat len))) with true; [reflexivity|].
symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- intros p Hp. destruct (Hmi p Hp) as [Hp0 | (a & nb & kb & Hin & Hk & ->)]; [left; exact Hp0 | right].
exists (bv_unsigned a + Z.of_nat kb). split; [exact (HB' a nb kb Hin Hk) | reflexivity].
Qed.
End c.
