(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0g.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition LOCK : Z := src0_D_malloc_lock.
Definition CTX : Z := src0_D_malloc_context.
Definition NLK : Z := src0_D_libc + 3.
Definition TP : Z := src0_tp.
Definition ERRNO : Z := src0_tp - 164.
Definition RA_AM : Z := src0_A_libc_malloc_impl + 0x18c.
Definition E_mi (regs : bvmap 5 word) (seq ctr : Z) (useq : list byte) (a g : word) (xr : nat -> word) : env :=
mkEnv (fun n => match n with
| 0%nat => Z_to_bv 64 0
| 1%nat => getr regs 1%bv
| 2%nat => getr regs 2%bv
| 3%nat => getr regs 3%bv
| 4%nat => getr regs 4%bv
| 5%nat => getr regs 5%bv
| 6%nat => getr regs 6%bv
| 7%nat => getr regs 7%bv
| 8%nat => getr regs 8%bv
| 9%nat => getr regs 9%bv
| 10%nat => getr regs 10%bv
| 11%nat => getr regs 11%bv
| 12%nat => getr regs 12%bv
| 13%nat => getr regs 13%bv
| 14%nat => getr regs 14%bv
| 15%nat => getr regs 15%bv
| 16%nat => getr regs 16%bv
| 17%nat => getr regs 17%bv
| 18%nat => getr regs 18%bv
| 19%nat => getr regs 19%bv
| 20%nat => getr regs 20%bv
| 21%nat => getr regs 21%bv
| 22%nat => getr regs 22%bv
| 23%nat => getr regs 23%bv
| 24%nat => getr regs 24%bv
| 25%nat => getr regs 25%bv
| 26%nat => getr regs 26%bv
| 27%nat => getr regs 27%bv
| 28%nat => getr regs 28%bv
| 29%nat => getr regs 29%bv
| 30%nat => getr regs 30%bv
| 31%nat => getr regs 31%bv
| 32%nat => Z_to_bv 64 seq
| 33%nat => Z_to_bv 64 ctr
| 34%nat => a
| 35%nat => g
| n => xr n
end)
(fun d => match d with 0%nat => useq | _ => [] end).
Definition regs_mi : list sv :=
SLit 0 :: SOff 1 0 :: SOff 2 0 :: SOff 3 0 :: SLit TP
:: map (fun r => SOff r 0) (seq 5 27).
Definition R_stack : region := mkRegion (Some 2%nat) (-8192) 0 (-8192) 0 [].
Definition R_lock : region := mkRegion None LOCK (LOCK + 4) 0 0 [mkChunk LOCK (CVal 4 (SLit 0))].
Definition R_nl : region := mkRegion None NLK (NLK + 1) 0 0 [mkChunk NLK (CVal 1 (SLit 0))].
Definition R_errno : region := mkRegion None ERRNO (ERRNO + 4) ERRNO (ERRNO + 4) [].
Definition R_ctr (w : bool) : region :=
mkRegion None (CTX + 12) (CTX + 16) (if w then CTX + 12 else 0) (if w then CTX + 16 else 0)
[mkChunk (CTX + 12) (CVal 4 (SOff 33 0))].
Definition R_useq (w : bool) : region :=
mkRegion None (CTX + 848) (CTX + 880) (if w then CTX + 848 else 0) (if w then CTX + 880 else 0)
[mkChunk (CTX + 848) (CData 0 0 32)].
Definition R_seq (w : bool) : region :=
mkRegion None (CTX + 912) (CTX + 913) (if w then CTX + 912 else 0) (if w then CTX + 913 else 0)
[mkChunk (CTX + 912) (CVal 1 (SOff 32 0))].
Definition R_map : region := mkRegion (Some 34%nat) 0 8 0 8 [mkChunk 0 (CZero 8)].
Definition R_meta : region := mkRegion (Some 35%nat) 16 40 16 40 [].
Definition mem_mi (w : bool) : smem := [R_stack; R_lock; R_nl; R_ctr w; R_useq w; R_seq w; R_errno].
Definition F_sp : afact := mkAF (CEIL_MIN + 8192) (2 ^ 63 - 1) 4.
Definition F_n : afact := mkAF 0 (2 ^ 62 - 1) 0.
Definition F_seq : afact := mkAF 0 255 0.
Definition F_ctr : afact := mkAF 0 (2 ^ 32 - 1) 0.
Definition F_map : afact := mkAF 4096 (CEIL_MAX - 131072) 12.
Definition F_meta : afact := mkAF 4096 (CEIL_MAX - 40) 3.
Definition facts_mi : facts :=
mkFacts [ (2%nat, F_sp); (10%nat, F_n); (32%nat, F_seq); (33%nat, F_ctr) ] [] [].
Definition ss_mi : sstate := mkSS src0_A_malloc regs_mi (mem_mi false) None facts_mi.
Definition run_ (ss : sstate) : sstate := fst (sym_runN src0segs src0tbl FUEL ss).
Definition runto_ (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN src0segs src0tbl FUEL pc ss).
Definition C_direct : acond := mkAC BC_GEU (SOff 10 0) (SLit 131052).
Definition C_small : acond := mkAC BC_LTU (SOff 10 0) (SLit 131052).
Definition C_mapok : acond := mkAC BC_NE (SAlu ALU_OR (SLit 0) (SAlu ALU_XOR (SOff 34 0) (SLit (-1)))) (SLit 0).
Definition C_seq255 : acond := mkAC BC_EQ (SOff 32 0) (SLit 255).
Definition C_seqne : acond := mkAC BC_NE (SOff 32 0) (SLit 255).
Definition ss_thr : sstate := Eval vm_compute in run_ ss_mi.
Definition ss_mmap : sstate := Eval vm_compute in run_ (add_cond ss_thr C_direct).
Definition facts_g : facts :=
mkFacts [ (34%nat, F_map); (2%nat, F_sp); (10%nat, F_n); (32%nat, F_seq); (33%nat, F_ctr) ] [C_direct] [].
Definition stack_of (ss : sstate) : region := nth 0 (ss_mem ss) R_stack.
Definition mem_g (stk : region) : smem := [R_map; stk; R_lock; R_nl; R_ctr true; R_useq true; R_seq true; R_errno].
Definition ss_granted : sstate :=
mkSS (ss_pc ss_mmap + 4) (sr_set (ss_regs ss_mmap) 10 (SOff 34 0)) (mem_g (stack_of ss_mmap)) None facts_g.
Definition ss_refused : sstate :=
mkSS (ss_pc ss_mmap + 4) (sr_set (ss_regs ss_mmap) 10 (SLit (2 ^ 64 - 12))) (ss_mem ss_mmap) None (ss_facts ss_mmap).
Definition ss_g1 : sstate := Eval vm_compute in run_ ss_granted.
Definition ss_seq : sstate := Eval vm_compute in run_ (add_cond ss_g1 C_mapok).
Definition ss_am255 : sstate := Eval vm_compute in runto_ src0_A_alloc_meta (add_cond ss_seq C_seq255).
Definition ss_amne : sstate := Eval vm_compute in runto_ src0_A_alloc_meta (add_cond ss_seq C_seqne).
Definition ss_ref_end : sstate := Eval vm_compute in run_ ss_refused.
Definition regs_ret (rv : sv) : list sv :=
[SLit 0; SOff 36 0; SOff 2 (-48); SOff 3 0; SLit TP; SOff 37 0; SOff 38 0; SOff 39 0;
SOff 10 0; SLit LOCK; rv; SOff 40 0; SOff 41 0; SOff 42 0; SOff 43 0; SOff 44 0; SOff 45 0; SOff 46 0;
SLit (2 ^ 64 - 1); SOff 10 20; SOff 34 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0;
SOff 26 0; SOff 27 0; SOff 47 0; SOff 48 0; SOff 49 0; SOff 50 0].
Definition R_stack_ret : region :=
mkRegion (Some 2%nat) (-8192) 0 (-8192) 0
[mkChunk (-48) (CVal 8 (SOff 20 0)); mkChunk (-40) (CVal 8 (SOff 19 0)); mkChunk (-32) (CVal 8 (SOff 18 0));
mkChunk (-24) (CVal 8 (SOff 9 0)); mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition mem_ret0 : smem := [R_stack_ret; R_lock; R_nl; R_errno].
Definition mem_ret1 : smem := [R_map; R_meta; R_stack_ret; R_lock; R_nl; R_ctr true; R_errno].
Definition facts_ret0 : facts := mkFacts [ (34%nat, F_map); (2%nat, F_sp); (10%nat, F_n) ] [C_direct] [].
Definition facts_ret1 : facts :=
mkFacts [ (35%nat, F_meta); (34%nat, F_map); (2%nat, F_sp); (10%nat, F_n); (33%nat, F_ctr) ] [C_direct] [].
Definition ss_ret0 : sstate := mkSS RA_AM (regs_ret (SLit 0)) mem_ret0 None facts_ret0.
Definition ss_ret1 : sstate := mkSS RA_AM (regs_ret (SOff 35 0)) mem_ret1 None facts_ret1.
Definition ss_mun : sstate := Eval vm_compute in run_ ss_ret0.
Definition ss_mun2 : sstate :=
mkSS (ss_pc ss_mun + 4) (sr_set (ss_regs ss_mun) 10 (SLit 0)) (ss_mem ss_mun) None (ss_facts ss_mun).
Definition ss_none_end : sstate := Eval vm_compute in run_ ss_mun2.
Definition ss_enf : sstate := Eval vm_compute in runto_ src0_A_enframe ss_ret1.
Section f.
Variable segs : list Segment.
Lemma chunk_ok_cval : forall E m base off (w : nat) v (val : Z),
sv_denot E v = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 ->
(forall k, (k < w)%nat -> mbyte segs m (base + off + Z.of_nat k) = Some (Z_to_bv 8 (le_byte val w k))) ->
chunk_ok segs E m base (mkChunk off (CVal (N.of_nat w) v)).
Proof.
intros E m base off w v val Hv Hval H i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
rewrite nat_N_Z in Hi.
exists (byte_of_word (sv_denot E v) i). split; [reflexivity|].
replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite H by lia.
f_equal. rewrite le_byte_bv by lia. unfold byte_of_word. rewrite Hv, u64_of_Z by lia.
rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma chunk_ok_czero : forall E m base off len,
(forall i, 0 <= i < len -> mbyte segs m (base + off + i) = Some (Z_to_bv 8 0)) ->
chunk_ok segs E m base (mkChunk off (CZero len)).
Proof.
intros E m base off len H i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
exists (Z_to_bv 8 0). split; [reflexivity|]. apply H. exact Hi.
Qed.
Lemma chunk_ok_cdata : forall E m base off d len,
Z.of_nat (length (ed E d)) = len ->
(forall k, (k < length (ed E d))%nat -> mbyte segs m (base + off + Z.of_nat k) = nth_error (ed E d) k) ->
chunk_ok segs E m base (mkChunk off (CData d 0 len)).
Proof.
intros E m base off d len Hlen H i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
rewrite Z.add_0_l.
destruct (nth_error (ed E d) (Z.to_nat i)) as [b|] eqn:Eb.
- exists b. split; [reflexivity|]. replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite H by lia. exact Eb.
- apply nth_error_None in Eb. lia.
Qed.
Lemma region_ok_intro : forall E m r,
0 <= base_val E (r_base r) + r_lo r -> base_val E (r_base r) + r_hi r <= 2 ^ 64 ->
(forall o, r_wlo r <= o < r_whi r -> writable_at segs m (base_val E (r_base r) + o)) ->
Forall (chunk_ok segs E m (base_val E (r_base r))) (r_chunks r) ->
region_ok segs E m r.
Proof. intros E m r H1 H2 H3 H4. unfold region_ok. auto. Qed.
Lemma mem_ok_intro : forall E m rs,
regions_wf rs = true -> Forall (region_ok segs E m) rs -> pairwise_disjoint E rs -> mem_ok segs E m rs.
Proof. intros. split; [assumption | split; assumption]. Qed.
Lemma region_ok_transport : forall E m m' r,
region_ok segs E m r -> region_wf r = true ->
(forall x, base_val E (r_base r) + r_lo r <= x < base_val E (r_base r) + r_hi r -> mbyte segs m' x = mbyte segs m x) ->
(forall x, base_val E (r_base r) + r_wlo r <= x < base_val E (r_base r) + r_whi r -> writable_at segs m x -> writable_at segs m' x) ->
region_ok segs E m' r.
Proof.
intros E m m' r (H1 & H2 & H3 & H4) Hwf Hrd Hwr.
apply region_wf_facts in Hwf as (_ & _ & Hci).
split; [exact H1|]. split; [exact H2|]. split.
- intros o Ho. apply Hwr; [lia|]. apply H3. exact Ho.
- rewrite Forall_forall in H4 |- *. intros c Hc i Hi.
destruct (H4 c Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
pose proof (chunk_inside_facts r c (proj1 (forallb_forall _ _) Hci c Hc)) as (Hc1 & Hc2 & Hc3).
rewrite Hrd by lia. exact Hb2.
Qed.
Lemma le_byte_0 : forall w k, le_byte 0 w k = 0.
Proof. intros w k. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. Qed.
End f.
Section h.
Variables (regs : bvmap 5 word) (mem : word -> option byte).
Variables (seq ctr : Z) (useq : list byte) (a g : word) (xr : nat -> word).
Let E := E_mi regs seq ctr useq a g xr.
Let sp := bv_unsigned (getr regs 2).
Hypothesis Hsp : alloc_ceiling + 8192 <= sp /\ sp < 2 ^ 63 /\ sp mod 16 = 0.
Hypothesis Hstk : forall x, sp - 8192 <= x < sp -> writable_at src0segs mem x.
Hypothesis Htp : getr regs 4 = Z_to_bv 64 TP.
Hypothesis Hn : bv_unsigned (getr regs 10) < 2 ^ 62.
Hypothesis Hlock : forall k, (k < 4)%nat -> mbyte src0segs mem (LOCK + Z.of_nat k) = Some (Z_to_bv 8 0).
Hypothesis Hnl : mbyte src0segs mem NLK = Some (Z_to_bv 8 0).
Hypothesis Hctr : forall k, (k < 4)%nat -> mbyte src0segs mem (CTX + 12 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte ctr 4 k)).
Hypothesis Hctr_range : 0 <= ctr < 2 ^ 32.
Hypothesis Huseq_len : length useq = 32%nat.
Hypothesis Huseq : forall k, (k < 32)%nat -> mbyte src0segs mem (CTX + 848 + Z.of_nat k) = nth_error useq k.
Hypothesis Hseq : mbyte src0segs mem (CTX + 912) = Some (Z_to_bv 8 (le_byte seq 1 0)).
Hypothesis Hseq_range : 0 <= seq < 256.
Hypothesis Herr : forall x, ERRNO <= x < ERRNO + 4 -> writable_at src0segs mem x.
Lemma regs_ok_entry : regs_ok E regs_mi regs.
Proof.
subst E. regs_ok_cases; first [ exact Htp | symmetry; exact Htp | apply getr_zero | symmetry; apply getr_zero ].
Qed.
Lemma facts_ok_entry : facts_ok E facts_mi.
Proof.
pose proof (proj1 alloc_ceiling_val) as ACV_p9.
subst E sp. pose proof (u64_range (getr regs 10)).
unfold facts_mi, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
unfold afact_ok, F_sp, F_n, F_seq, F_ctr; cbn [af_lo af_hi af_al2 ew E_mi].
rewrite !u64_of_Z by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. change (2 ^ 4) with 16.
repeat split; lia.
Qed.
Lemma mem_ok_entry : mem_ok src0segs E mem (mem_mi false).
Proof.
subst E sp. pose proof (proj1 alloc_ceiling_val) as AC.
apply mem_ok_intro.
- vm_compute. reflexivity.
- unfold mem_mi. repeat apply Forall_cons; try apply Forall_nil;
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val ew E_mi R_stack R_lock R_nl R_ctr R_useq R_seq R_errno];
unfold LOCK, NLK, CTX, ERRNO, TP, src0_D_malloc_lock, src0_D_malloc_context, src0_D_libc, src0_tp in *; try lia.
+ intros o Ho. apply Hstk. lia.
+ constructor.
+ apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_cval src0segs _ mem 0 _ 4 (SLit 0) 0); [reflexivity | lia |].
intros k Hk. rewrite le_byte_0. rewrite Z.add_0_l. apply Hlock. exact Hk.
+ apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_cval src0segs _ mem 0 _ 1 (SLit 0) 0); [reflexivity | lia |].
intros k Hk. rewrite le_byte_0. destruct k; [|lia]. rewrite Z.add_0_l, Z.add_0_r. exact Hnl.
+ apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_cval src0segs _ mem 0 _ 4 (SOff 33 0) ctr); [| lia |].
* cbn [sv_denot ew E_mi]. rewrite u64_of_Z by lia. rewrite Z.add_0_r. reflexivity.
* intros k Hk. rewrite Z.add_0_l. apply Hctr. exact Hk.
+ apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_cdata; cbn [ed E_mi]; [rewrite Huseq_len; reflexivity|].
intros k Hk. rewrite Z.add_0_l. apply Huseq. rewrite Huseq_len in Hk. exact Hk.
+ apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_cval src0segs _ mem 0 _ 1 (SOff 32 0) seq); [| lia |].
* cbn [sv_denot ew E_mi]. rewrite u64_of_Z by lia. rewrite Z.add_0_r. reflexivity.
* intros k Hk. destruct k; [|lia]. rewrite Z.add_0_l, Z.add_0_r. exact Hseq.
+ intros o Ho. rewrite Z.add_0_l. apply Herr. lia.
+ constructor.
- cbn [pairwise_disjoint all_disjoint mem_mi extent_disjoint base_val r_base r_lo r_hi ew E_mi R_stack R_lock R_nl R_ctr R_useq R_seq R_errno].
unfold LOCK, NLK, CTX, ERRNO, TP, src0_D_malloc_lock, src0_D_malloc_context, src0_D_libc, src0_tp in *.
repeat split; unfold extent_disjoint; cbn [base_val r_base r_lo r_hi ew E_mi R_stack R_lock R_nl R_ctr R_useq R_seq R_errno];
unfold LOCK, NLK, CTX, ERRNO, TP, src0_D_malloc_lock, src0_D_malloc_context, src0_D_libc, src0_tp; lia.
Qed.
Theorem st_ok_entry :
st_ok src0segs E ss_mi (mkst regs (Z_to_bv 64 src0_A_malloc) mem (seg_rom src0segs)).
Proof.
unfold st_ok, ss_mi, mkst; cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]).
split; [apply regs_ok_entry|]. split; [apply mem_ok_entry | apply facts_ok_entry].
Qed.
End h.
Lemma E_mi_agree_34 : forall regs seq ctr useq a0 g0 xr0 a g xr,
env_agree 34 (E_mi regs seq ctr useq a0 g0 xr0) (E_mi regs seq ctr useq a g xr).
Proof.
intros. split; [|reflexivity]. intros i Hi. cbn [ew E_mi].
do 34 (destruct i as [|i]; [reflexivity|]). lia.
Qed.
Lemma E_mi_agree_35 : forall regs seq ctr useq a g0 xr0 g xr,
env_agree 35 (E_mi regs seq ctr useq a g0 xr0) (E_mi regs seq ctr useq a g xr).
Proof.
intros. split; [|reflexivity]. intros i Hi. cbn [ew E_mi].
do 35 (destruct i as [|i]; [reflexivity|]). lia.
Qed.
Section j.
Variables (regs : bvmap 5 word) (seq ctr : Z) (useq : list byte) (a0 g0 : word) (xr0 : nat -> word).
Let E := E_mi regs seq ctr useq a0 g0 xr0.
Lemma st_ok_refused : forall regs1 mem1,
regs_ok E (ss_regs ss_mmap) regs1 -> mem_ok src0segs E mem1 (ss_mem ss_mmap) -> facts_ok E (ss_facts ss_mmap) ->
st_ok src0segs E ss_refused
(mkst (regupd regs1 10 (Z_to_bv 64 (2 ^ 64 - 12))) (v_addi (Z_to_bv 64 (ss_pc ss_mmap)) 4) mem1 (seg_rom src0segs)).
Proof.
intros regs1 mem1 HR HM HG.
change ss_refused with (resume ss_mmap (SLit (2 ^ 64 - 12)) (ss_mem ss_mmap) (ss_facts ss_mmap)).
apply st_ok_resume_sv; [exact HR | exact HM | exact HG | reflexivity].
Qed.
Lemma region_ok_rw : forall (E1 : env) m lo hi cs,
region_ok src0segs E1 m (mkRegion None lo hi 0 0 cs) ->
(forall x, lo <= x < hi -> writable_at src0segs m x) -> lo <= hi ->
region_ok src0segs E1 m (mkRegion None lo hi lo hi cs).
Proof.
intros E1 m lo hi cs H Hw Hle. unfold region_ok in *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in *.
destruct H as (H1 & H2 & H3 & H4).
split; [exact H1|]. split; [exact H2|]. split; [|exact H4]. intros o Ho. rewrite Z.add_0_l. apply Hw. exact Ho.
Qed.
Lemma ss_mmap_mem : ss_mem ss_mmap = stack_of ss_mmap :: tl (mem_mi false).
Proof. vm_compute. reflexivity. Qed.
Lemma apply_zeros1_mbyte_out : forall m (za zn : word) x,
0 <= x < 2 ^ 64 -> (x < bv_unsigned za \/ bv_unsigned za + bv_unsigned zn <= x) ->
mbyte src0segs (apply_zeros m [(za, zn)]) x = mbyte src0segs m x.
Proof.
intros m za zn x Hx Hout. unfold mbyte. rewrite apply_zeros1_out; [reflexivity|]. rewrite u64_of_Z by lia. exact Hout.
Qed.
Lemma apply_zeros1_writable : forall m zs x, writable_at src0segs m x -> writable_at src0segs (apply_zeros m zs) x.
Proof.
intros m zs x H. unfold writable_at, wview in *. destruct zs as [|z zs]; [exact H|].
cbn [apply_zeros]. destruct (zeros_cover (z :: zs) (Z_to_bv 64 x)); [discriminate | exact H].
Qed.
Lemma st_ok_granted : forall regs1 mem1 (a : word) (len : Z),
regs_ok E (ss_regs ss_mmap) regs1 -> mem_ok src0segs E mem1 (ss_mem ss_mmap) -> facts_ok E (ss_facts ss_mmap) ->
alloc_ceiling + 8192 <= bv_unsigned (getr regs 2) ->
4096 <= bv_unsigned a -> bv_unsigned a + len <= alloc_ceiling -> bv_unsigned a mod 4096 = 0 ->
131072 <= len ->
(bv_unsigned a + len <= 0x1f000 \/ 0x51000 <= bv_unsigned a) ->
(forall x, CTX <= x < CTX + 928 -> writable_at src0segs (apply_zeros mem1 [(a, Z_to_bv 64 len)]) x) ->
st_ok src0segs (E_mi regs seq ctr useq a g0 xr0) ss_granted
(mkst (regupd regs1 10 a) (v_addi (Z_to_bv 64 (ss_pc ss_mmap)) 4)
(apply_zeros mem1 [(a, Z_to_bv 64 len)]) (seg_rom src0segs)).
Proof.
intros regs1 mem1 a len HR HM HG Hsp Ha1 Ha2 Ha3 Hlen Himg Hctxw.
pose proof (proj1 alloc_ceiling_val) as AC.
set (E' := E_mi regs seq ctr useq a g0 xr0).
assert (HA : env_agree 34 E E') by (subst E E'; apply E_mi_agree_34).
assert (Elen : bv_unsigned (Z_to_bv 64 len) = len) by (apply u64_of_Z; lia).
rewrite ss_mmap_mem in HM.
change ss_granted with (resume ss_mmap (SOff 34 0) (mem_g (stack_of ss_mmap)) facts_g).
eapply (st_ok_resume_mem src0segs 34 E E'); [exact HR | exact HA | vm_compute; reflexivity | | |].
- cbn [sv_denot ew E' E_mi]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
-
destruct HM as (Hwf & Hok & Hpd).
assert (Hstk : r_base (stack_of ss_mmap) = Some 2%nat /\ r_lo (stack_of ss_mmap) = -8192 /\ r_hi (stack_of ss_mmap) = 0)
by (vm_compute; repeat split; reflexivity).
destruct Hstk as (S1 & S2 & S3).
assert (OUT : forall r, In r (stack_of ss_mmap :: tl (mem_mi false)) ->
forall x, base_val E (r_base r) + r_lo r <= x < base_val E (r_base r) + r_hi r ->
x < bv_unsigned a \/ bv_unsigned a + bv_unsigned (Z_to_bv 64 len) <= x).
{ intros r Hr x Hx. rewrite Elen. cbn [tl mem_mi In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
[ rewrite S1, S2, S3 in Hx | ..]; cbn [base_val ew E_mi r_base r_lo r_hi R_lock R_nl R_ctr R_useq R_seq R_errno] in Hx;
unfold LOCK, NLK, CTX, ERRNO, TP, src0_D_malloc_lock, src0_D_malloc_context, src0_D_libc, src0_tp in Hx; subst E; cbn [ew E_mi] in Hx; lia. }
assert (TR : forall r, In r (stack_of ss_mmap :: tl (mem_mi false)) ->
region_ok src0segs E' (apply_zeros mem1 [(a, Z_to_bv 64 len)]) r).
{ intros r Hr. apply (region_ok_agree src0segs 34 E E'); [exact HA| |].
- assert (Hat : forallb (region_atoms_lt 34) (stack_of ss_mmap :: tl (mem_mi false)) = true) by (vm_compute; reflexivity).
exact (proj1 (forallb_forall _ _) Hat r Hr).
- eapply region_ok_transport; [apply (proj1 (Forall_forall _ _) Hok r Hr) | apply (regions_wf_In _ r Hwf Hr) | |].
+ intros x Hx. pose proof (proj1 (Forall_forall _ _) Hok r Hr) as (B1 & B2 & _).
apply apply_zeros1_mbyte_out; [lia|]. apply (OUT r Hr x Hx).
+ intros x _ Hw. apply apply_zeros1_writable. exact Hw. }
apply mem_ok_intro.
+ vm_compute. reflexivity.
+ unfold mem_g. apply Forall_cons.
{
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val ew E' E_mi R_map]; try lia.
- intros o Ho. apply present_writable. exists (Z_to_bv 8 0). apply apply_zeros1_in. rewrite u64_of_Z, Elen by lia. lia.
- apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_czero. intros i Hi. unfold mbyte.
rewrite apply_zeros1_in; [reflexivity|]. rewrite u64_of_Z, Elen by lia. lia. }
apply Forall_cons; [apply TR; left; reflexivity|].
apply Forall_cons; [apply TR; right; cbn; tauto|].
apply Forall_cons; [apply TR; right; cbn; tauto|].
assert (W : forall lo hi cs, In (mkRegion None lo hi 0 0 cs) (tl (mem_mi false)) -> CTX <= lo -> hi <= CTX + 928 -> lo <= hi ->
region_ok src0segs E' (apply_zeros mem1 [(a, Z_to_bv 64 len)]) (mkRegion None lo hi lo hi cs)).
{ intros lo hi cs Hin H1 H2 H3. apply region_ok_rw; [apply TR; right; exact Hin | intros x Hx; apply Hctxw; lia | exact H3]. }
apply Forall_cons; [apply W; [cbn; tauto | unfold CTX; lia ..] |].
apply Forall_cons; [apply W; [cbn; tauto | unfold CTX; lia ..] |].
apply Forall_cons; [apply W; [cbn; tauto | unfold CTX; lia ..] |].
apply Forall_cons; [apply TR; right; cbn; tauto | apply Forall_nil].
+
cbn [pairwise_disjoint all_disjoint mem_g]. unfold extent_disjoint. rewrite !S1, !S2, !S3.
cbn [base_val r_base r_lo r_hi ew E' E_mi R_map R_lock R_nl R_ctr R_useq R_seq R_errno].
unfold LOCK, NLK, CTX, ERRNO, TP, src0_D_malloc_lock, src0_D_malloc_context, src0_D_libc, src0_tp.
repeat split; lia.
-
destruct HG as (HGa & HGc & _).
assert (Hat : facts_atoms_lt 34 (ss_facts ss_mmap) = true) by (vm_compute; reflexivity).
pose proof (facts_ok_agree 34 E E' (ss_facts ss_mmap) HA Hat (conj HGa (conj HGc I))) as HG'.
split; [| split; [| exact I]].
+ cbn [f_atoms facts_g atoms_ok]. split.
* unfold afact_ok, F_map; cbn [af_lo af_hi af_al2 ew E' E_mi]. change (2 ^ 12) with 4096. lia.
* destruct HG' as (X & _ & _). exact X.
+ cbn [f_conds facts_g conds_ok]. destruct HG' as (_ & X & _). exact X.
Qed.
End j.
Definition word_at (segs : list Segment) (m : word -> option byte) (addr : Z) (w : word) : Prop :=
forall k, (k < 8)%nat -> mbyte segs m (addr + Z.of_nat k) = Some (byte_of_word w (Z.of_nat k)).
Lemma chunk_ok_word_at : forall segs E m base off v w,
sv_denot E v = w -> word_at segs m (base + off) w -> chunk_ok segs E m base (mkChunk off (CVal 8 v)).
Proof.
intros segs E m base off v w Hv Hw i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
exists (byte_of_word (sv_denot E v) i). split; [reflexivity|]. rewrite Hv.
replace i with (Z.of_nat (Z.to_nat i)) by lia. apply Hw. lia.
Qed.
Lemma word_at_of_chunk : forall segs E m base off v,
chunk_ok segs E m base (mkChunk off (CVal 8 v)) -> word_at segs m (base + off) (sv_denot E v).
Proof.
intros segs E m base off v H k Hk. destruct (H (Z.of_nat k) ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [c_off c_val cbyte] in Hb1, Hb2. injection Hb1 as <-. exact Hb2.
Qed.
Section l.
Variables (regs : bvmap 5 word) (seq ctr : Z) (useq : list byte) (a g : word) (xr : nat -> word).
Let E := E_mi regs seq ctr useq a g xr.
Let sp := bv_unsigned (getr regs 2).
Let n := bv_unsigned (getr regs 10).
Variables (regs4 : bvmap 5 word) (mem4 : word -> option byte).
Hypothesis Hxr : xr 36%nat = getr regs4 1 /\ xr 37%nat = getr regs4 5 /\ xr 38%nat = getr regs4 6 /\ xr 39%nat = getr regs4 7 /\
xr 40%nat = getr regs4 11 /\ xr 41%nat = getr regs4 12 /\ xr 42%nat = getr regs4 13 /\ xr 43%nat = getr regs4 14 /\
xr 44%nat = getr regs4 15 /\ xr 45%nat = getr regs4 16 /\ xr 46%nat = getr regs4 17 /\
xr 47%nat = getr regs4 28 /\ xr 48%nat = getr regs4 29 /\ xr 49%nat = getr regs4 30 /\ xr 50%nat = getr regs4 31.
Hypothesis H2 : getr regs4 2 = Z_to_bv 64 (sp - 48).
Hypothesis H3 : getr regs4 3 = getr regs 3.
Hypothesis H4 : getr regs4 4 = Z_to_bv 64 TP.
Hypothesis H8 : getr regs4 8 = getr regs 10.
Hypothesis H9 : getr regs4 9 = Z_to_bv 64 LOCK.
Hypothesis H18 : getr regs4 18 = Z_to_bv 64 (2 ^ 64 - 1).
Hypothesis H19 : getr regs4 19 = Z_to_bv 64 (n + 20).
Hypothesis H20 : getr regs4 20 = a.
Hypothesis H21 : getr regs4 21 = getr regs 21. Hypothesis H22 : getr regs4 22 = getr regs 22.
Hypothesis H23 : getr regs4 23 = getr regs 23. Hypothesis H24 : getr regs4 24 = getr regs 24.
Hypothesis H25 : getr regs4 25 = getr regs 25. Hypothesis H26 : getr regs4 26 = getr regs 26.
Hypothesis H27 : getr regs4 27 = getr regs 27.
Hypothesis Hsp : alloc_ceiling + 8192 <= sp /\ sp < 2 ^ 63 /\ sp mod 16 = 0.
Hypothesis Hstk : forall x, sp - 8192 <= x < sp -> writable_at src0segs mem4 x.
Hypothesis Hsv20 : word_at src0segs mem4 (sp - 48) (getr regs 20).
Hypothesis Hsv19 : word_at src0segs mem4 (sp - 40) (getr regs 19).
Hypothesis Hsv18 : word_at src0segs mem4 (sp - 32) (getr regs 18).
Hypothesis Hsv9 : word_at src0segs mem4 (sp - 24) (getr regs 9).
Hypothesis Hsv8 : word_at src0segs mem4 (sp - 16) (getr regs 8).
Hypothesis Hsv1 : word_at src0segs mem4 (sp - 8) (getr regs 1).
Hypothesis Hlock : forall k, (k < 4)%nat -> mbyte src0segs mem4 (LOCK + Z.of_nat k) = Some (Z_to_bv 8 0).
Hypothesis Hnl : mbyte src0segs mem4 NLK = Some (Z_to_bv 8 0).
Hypothesis Herr : forall x, ERRNO <= x < ERRNO + 4 -> writable_at src0segs mem4 x.
Hypothesis Hn : 131052 <= n < 2 ^ 62.
Hypothesis Ha : 4096 <= bv_unsigned a /\ bv_unsigned a + 131072 <= alloc_ceiling /\ bv_unsigned a mod 4096 = 0.
Hypothesis Haimg : bv_unsigned a + 131072 <= 0x1f000 \/ 0x51000 <= bv_unsigned a.
Lemma regs_ok_ret : forall rv RV, sv_denot E rv = RV -> getr regs4 10 = RV -> regs_ok E (regs_ret rv) regs4.
Proof.
intros rv RV Hrv H10. subst E sp n.
destruct Hxr as (X36 & X37 & X38 & X39 & X40 & X41 & X42 & X43 & X44 & X45 & X46 & X47 & X48 & X49 & X50).
regs_ok_cases.
all: rewrite <- ?X36, <- ?X37, <- ?X38, <- ?X39, <- ?X40, <- ?X41, <- ?X42,
<- ?X43, <- ?X44, <- ?X45, <- ?X46, <- ?X47, <- ?X48, <- ?X49, <- ?X50; try reflexivity.
all: try (symmetry; apply getr_zero).
all: rewrite ?H2, ?H8, ?H19, ?H20, ?H21, ?H22, ?H23, ?H24, ?H25, ?H26, ?H27, ?H9, ?H18, ?H4, ?H3; try reflexivity.
all: try (rewrite H10, <- Hrv; reflexivity).
all: try (f_equal; lia).
Qed.
Ltac lits := unfold LOCK, NLK, CTX, ERRNO, TP, src0_D_malloc_lock, src0_D_malloc_context, src0_D_libc, src0_tp in *.
Lemma region_ok_stack_ret : region_ok src0segs E mem4 R_stack_ret.
Proof.
subst E sp n. pose proof (proj1 alloc_ceiling_val).
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val ew E_mi R_stack_ret]; try lia.
- intros o Ho. apply Hstk. lia.
- repeat apply Forall_cons; try apply Forall_nil;
(eapply chunk_ok_word_at; [| first [exact Hsv20 | exact Hsv19 | exact Hsv18 | exact Hsv9 | exact Hsv8 | exact Hsv1]]);
cbn [sv_denot ew E_mi]; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned.
Qed.
Lemma region_ok_lock : forall E', region_ok src0segs E' mem4 R_lock.
Proof.
intros E'. apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_lock]; lits; try lia.
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_cval src0segs _ mem4 0 _ 4 (SLit 0) 0); [reflexivity | lia |].
intros k Hk. rewrite le_byte_0, Z.add_0_l. apply Hlock. exact Hk.
Qed.
Lemma region_ok_nl : forall E', region_ok src0segs E' mem4 R_nl.
Proof.
intros E'. apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_nl]; lits; try lia.
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_cval src0segs _ mem4 0 _ 1 (SLit 0) 0); [reflexivity | lia |].
intros k Hk. rewrite le_byte_0. destruct k; [|lia]. rewrite Z.add_0_l, Z.add_0_r. exact Hnl.
Qed.
Lemma region_ok_errno : forall E', region_ok src0segs E' mem4 R_errno.
Proof.
intros E'. apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_errno]; lits; try lia.
- intros o Ho. rewrite Z.add_0_l. apply Herr. lia.
- apply Forall_nil.
Qed.
Lemma facts_ret_sp_n : afact_ok E 2 F_sp /\ afact_ok E 10 F_n /\ afact_ok E 34 F_map /\ acond_ok E C_direct.
Proof.
subst E sp n. pose proof (proj1 alloc_ceiling_val). pose proof (u64_range (getr regs 10)).
unfold afact_ok, acond_ok, F_sp, F_n, F_map, C_direct; cbn [af_lo af_hi af_al2 ac_c ac_a ac_b ew E_mi sv_denot].
change (2 ^ 0) with 1. change (2 ^ 4) with 16. change (2 ^ 12) with 4096. rewrite !Z.mod_1_r.
repeat split; try lia.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite branch_geu, u64_of_Z by lia. apply negb_true_iff. apply Z.ltb_ge. lia.
Qed.
Theorem st_ok_ret0 :
getr regs4 10 = Z_to_bv 64 0 ->
st_ok src0segs E ss_ret0 (mkst regs4 (Z_to_bv 64 RA_AM) mem4 (seg_rom src0segs)).
Proof.
intros H10. pose proof (proj1 alloc_ceiling_val). pose proof facts_ret_sp_n as (F1 & F2 & F3 & F4).
unfold st_ok, ss_ret0, mkst; cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]).
split; [apply (regs_ok_ret (SLit 0) (Z_to_bv 64 0)); [reflexivity | exact H10]|]. split.
- apply mem_ok_intro; [vm_compute; reflexivity| |].
+ unfold mem_ret0. apply Forall_cons; [apply region_ok_stack_ret|]. apply Forall_cons; [apply region_ok_lock|].
apply Forall_cons; [apply region_ok_nl|]. apply Forall_cons; [apply region_ok_errno|apply Forall_nil].
+ subst E sp n. cbn [pairwise_disjoint all_disjoint mem_ret0]. unfold extent_disjoint.
cbn [base_val r_base r_lo r_hi ew E_mi R_stack_ret R_lock R_nl R_errno]. lits. repeat split; lia.
- split; [|split; [|exact I]].
+ cbn [f_atoms facts_ret0 atoms_ok]. repeat split; assumption || apply F1 || apply F2 || apply F3.
+ cbn [f_conds facts_ret0 conds_ok]. split; [exact F4 | exact I].
Qed.
Theorem st_ok_ret1 :
getr regs4 10 = g ->
4096 <= bv_unsigned g -> bv_unsigned g + 40 <= alloc_ceiling -> bv_unsigned g mod 8 = 0 ->
(bv_unsigned g + 40 <= 0x1f000 \/ 0x51000 <= bv_unsigned g) ->
(forall x, bv_unsigned g + 16 <= x < bv_unsigned g + 40 -> writable_at src0segs mem4 x) ->
(bv_unsigned a + 8 <= bv_unsigned g + 16 \/ bv_unsigned g + 40 <= bv_unsigned a) ->
(forall i, 0 <= i < 8 -> mbyte src0segs mem4 (bv_unsigned a + i) = Some (Z_to_bv 8 0)) ->
(forall x, bv_unsigned a <= x < bv_unsigned a + 8 -> writable_at src0segs mem4 x) ->
(forall k, (k < 4)%nat -> mbyte src0segs mem4 (CTX + 12 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte ctr 4 k))) ->
0 <= ctr < 2 ^ 32 ->
(forall x, CTX + 12 <= x < CTX + 16 -> writable_at src0segs mem4 x) ->
st_ok src0segs E ss_ret1 (mkst regs4 (Z_to_bv 64 RA_AM) mem4 (seg_rom src0segs)).
Proof.
intros H10 Hg1 Hg2 Hg3 Hgimg Hgw Hag Hmz Hmw Hctr Hctr_range Hctw.
pose proof (proj1 alloc_ceiling_val). pose proof facts_ret_sp_n as (F1 & F2 & F3 & F4).
unfold st_ok, ss_ret1, mkst; cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]).
split; [apply (regs_ok_ret (SOff 35 0) g); [subst E; cbn [sv_denot ew E_mi]; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned | exact H10]|]. split.
- apply mem_ok_intro; [vm_compute; reflexivity| |].
+ unfold mem_ret1.
apply Forall_cons.
{ apply region_ok_intro; subst E; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val ew E_mi R_map]; try lia.
- intros o Ho. rewrite <- (Z.add_0_r (bv_unsigned a + o)). replace (bv_unsigned a + o + 0) with (bv_unsigned a + o) by lia. apply Hmw. lia.
- apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_czero. intros i Hi. rewrite Z.add_0_r. apply Hmz. exact Hi. }
apply Forall_cons.
{ apply region_ok_intro; subst E; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val ew E_mi R_meta]; try lia.
- intros o Ho. apply Hgw. lia.
- apply Forall_nil. }
apply Forall_cons; [apply region_ok_stack_ret|]. apply Forall_cons; [apply region_ok_lock|].
apply Forall_cons; [apply region_ok_nl|].
apply Forall_cons.
{ apply region_ok_intro; subst E; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val ew E_mi R_ctr]; lits; try lia.
- intros o Ho. rewrite Z.add_0_l. apply Hctw. lia.
- apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_cval src0segs _ mem4 0 _ 4 (SOff 33 0) ctr); [| lia |].
+ cbn [sv_denot ew E_mi]. rewrite u64_of_Z by lia. rewrite Z.add_0_r. reflexivity.
+ intros k Hk. rewrite Z.add_0_l. apply Hctr. exact Hk. }
apply Forall_cons; [apply region_ok_errno|apply Forall_nil].
+ subst E sp n. cbn [pairwise_disjoint all_disjoint mem_ret1]. unfold extent_disjoint.
cbn [base_val r_base r_lo r_hi ew E_mi R_map R_meta R_stack_ret R_lock R_nl R_ctr R_errno]. lits. repeat split; lia.
- split; [|split; [|exact I]].
+ cbn [f_atoms facts_ret1 atoms_ok]. split.
{ unfold afact_ok, F_meta; subst E; cbn [af_lo af_hi af_al2 ew E_mi]. change (2 ^ 3) with 8. lia. }
split; [exact F3|]. split; [exact F1|]. split; [exact F2|]. split; [|exact I].
unfold afact_ok, F_ctr; subst E; cbn [af_lo af_hi af_al2 ew E_mi]. rewrite u64_of_Z by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
+ cbn [f_conds facts_ret1 conds_ok]. split; [exact F4 | exact I].
Qed.
End l.
Section p.
Variables (regs : bvmap 5 word) (seq ctr : Z) (useq : list byte) (a g : word) (xr : nat -> word).
Let E := E_mi regs seq ctr useq a g xr.
Lemma ss_mun_mem : ss_mem ss_mun = nth 0 (ss_mem ss_mun) R_stack :: tl mem_ret0.
Proof. vm_compute. reflexivity. Qed.
Lemma st_ok_mun2 : forall regs5 mem5 (ua un : word),
regs_ok E (ss_regs ss_mun) regs5 -> mem_ok src0segs E mem5 (ss_mem ss_mun) -> facts_ok E (ss_facts ss_mun) ->
alloc_ceiling + 8192 <= bv_unsigned (getr regs 2) ->
0 < bv_unsigned un -> bv_unsigned ua + bv_unsigned un <= alloc_ceiling ->
(bv_unsigned ua + bv_unsigned un <= 0x1f000 \/ 0x51000 <= bv_unsigned ua) ->
st_ok src0segs E ss_mun2
(mkst (regupd regs5 10 (Z_to_bv 64 0)) (v_addi (Z_to_bv 64 (ss_pc ss_mun)) 4)
(apply_unmaps mem5 [(ua, un)]) (seg_rom src0segs)).
Proof.
intros regs5 mem5 ua un HR HM HG Hsp Hn Hhi Himg. pose proof (proj1 alloc_ceiling_val).
pose proof (u64_range ua). pose proof (u64_range un).
change ss_mun2 with (resume ss_mun (SLit 0) (ss_mem ss_mun) (ss_facts ss_mun)).
eapply (st_ok_resume_mem src0segs 51 E E); [exact HR | apply env_agree_refl | vm_compute; reflexivity | reflexivity | | exact HG].
rewrite <- (Z_to_bv_bv_unsigned 64 ua), <- (Z_to_bv_bv_unsigned 64 un).
apply mem_ok_unmap; [exact HM | lia | lia | lia |].
assert (Hstk : r_base (nth 0 (ss_mem ss_mun) R_stack) = Some 2%nat /\ r_lo (nth 0 (ss_mem ss_mun) R_stack) = -8192
/\ r_hi (nth 0 (ss_mem ss_mun) R_stack) = 0) by (vm_compute; repeat split; reflexivity).
destruct Hstk as (S1 & S2 & S3).
intros r Hr. rewrite ss_mun_mem in Hr. cbn [tl mem_ret0 In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]];
[ rewrite S1, S2, S3 | ..]; subst E; cbn [base_val r_base r_lo r_hi ew E_mi R_lock R_nl R_errno];
unfold LOCK, NLK, CTX, ERRNO, TP, src0_D_malloc_lock, src0_D_malloc_context, src0_D_libc, src0_tp; lia.
Qed.
End p.
Lemma run_mi : sym_runN src0segs src0tbl FUEL ss_mi = (ss_thr, RS_stopped (SR_branch BC_LTU (SOff 10 0) (SLit 131052))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_thr : sym_runN src0segs src0tbl FUEL (add_cond ss_thr C_direct) = (ss_mmap, RS_ecall).
Proof. vm_compute. reflexivity. Qed.
Lemma run_refused : sym_runN src0segs src0tbl FUEL ss_refused = (ss_ref_end, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_granted : sym_runN src0segs src0tbl FUEL ss_granted = (ss_g1, RS_stopped (SR_branch BC_NE (ac_a C_mapok) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_g1 : sym_runN src0segs src0tbl FUEL (add_cond ss_g1 C_mapok) = (ss_seq, RS_stopped (SR_branch BC_NE (SOff 32 0) (SLit 255))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_seq255 : sym_run_toN src0segs src0tbl FUEL src0_A_alloc_meta (add_cond ss_seq C_seq255) = (ss_am255, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma run_seqne : sym_run_toN src0segs src0tbl FUEL src0_A_alloc_meta (add_cond ss_seq C_seqne) = (ss_amne, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma run_ret0 : sym_runN src0segs src0tbl FUEL ss_ret0 = (ss_mun, RS_ecall).
Proof. vm_compute. reflexivity. Qed.
Lemma run_mun2 : sym_runN src0segs src0tbl FUEL ss_mun2 = (ss_none_end, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_ret1 : sym_run_toN src0segs src0tbl FUEL src0_A_enframe ss_ret1 = (ss_enf, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma ss_mmap_pc : ss_pc ss_mmap = src0_A_mmap + 0xc4. Proof. reflexivity. Qed.
Lemma ss_am255_pc : ss_pc ss_am255 = src0_A_alloc_meta. Proof. reflexivity. Qed.
Lemma ss_amne_pc : ss_pc ss_amne = src0_A_alloc_meta. Proof. reflexivity. Qed.
Lemma ss_ref_end_pc : ss_pc ss_ref_end = src0_A_libc_malloc_impl + 0x58. Proof. reflexivity. Qed.
Lemma ss_none_end_pc : ss_pc ss_none_end = src0_A_libc_malloc_impl + 0x58. Proof. reflexivity. Qed.
Lemma ss_mun_pc : ss_pc ss_mun = src0_A_munmap + 0x28. Proof. reflexivity. Qed.
Lemma ss_enf_pc : ss_pc ss_enf = src0_A_enframe. Proof. reflexivity. Qed.
Definition cs_atoms : list nat := [2; 3; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition preserved_check (ss : sstate) : bool :=
forallb (fun k => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat k))) (SOff k 0)) cs_atoms
&& sv_eqb (sr_get (ss_regs ss) 4) (SLit TP).
Lemma regs_preserved_sym : forall regs seq ctr useq a g xr ss ms,
preserved_check ss = true ->
st_ok src0segs (E_mi regs seq ctr useq a g xr) ss ms -> getr regs 4 = Z_to_bv 64 TP ->
regs_preserved regs (ms_regs ms).
Proof.
intros regs seq ctr useq a g xr ss ms Hc HS Htp r Hr.
unfold preserved_check in Hc. apply andb_prop in Hc as [Hc H4]. rewrite forallb_forall in Hc.
rewrite (st_ok_reg src0segs _ ss ms _ HS).
assert (CASE : r = 4 \/ exists k, In k cs_atoms /\ r = Z.of_nat k).
{ unfold callee_saved in Hr. unfold cs_atoms.
destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [right; exists 2%nat | right; exists 3%nat | left; reflexivity | right; exists 8%nat | right; exists 9%nat |];
try (split; [cbn; tauto | reflexivity]).
right. exists (Z.to_nat r). split; [|lia].
assert (H : (18 <= Z.to_nat r <= 27)%nat) by lia. revert H. generalize (Z.to_nat r) as m. intros m H.
do 18 (destruct m as [|m]; [lia|]).
do 10 (destruct m as [|m]; [cbn; tauto|]). lia. }
destruct CASE as [-> | (k & Hk & ->)].
- replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity).
apply sv_eqb_eq in H4. rewrite H4. cbn [sv_denot]. symmetry. exact Htp.
- specialize (Hc k Hk). apply sv_eqb_eq in Hc. rewrite Hc. cbn [sv_denot].
rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
unfold cs_atoms in Hk. cbn [In] in Hk.
destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; cbn [ew E_mi];
f_equal; apply bv_eq; reflexivity.
Qed.
Definition scratch_check (ss : sstate) : bool :=
existsb (fun r => match r_base r with Some 2%nat => (r_wlo r <=? -8192) && (0 <=? r_whi r) | _ => false end) (ss_mem ss)
&& existsb (fun r => match r_base r with None => (r_wlo r <=? ERRNO) && (ERRNO + 4 <=? r_whi r) | _ => false end) (ss_mem ss).
Lemma scratch_writable_sym : forall regs seq ctr useq a g xr ss ms x,
scratch_check ss = true ->
st_ok src0segs (E_mi regs seq ctr useq a g xr) ss ms ->
(bv_unsigned (getr regs 2) - 8192 <= x < bv_unsigned (getr regs 2)) \/ (ERRNO <= x < ERRNO + 4) ->
writable_at src0segs (ms_mem ms) x.
Proof.
intros regs seq ctr useq a g xr ss ms x Hc HS Hx.
pose proof (st_ok_mem_ok src0segs _ _ _ HS) as (_ & Hok & _). rewrite Forall_forall in Hok.
unfold scratch_check in Hc. apply andb_prop in Hc as [H1 H2].
apply existsb_exists in H1 as (r1 & Hin1 & Hr1). apply existsb_exists in H2 as (r2 & Hin2 & Hr2).
destruct Hx as [Hx|Hx].
- destruct (r_base r1) as [[|[|[|k]]]|] eqn:Eb; try discriminate.
apply andb_prop in Hr1 as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.leb_le in Q2.
destruct (Hok r1 Hin1) as (_ & _ & W & _). rewrite Eb in W. cbn [base_val ew E_mi] in W.
replace x with (bv_unsigned (getr regs 2) + (x - bv_unsigned (getr regs 2))) by lia. apply W. lia.
- destruct (r_base r2) eqn:Eb; try discriminate.
apply andb_prop in Hr2 as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.leb_le in Q2.
destruct (Hok r2 Hin2) as (_ & _ & W & _). rewrite Eb in W. cbn [base_val] in W.
replace x with (0 + x) by lia. apply W. lia.
Qed.
Lemma ref_end_checks : preserved_check ss_ref_end = true /\ scratch_check ss_ref_end = true.
Proof. vm_compute. split; reflexivity. Qed.
Lemma none_end_checks : preserved_check ss_none_end = true /\ scratch_check ss_none_end = true.
Proof. vm_compute. split; reflexivity. Qed.
Lemma enf_checks : preserved_check ss_enf = true /\ scratch_check ss_enf = true.
Proof. vm_compute. split; reflexivity. Qed.
End e.
