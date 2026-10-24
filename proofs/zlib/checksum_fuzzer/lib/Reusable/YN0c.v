(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0x YO0z YO0y YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0s YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0v YK02 YP0n YM06 YM02 YM00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a YO0b YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN02 YN2b YN2e YN04 YN0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s YO0u YO0v YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN2c YN2f YN2g YN2d YN0d.
From Stdlib Require Import List.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM01.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma mreal_IAsk {R} : forall segs c q s (k : Z -> itree astate R) Q,
SR segs c (fun c1 => knode segs c1 q s (fun z c2 => mreal segs c2 (k z) Q)) -> mreal segs c (IAsk q s k) Q.
Proof. intros. exact H. Qed.
Lemma mreal_IRet {R} : forall segs c (r : R) Q, SR segs c (Q r) -> mreal segs c (IRet r) Q.
Proof. intros. exact H. Qed.
Lemma with_vmmaps_self : forall md, m_vm_lazy md = [] -> m_vm_materialized md = [] -> md = with_vmmaps (m_vmmaps md) md.
Proof.
intros [fd [maps lazy mat] io fs proc lim tm] Hl Hm. unfold with_vmmaps, m_vmmaps, m_vm_lazy, m_vm_materialized in *.
cbn in *. subst. reflexivity.
Qed.
End d.
Notation B := src0_msyms.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma B_segs : ms_segs B = src0segs. Proof. reflexivity. Qed.
Lemma B_ctx : ms_ctx B = CTX. Proof. reflexivity. Qed.
Lemma B_lock : ms_lock B = LOCK. Proof. reflexivity. Qed.
Lemma B_nl : ms_libc B + 3 = NLK. Proof. reflexivity. Qed.
Lemma B_errno : errno_addr B = ERRNO. Proof. reflexivity. Qed.
Lemma B_tp : ms_tp B = TP. Proof. reflexivity. Qed.
Lemma B_malloc : ms_malloc B = src0_A_malloc. Proof. reflexivity. Qed.
Lemma src0_img_range : forall a, in_img B a -> 0x10000 <= a < 0x51000.
Proof.
intros a [_ (s & Hs & Ha)].
assert (H : forallb (fun s : word * word => (0x10000 <=? bv_unsigned (fst s)) && (bv_unsigned (fst s) + bv_unsigned (snd s) <=? 0x51000))
(segments_reserved src0segs) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H s Hs). apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma src0_errno_img : forall x, ERRNO <= x < ERRNO + 4 -> in_img B x.
Proof.
intros x Hx. eapply (covered_sound B 0x1f000 0x32000); [vm_compute; reflexivity|].
unfold ERRNO, src0_tp in Hx. lia.
Qed.
Lemma src0_rwseg_img : forall x, 0x1f000 <= x < 0x51000 -> in_img B x.
Proof. intros x Hx. eapply (covered_sound B 0x1f000 0x32000); [vm_compute; reflexivity| lia]. Qed.
Section f.
Hypothesis AMH : alloc_meta_hyp B.
Lemma errno_not_footprint : forall L A mem md x,
MRc B L A mem md -> ERRNO <= x < ERRNO + 4 -> ~ in_footprint L A x.
Proof.
intros L A mem md x M Hx (rg & Hrg & Hin).
destruct (In_footprint_inv A rg Hrg) as [-> | [(ar & Har & ->) | (k & r & Hr & Hk & Hl & ->)]]; cbn [fst snd loc_addr] in Hin.
- rewrite (mc_ctx _ _ _ _ _ M) in Hin. cbn in Hin. unfold CTX_SIZE, ERRNO, src0_D_malloc_context, src0_tp in *. lia.
- destruct (inv_areas (mc_wf _ _ _ _ _ M)) as (_ & Hareas & _).
destruct (Hareas ar Har) as (r & o & rg & -> & _ & Ho & Hr & Hl & Hlen & _). cbn [loc_addr] in Hin.
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) r rg Hr Hl) as (_ & _ & _ & Himg).
apply (Himg x); [unfold PGSZ in *; lia|]. apply src0_errno_img. exact Hx.
- destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) k r Hr Hl) as (_ & _ & _ & Himg).
apply (Himg x); [lia|]. apply src0_errno_img. exact Hx.
Qed.
Lemma errno_not_owned : forall L A mem md x,
MRc B L A mem md -> ERRNO <= x < ERRNO + 4 -> ~ owned B L A x.
Proof.
intros L A mem md x M Hx [[Hfp Hnb] | Hs].
- exact (errno_not_footprint L A mem md x M Hx Hfp).
- unfold static_owned in Hs. cbn in Hs. unfold ERRNO, src0_tp, src0_D_malloc_lock, src0_D_libc, src0_D_got_stack_chk_guard,
src0_D_stack_chk_guard, src0_D_debruijn32, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab in *. lia.
Qed.
Definition useq_of (A : astate) : list byte :=
map (fun k => Z_to_bv 8 (le_byte (nth k (st_unmap_seq A) 0) 1 0)) (seq 0 32).
Lemma useq_of_length : forall A, length (useq_of A) = 32%nat.
Proof. intros A. unfold useq_of. rewrite length_map, length_seq. reflexivity. Qed.
Lemma In_ctx_image : forall A c, In c (ctx_cells A) -> In c (image A).
Proof. intros A c H. unfold image. apply in_app_iff. left. exact H. Qed.
Lemma In_ctx_seq : forall A, In (MCell (LCtx CTX_seq) 1 (VZ (st_seq A))) (ctx_cells A).
Proof. intros A. unfold ctx_cells. apply in_app_iff. left. cbn. tauto. Qed.
Lemma In_ctx_ctr : forall A, In (MCell (LCtx CTX_mmap_counter) 4 (VZ (st_mmap_counter A))) (ctx_cells A).
Proof. intros A. unfold ctx_cells. apply in_app_iff. left. cbn. tauto. Qed.
Lemma In_ctx_useq : forall A k, (k < 32)%nat ->
In (MCell (LCtx (CTX_unmap_seq + Z.of_nat k)) 1 (VZ (nth k (st_unmap_seq A) 0))) (ctx_cells A).
Proof.
intros A k Hk. unfold ctx_cells. rewrite !in_app_iff. right. right. right. left.
apply in_map_iff. exists k. split; [reflexivity|]. apply in_seq. lia.
Qed.
Definition E_entry (regs : bvmap 5 word) (A : astate) (a g : word) (xr : nat -> word) : env :=
E_mi regs (st_seq A) (st_mmap_counter A) (useq_of A) a g xr.
Lemma entry_st_ok : forall L A regs mem md a g xr,
call_pre B (MRx B) L A regs mem md -> bv_unsigned (getr regs 10) < 2 ^ 62 ->
st_ok src0segs (E_entry regs A a g xr) ss_mi (mkst regs (Z_to_bv 64 src0_A_malloc) mem (seg_rom src0segs)).
Proof.
intros L A regs mem md a g xr (MX & HW & HB & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herr & _) Hn.
pose proof (MRx_MRc _ _ _ _ _ MX) as M.
pose proof (MRc_memrep B L A mem md M) as MM.
pose proof (mc_statics _ _ _ _ _ M) as ST. pose proof (mc_ctx _ _ _ _ _ M) as EC.
pose proof (inv_ctx HW) as (Lact & Lus & Luseq & Lbo & Uus & Uuseq & Ubo & Rseq & Rctr & _).
unfold spZ in *. rewrite B_segs, B_errno, B_tp in *.
apply st_ok_entry.
- unfold ALLOC_STACK in *. lia.
- unfold ALLOC_STACK in *. exact Hstk.
- exact Htp.
- exact Hn.
- intros k Hk. rewrite <- B_lock. apply (st_lock _ _ ST). exact Hk.
- rewrite <- B_nl. apply (st_needlocks _ _ ST).
- intros k Hk. pose proof (memrep_cell B L A mem _ MM (In_ctx_image A _ (In_ctx_ctr A))) as C.
unfold cell_mem in C. cbn [mc_loc mc_w mc_val loc_addr sval_num] in C. rewrite EC, B_ctx in C.
unfold CTX_mmap_counter in C. change (ms_segs B) with src0segs in C. apply C. exact Hk.
- exact Rctr.
- apply useq_of_length.
- intros k Hk. pose proof (memrep_cell B L A mem _ MM (In_ctx_image A _ (In_ctx_useq A k Hk))) as C.
unfold cell_mem in C. cbn [mc_loc mc_w mc_val loc_addr sval_num] in C. rewrite EC, B_ctx in C.
unfold CTX_unmap_seq in C. specialize (C 0%nat ltac:(lia)). rewrite Z.add_0_r in C. change (ms_segs B) with src0segs in C.
replace (CTX + 848 + Z.of_nat k) with (CTX + (848 + Z.of_nat k)) by lia. rewrite C.
unfold useq_of. rewrite nth_error_map, nth_error_seq, (proj2 (Nat.ltb_lt k 32) Hk). reflexivity.
- pose proof (memrep_cell B L A mem _ MM (In_ctx_image A _ (In_ctx_seq A))) as C.
unfold cell_mem in C. cbn [mc_loc mc_w mc_val loc_addr sval_num] in C. rewrite EC, B_ctx in C.
unfold CTX_seq in C. specialize (C 0%nat ltac:(lia)). rewrite Z.add_0_r in C. change (ms_segs B) with src0segs in C. exact C.
- lia.
- exact Herr.
Qed.
Lemma fetch_ret : fetch_word src0segs (Z_to_bv 64 (src0_A_libc_malloc_impl + 0x58)) = Some (0x00008067%bv : bv 32).
Proof. rewrite <- (Z_to_bv_bv_unsigned 32 (0x00008067%bv : bv 32)). apply src0tbl_ok. vm_compute. reflexivity. Qed.
Lemma decode_ret : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma SR_final_ret : forall E ss ms md Q,
st_ok src0segs E ss ms -> ss_resv ss = None -> ss_pc ss = src0_A_libc_malloc_impl + 0x58 ->
sr_get (ss_regs ss) 1 = SOff 1 0 -> YK0s.ret_ok (ew E 1) ->
m_halted md = None -> m_vm_lazy md = [] ->
Q (mkCfg (mkst (ms_regs ms) (ew E 1) (ms_mem ms) (seg_rom src0segs)) md) ->
SR src0segs (mkCfg ms md) Q.
Proof.
intros E ss ms md Q HS Hrv Hpc Hra Hret Hh Hlz HQ.
pose proof (st_ok_reg src0segs E ss ms 1 HS) as R1. rewrite Hra in R1. cbn [sv_denot] in R1.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned in R1.
rewrite (st_ok_mkst src0segs E ss ms HS Hrv). rewrite Hpc.
eapply SR_step; [exact Hh | exact Hlz | reflexivity | |].
- eapply step_jalr_x0; [apply fetch_ret | reflexivity | apply decode_ret | exact R1].
- cbn [ms_regs ms_mem mkst]. change (bv_signed (0%bv : bv 12)) with 0. unfold YK0s.ret_ok in Hret. rewrite Hret.
apply SR_ret. exact HQ.
Qed.
Lemma leaf_unchanged : forall L A regs mem md n regs' mem',
call_pre B (MRx B) L A regs mem md ->
(forall x, 0 <= x < 2 ^ 64 -> ~ scratch B regs x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
(forall x, scratch B regs x -> writable_at src0segs mem' x) ->
regs_preserved regs regs' -> getr regs' 10 = Z_to_bv 64 0 ->
malloc_leaf B (MRx B) L A regs mem md n (None, A) (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom src0segs)) md).
Proof.
intros L A regs mem md n regs' mem' PRE Hfr Hsw Hpres Ha0.
pose proof PRE as (MX & HW & HB & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herr & _).
pose proof (MRx_MRc _ _ _ _ _ MX) as M. destruct (mc_md _ _ _ _ _ M) as (Hh & Hlz & Hmat).
assert (NS : forall x, owned B L A x -> ~ scratch B regs x).
{ intros x Ho [Hs | Hs].
- pose proof (owned_low B L A mem md x M Ho). unfold spZ in *. lia.
- rewrite B_errno in Hs. exact (errno_not_owned L A mem md x M Hs Ho). }
assert (EQ : forall x, owned B L A x -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x).
{ intros x Ho. pose proof (owned_low B L A mem md x M Ho). unfold mbyte. rewrite B_segs, Hfr; [reflexivity | pose proof alloc_ceiling_val; lia | apply NS; exact Ho]. }
exists L, regs', mem', md. split; [reflexivity|]. split; [| split; [exact Ha0 | reflexivity]].
split; [| split; [exact HW | split; [exact HB | split; [apply layout_le_refl | split; [auto | split; [exact Hpres | split;
[exists (m_vmmaps md); apply with_vmmaps_self; assumption | split; [| split]]]]]]]].
-   apply (mr_frame _ _ (MRx_laws B) L A mem mem' md md MX).
+ exact EQ.
+ intros x Ho [b Hb]. pose proof (owned_low B L A mem md x M Ho). exists b. rewrite Hfr; [exact Hb | pose proof alloc_ceiling_val; lia | apply NS; exact Ho].
+ intros p k i Hin Hi. destruct (blocks_facts B L A mem md p k i M Hin Hi) as ([b Hb] & Hlo & Hhi & Hno).
exists b. rewrite Hfr; [exact Hb | pose proof alloc_ceiling_val; lia |].
intros [Hs|Hs]; [unfold spZ in *; lia|]. rewrite B_errno in Hs.
destruct (block_region A p k (mc_wf _ _ _ _ _ M) Hin) as (r & o & rg & -> & Hrg & Hk & Hl & Ho & _ & Hlen & _).
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) r rg Hrg Hl) as (_ & _ & _ & Himg).
apply (Himg (ptr_addr L (SP r o) + i)); [unfold ptr_addr; cbn [loc_addr]; lia | apply src0_errno_img; exact Hs].
+ reflexivity. + exact Hh. + exact Hlz. + exact Hmat.
-   intros x Hhi Ho Ho' Hns _. pose proof (proj1 alloc_ceiling_val).
assert (Hx : 0 <= x < 2 ^ 64) by (destruct Hhi as [Hhi|Hhi]; [lia | apply src0_img_range in Hhi; lia]).
unfold mbyte, writable_at, wview. rewrite B_segs, Hfr by assumption. tauto.
-   intros p k i Hin _ Hi. destruct (blocks_facts B L A mem md p k i M Hin Hi) as (_ & Hlo & Hhi & Hno).
unfold mbyte. rewrite B_segs, Hfr; [reflexivity | pose proof alloc_ceiling_val; lia |].
intros [Hs|Hs]; [unfold spZ in *; lia|]. rewrite B_errno in Hs.
destruct (block_region A p k (mc_wf _ _ _ _ _ M) Hin) as (r & o & rg & -> & Hrg & Hk & Hl & Ho & _ & Hlen & _).
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) r rg Hrg Hl) as (_ & _ & _ & Himg).
apply (Himg (ptr_addr L (SP r o) + i)); [unfold ptr_addr; cbn [loc_addr]; lia | apply src0_errno_img; exact Hs].
-   rewrite B_segs. exact Hsw.
Qed.
Lemma in_wrange_scratch : forall E regs rs x,
map (fun r => (r_base r, r_wlo r, r_whi r)) rs =
[(Some 2%nat, -8192, 0); (None, 0, 0); (None, 0, 0); (None, 0, 0); (None, 0, 0); (None, 0, 0); (None, ERRNO, ERRNO + 4)] ->
ew E 2 = getr regs 2 ->
in_wrange E rs x -> scratch B regs x.
Proof.
intros E regs rs x Hsk E2 (r & Hin & Hx).
assert (Hk : In (r_base r, r_wlo r, r_whi r) (map (fun r => (r_base r, r_wlo r, r_whi r)) rs)) by (apply in_map_iff; exists r; auto).
rewrite Hsk in Hk. cbn [In] in Hk. unfold scratch, spZ, ALLOC_STACK. rewrite B_errno.
destruct Hk as [Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[]]]]]]]];
injection Hk as E1 E2' E3; rewrite <- E1, <- E2', <- E3 in Hx; cbn [base_val] in Hx; rewrite ?E2 in Hx; lia.
Qed.
Lemma sk_mi : map (fun r => (r_base r, r_wlo r, r_whi r)) (ss_mem ss_mi) =
[(Some 2%nat, -8192, 0); (None, 0, 0); (None, 0, 0); (None, 0, 0); (None, 0, 0); (None, 0, 0); (None, ERRNO, ERRNO + 4)].
Proof. vm_compute. reflexivity. Qed.
Lemma sk_thr : map (fun r => (r_base r, r_wlo r, r_whi r)) (ss_mem (add_cond ss_thr C_direct)) =
[(Some 2%nat, -8192, 0); (None, 0, 0); (None, 0, 0); (None, 0, 0); (None, 0, 0); (None, 0, 0); (None, ERRNO, ERRNO + 4)].
Proof. vm_compute. reflexivity. Qed.
Lemma sk_refused : map (fun r => (r_base r, r_wlo r, r_whi r)) (ss_mem ss_refused) =
[(Some 2%nat, -8192, 0); (None, 0, 0); (None, 0, 0); (None, 0, 0); (None, 0, 0); (None, 0, 0); (None, ERRNO, ERRNO + 4)].
Proof. vm_compute. reflexivity. Qed.
Lemma region_free_exists_high : forall (ivs : list (word * word)) (nZ : Z),
0 < nZ <= 2 ^ 39 ->
Forall (fun p => bv_unsigned (snd p) <= 2 ^ 39) ivs ->
(length ivs <= 84)%nat ->
exists a : word,
bv_unsigned a mod page_size = 0 /\ 43 * 2 ^ 40 <= bv_unsigned a /\
bv_unsigned a + nZ <= alloc_ceiling /\
region_free ivs a (Z_to_bv 64 nZ) = true.
Proof.
intros ivs nZ HnZ Hsizes Hlen.
destruct (pigeonhole_Z (map iv_slot ivs) 43 85) as (j & Hj & Hnotin).
{ rewrite length_map. lia. }
change (Z.of_nat 85) with 85 in Hj.
assert (Hslotv : slot = 1099511627776) by reflexivity.
assert (Hjs : 0 <= j * slot < 2 ^ 64) by (rewrite Hslotv; lia).
exists (Z_to_bv 64 (j * slot)).
rewrite Z_to_bv64_small by exact Hjs.
split; [|split; [|split]].
- unfold page_size. rewrite Hslotv.
replace (j * 1099511627776) with ((j * 268435456) * 4096) by lia.
apply Z_mod_mult.
- rewrite Hslotv. lia.
- pose proof (proj1 alloc_ceiling_value). rewrite Hslotv. lia.
- induction ivs as [|[b s] ivs IH]; [reflexivity|].
cbn [region_free]. apply andb_true_iff. split.
+ apply Bool.negb_true_iff.
destruct (iv_overlap (Z_to_bv 64 (j * slot)) (Z_to_bv 64 nZ) b s) eqn:Hov; [|reflexivity].
exfalso. apply Hnotin. cbn [map]. left. symmetry.
apply (overlap_pins_slot b s j nZ); try lia.
* apply Forall_inv in Hsizes. cbn [snd] in Hsizes. rewrite Hslotv. lia.
* exact Hov.
+ apply IH.
* apply Forall_inv_tail in Hsizes. exact Hsizes.
* cbn [length] in Hlen. lia.
* intro Hin. apply Hnotin. cbn [map]. right. exact Hin.
Qed.
Lemma src0_reserved_small :
Forall (fun p => bv_unsigned (snd p) <= 2 ^ 39) (segments_reserved src0segs) /\ (length (segments_reserved src0segs) <= 8)%nat.
Proof.
split.
- assert (H : forallb (fun p : word * word => bv_unsigned (snd p) <=? 2 ^ 39) (segments_reserved src0segs) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. apply Forall_forall. intros p Hp. apply Z.leb_le. apply H. exact Hp.
- vm_compute. lia.
Qed.
Lemma src0_reserved_bytes : ivs_bytes (segments_reserved src0segs) <= 2 ^ 30.
Proof.
assert (H : (ivs_bytes (segments_reserved src0segs) <=? 2 ^ 30) = true) by (vm_compute; reflexivity).
apply Z.leb_le. exact H.
Qed.
Lemma live_bytes_nonneg : forall A, WF A -> 0 <= live_bytes A.
Proof.
intros A HW. destruct (inv_areas HW) as (_ & _ & _ & _ & _ & _ & _ & _ & Hnn).
unfold live_bytes. unfold region_of in Hnn.
assert (G : forall l, (forall k rg, nth_error l k = Some rg -> 0 <= rg_len rg) ->
0 <= fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 l).
{ induction l as [|r l IH]; intros Hl; cbn; [lia|].
assert (0 <= rg_len r) by (apply (Hl 0%nat r); reflexivity).
assert (0 <= fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 l)
by (apply IH; intros k rg Hk; apply (Hl (S k) rg); exact Hk).
destruct (rg_live r); lia. }
apply G. exact Hnn.
Qed.
Lemma direct_grant_exists : forall L A mem md len,
MRx B L A mem md -> mgrant A (KMmapRW len) -> 0 < len ->
exists a, grant_ok (Z_to_bv 64 0) md a (page_round len) = true.
Proof.
intros L A mem md len MX (Hpos & Hlive & Hsl & Hreq) Hlen. pose proof (MRx_MRc _ _ _ _ _ MX) as M.
pose proof (mc_ledger _ _ _ _ _ M) as G. pose proof (MRx_ledger_x _ _ _ _ _ MX) as LX.
unfold req_len in Hpos, Hlive, Hreq. unfold MG_LIVE, MG_SLOTS, MG_REQ in *.
pose proof (live_bytes_nonneg A (mc_wf _ _ _ _ _ M)) as Hlb.
destruct src0_reserved_small as [RS RL]. pose proof src0_reserved_bytes as RB.
destruct (region_free_exists28_std (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (page_round len)) as (a & Ha1 & Ha2 & Ha3 & Ha4).
- lia.
- rewrite length_app. rewrite (lg_reserved _ _ _ _ G). pose proof (lg_count _ _ _ _ G). change (ms_segs B) with src0segs. lia.
- rewrite ivs_bytes_app, (lg_reserved _ _ _ _ G). change (ms_segs B) with src0segs.
rewrite (ivs_bytes_live_bytes (vm_maps (m_vmmaps md))). pose proof (lx_lb _ _ _ LX). lia.
- exists a. unfold grant_ok.
rewrite (proj2 (Z.eqb_eq _ _) Ha1), (proj2 (Z.ltb_lt 0 _)) by lia.
pose proof (YM05.ceil_le_top _ (lg_ceil _ _ _ _ G)) as Htop.
assert (Ha3' : bv_unsigned a + page_round len <= alloc_top (m_vmmaps md)) by lia.
rewrite (proj2 (Z.leb_le _ _) Ha3'), Ha4.
rewrite (proj2 (Z.leb_le _ _)).
2:{ pose proof (lg_backing _ _ _ _ G). pose proof (lg_limit _ _ _ _ G). unfold SRC_LIM_MIN in *. lia. }
reflexivity.
Qed.
Lemma in_wrange_list : forall E rs x,
in_wrange E rs x ->
exists t, In t (map (fun r => (r_base r, r_wlo r, r_whi r)) rs) /\
base_val E (fst (fst t)) + snd (fst t) <= x < base_val E (fst (fst t)) + snd t.
Proof.
intros E rs x (r & Hin & Hx). exists (r_base r, r_wlo r, r_whi r). split; [apply in_map_iff; exists r; auto | exact Hx].
Qed.
Definition wr_g (regs : bvmap 5 word) (a : word) (x : Z) : Prop :=
scratch B regs x \/ ctxw B x \/ (bv_unsigned a <= x < bv_unsigned a + 8).
Lemma sk_granted : map (fun r => (r_base r, r_wlo r, r_whi r)) (ss_mem ss_granted) =
[(Some 34%nat, 0, 8); (Some 2%nat, -8192, 0); (None, 0, 0); (None, 0, 0); (None, CTX + 12, CTX + 16); (None, CTX + 848, CTX + 880); (None, CTX + 912, CTX + 913); (None, ERRNO, ERRNO + 4)].
Proof. vm_compute. reflexivity. Qed.
Lemma in_wrange_g : forall regs seq ctr useq a g xr rs x,
map (fun r => (r_base r, r_wlo r, r_whi r)) rs =
[(Some 34%nat, 0, 8); (Some 2%nat, -8192, 0); (None, 0, 0); (None, 0, 0); (None, CTX + 12, CTX + 16); (None, CTX + 848, CTX + 880); (None, CTX + 912, CTX + 913); (None, ERRNO, ERRNO + 4)] ->
in_wrange (E_mi regs seq ctr useq a g xr) rs x -> wr_g regs a x.
Proof.
intros regs seq ctr useq a g xr rs x Hsk Hw. apply in_wrange_list in Hw as (t & Hin & Hx). rewrite Hsk in Hin.
unfold wr_g, scratch, spZ, ALLOC_STACK, ctxw. rewrite B_errno, B_ctx. cbn [In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn [fst snd base_val ew E_mi] in Hx; lia.
Qed.
Lemma sk_g_all :
skeleton (ss_mem ss_granted) = skeleton (ss_mem (add_cond ss_g1 C_mapok)) /\
skeleton (ss_mem (add_cond ss_g1 C_mapok)) = skeleton (ss_mem (add_cond ss_seq C_seq255)) /\
skeleton (ss_mem (add_cond ss_g1 C_mapok)) = skeleton (ss_mem (add_cond ss_seq C_seqne)).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma run_to_am : forall regs seq ctr useq a g0 xr0 ms mdl Q,
let E := E_mi regs seq ctr useq a g0 xr0 in
m_halted mdl = None -> m_vm_lazy mdl = [] ->
st_ok src0segs E ss_granted ms ->
bv_unsigned a + 8 < 2 ^ 64 -> 0 <= seq < 256 ->
(forall ms5, ((seq = 255 /\ st_ok src0segs E ss_am255 ms5) \/ (seq <> 255 /\ st_ok src0segs E ss_amne ms5)) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ wr_g regs a x -> ms_mem ms5 (Z_to_bv 64 x) = ms_mem ms (Z_to_bv 64 x)) ->
SR src0segs (mkCfg ms5 mdl) Q) ->
SR src0segs (mkCfg ms mdl) Q.
Proof.
intros regs seq ctr useq a g0 xr0 ms mdl Q E Hh Hlz HS Ha Hseq Hk.
pose proof sk_g_all as (SK1 & SK2 & SK3).
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E ss_granted ss_g1); [exact Hh | exact Hlz | exact HS | apply run_granted |].
intros ms1 HS1 HF1.
apply (st_ok_add_cond src0segs E ss_g1 ms1 BC_NE (ac_a C_mapok) (SLit 0)) in HS1.
2:{ cbn [ac_a C_mapok sv_denot]. subst E. cbn [ew E_mi]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply mapok_taken. exact Ha. }
change (add_cond ss_g1 (mkAC BC_NE (ac_a C_mapok) (SLit 0))) with (add_cond ss_g1 C_mapok) in HS1.
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E (add_cond ss_g1 C_mapok) ss_seq); [exact Hh | exact Hlz | exact HS1 | apply run_g1 |].
intros ms2 HS2 HF2.
assert (FR12 : frame_of E (ss_mem ss_granted) (ms_mem ms) (ms_mem ms2)) by (eapply frame_of_trans; [exact SK1 | exact HF1 | exact HF2]).
destruct (Z.eq_dec seq 255) as [Es | Ns].
- apply (st_ok_add_cond_neg src0segs E ss_seq ms2 BC_NE (SOff 32 0) (SLit 255)) in HS2.
2:{ cbn [sv_denot]. subst E. cbn [ew E_mi]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite Es. vm_compute. reflexivity. }
change (add_cond ss_seq (mkAC (neg_bc BC_NE) (SOff 32 0) (SLit 255))) with (add_cond ss_seq C_seq255) in HS2.
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL src0_A_alloc_meta E (add_cond ss_seq C_seq255) ss_am255 RS_running);
[exact Hh | exact Hlz | exact HS2 | apply run_seq255 |].
intros ms5 HS5 HF5. apply Hk; [left; auto|].
intros x Hx Hnw.
assert (FR : frame_of E (ss_mem ss_granted) (ms_mem ms) (ms_mem ms5)).
{ eapply frame_of_trans; [| exact FR12 | exact HF5]. rewrite SK1. exact SK2. }
specialize (FR (Z64 x)). rewrite u64_of_Z in FR by exact Hx. apply FR. intros W. apply Hnw. eapply in_wrange_g; [apply sk_granted | exact W].
- apply (st_ok_add_cond src0segs E ss_seq ms2 BC_NE (SOff 32 0) (SLit 255)) in HS2.
2:{ cbn [sv_denot]. subst E. cbn [ew E_mi]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite branch_ne, !u64_of_Z by lia.
apply Bool.negb_true_iff. apply Z.eqb_neq. exact Ns. }
change (add_cond ss_seq (mkAC BC_NE (SOff 32 0) (SLit 255))) with (add_cond ss_seq C_seqne) in HS2.
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL src0_A_alloc_meta E (add_cond ss_seq C_seqne) ss_amne RS_running);
[exact Hh | exact Hlz | exact HS2 | apply run_seqne |].
intros ms5 HS5 HF5. apply Hk; [right; auto|].
intros x Hx Hnw.
assert (FR : frame_of E (ss_mem ss_granted) (ms_mem ms) (ms_mem ms5)).
{ eapply frame_of_trans; [| exact FR12 | exact HF5]. rewrite SK1. exact SK3. }
specialize (FR (Z64 x)). rewrite u64_of_Z in FR by exact Hx. apply FR. intros W. apply Hnw. eapply in_wrange_g; [apply sk_granted | exact W].
Qed.
Lemma src0_ENC : forall x, errno_addr B <= x < errno_addr B + 4 -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE).
Proof. intros x. rewrite B_errno, B_ctx. unfold ERRNO, CTX, CTX_SIZE, src0_tp, src0_D_malloc_context. lia. Qed.
Lemma src0_ENS : forall x, errno_addr B <= x < errno_addr B + 4 -> ~ static_owned B x.
Proof.
intros x. rewrite B_errno. unfold static_owned. cbn. unfold ERRNO, src0_tp, src0_D_malloc_lock, src0_D_libc, src0_D_got_stack_chk_guard,
src0_D_stack_chk_guard, src0_D_debruijn32, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab. lia.
Qed.
Lemma src0_ERRIMG : forall x, errno_addr B <= x < errno_addr B + 4 -> in_img B x.
Proof. intros x. rewrite B_errno. apply src0_errno_img. Qed.
Lemma src0_SNC : forall x, static_owned B x -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE).
Proof.
intros x. rewrite B_ctx. unfold static_owned. cbn. unfold CTX, CTX_SIZE, src0_D_malloc_context, src0_D_malloc_lock, src0_D_libc, src0_D_got_stack_chk_guard,
src0_D_stack_chk_guard, src0_D_debruijn32, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab. lia.
Qed.
Lemma auxv_pre_ext : forall sec lo m m',
(forall x, lo <= x < 2 ^ 63 -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x) ->
(forall x, ms_libc B + 8 <= x < ms_libc B + 16 -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x) ->
auxv_pre B sec lo m -> auxv_pre B sec lo m'.
Proof.
intros sec lo m m' Hhi Hlibc (av & ar & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
exists av, ar. repeat split; try assumption.
- intros k Hk. rewrite Hlibc by lia. apply H1. exact Hk.
- intros k Hk j Hj. rewrite Hhi by lia. apply H2; assumption.
- intros k Hk. rewrite Hhi by lia. apply H3. exact Hk.
- intros k Hk. rewrite Hhi by lia. apply H4. exact Hk.
Qed.
Ltac st_region HS i name :=
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
let r := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch r with Some ?rr =>
pose proof (st_ok_region segs E ss ms i rr HS ltac:(vm_compute; reflexivity)) as name end end.
Ltac st_chunk HS i c name :=
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
let r := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch r with Some ?rr =>
pose proof (st_ok_chunk segs E ss ms i rr c HS ltac:(vm_compute; reflexivity) ltac:(cbn; tauto)) as name;
cbn [base_val r_base] in name end end.
Ltac st_writable HS i o :=
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
let r := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch r with Some ?rr =>
apply (st_ok_writable segs E ss ms i rr o HS ltac:(vm_compute; reflexivity)) end end.
Lemma am_entry : forall L A regs mem md n mem2 (a : word) ms5,
call_pre B (MRx B) L A regs mem md -> getr regs 10 = Z_to_bv 64 n -> MMAP_THRESHOLD <= n < 2 ^ 62 ->
let E := E_entry regs A a (Z_to_bv 64 0) (fun _ => Z_to_bv 64 0) in
let sp := bv_unsigned (getr regs 2) in
(forall x, 0 <= x < 2 ^ 64 -> ~ scratch B regs x -> mem2 (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
grant_ok (Z_to_bv 64 0) md a (dlen n) = true ->
((st_seq A = 255 /\ st_ok src0segs E ss_am255 ms5) \/ (st_seq A <> 255 /\ st_ok src0segs E ss_amne ms5)) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ wr_g regs a x -> ms_mem ms5 (Z_to_bv 64 x) = apply_zeros mem2 [(a, Z_to_bv 64 (dlen n))] (Z_to_bv 64 x)) ->
midrep B (L1 L A a) (dA2 A n) (ms_mem ms5) (md1 md a (dlen n)) /\
callee_pre B (ms_regs ms5) (ms_mem ms5) AM_STACK /\
(st_init_done (dA2 A n) = false -> auxv_pre B (ly_sec L) (spZ (ms_regs ms5)) (ms_mem ms5)) /\
ms5 = mkst (ms_regs ms5) (Z_to_bv 64 src0_A_alloc_meta) (ms_mem ms5) (seg_rom src0segs) /\
getr (ms_regs ms5) 1 = Z_to_bv 64 RA_AM /\ getr (ms_regs ms5) 2 = Z_to_bv 64 (sp - 48) /\
getr (ms_regs ms5) 3 = getr regs 3 /\ getr (ms_regs ms5) 4 = Z_to_bv 64 TP /\
getr (ms_regs ms5) 8 = getr regs 10 /\ getr (ms_regs ms5) 9 = Z_to_bv 64 LOCK /\
getr (ms_regs ms5) 18 = Z_to_bv 64 (2 ^ 64 - 1) /\ getr (ms_regs ms5) 19 = Z_to_bv 64 (n + 20) /\ getr (ms_regs ms5) 20 = a /\
(forall r, 21 <= bv_unsigned r <= 27 -> getr (ms_regs ms5) r = getr regs r) /\
(forall k off (r : reg), In (off, r) [(-48, 20%bv : reg); (-40, 19%bv : reg); (-32, 18%bv : reg); (-24, 9%bv : reg); (-16, 8%bv : reg); (-8, 1%bv : reg)] ->
(k < 8)%nat -> mbyte src0segs (ms_mem ms5) (sp + off + Z.of_nat k) = Some (byte_of_word (getr regs r) (Z.of_nat k))) /\
(forall i, 0 <= i < dlen n -> mbyte src0segs (ms_mem ms5) (bv_unsigned a + i) = Some (Z_to_bv 8 0)) /\
(forall x, bv_unsigned a <= x < bv_unsigned a + dlen n -> present (ms_mem ms5) x) /\
(forall x, sp - 8192 <= x < sp -> writable_at src0segs (ms_mem ms5) x) /\
(forall x, ERRNO <= x < ERRNO + 4 -> writable_at src0segs (ms_mem ms5) x).
Proof.
intros L A regs mem md n mem2 a ms5 PRE Hn Hrange E sp FR2 GR HS5 FR5.
pose proof PRE as (MX & HW & HB & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herr & Hauxv).
pose proof (MRx_MRc _ _ _ _ _ MX) as M. pose proof (proj1 alloc_ceiling_val) as AC. pose proof (u64_range a) as Ua.
pose proof (dlen_facts n (proj1 Hrange)) as (D1 & D2 & D3 & D4 & D5).
pose proof (grant_facts B L A mem md a (dlen n) MX (conj D1 D2) GR) as (Gal & Gpos & Gceil & _ & _).
pose proof (inv_ctx HW) as (Lact & Lus & Luseq & Lbo & Uus & Uuseq & Ubo & Rseq & Rctr & _).
assert (HT : MMAP_THRESHOLD = 131052) by reflexivity. assert (PG : PGSZ = 4096) by reflexivity.
assert (Hn' : bv_unsigned (getr regs 10) = n) by (rewrite Hn; apply u64_of_Z; lia).
unfold spZ in *. fold sp in Hal, Hceil, Hsp63, Hstk.
assert (NI : forall x, bv_unsigned a <= x < bv_unsigned a + dlen n -> ~ in_img B x).
{ intros x Hx Hi. exact (new_disjoint_img B L A mem md a (dlen n) MX (dlen_pos n (proj1 Hrange)) GR x Hi Hx). }
assert (Elen : bv_unsigned (Z_to_bv 64 (dlen n)) = dlen n) by (apply u64_of_Z; lia).
assert (K : ms5 = mkst (ms_regs ms5) (Z_to_bv 64 src0_A_alloc_meta) (ms_mem ms5) (seg_rom src0segs) /\
getr (ms_regs ms5) 1 = Z_to_bv 64 RA_AM /\ getr (ms_regs ms5) 2 = Z_to_bv 64 (sp - 48) /\
getr (ms_regs ms5) 3 = getr regs 3 /\ getr (ms_regs ms5) 4 = Z_to_bv 64 TP /\
getr (ms_regs ms5) 8 = getr regs 10 /\ getr (ms_regs ms5) 9 = Z_to_bv 64 LOCK /\
getr (ms_regs ms5) 18 = Z_to_bv 64 (2 ^ 64 - 1) /\ getr (ms_regs ms5) 19 = Z_to_bv 64 (n + 20) /\ getr (ms_regs ms5) 20 = a /\
(forall r, 21 <= bv_unsigned r <= 27 -> getr (ms_regs ms5) r = getr regs r) /\
(forall k off (r : reg), In (off, r) [(-48, 20%bv : reg); (-40, 19%bv : reg); (-32, 18%bv : reg); (-24, 9%bv : reg); (-16, 8%bv : reg); (-8, 1%bv : reg)] ->
(k < 8)%nat -> mbyte src0segs (ms_mem ms5) (sp + off + Z.of_nat k) = Some (byte_of_word (getr regs r) (Z.of_nat k))) /\
(forall x, sp - 8192 <= x < sp -> writable_at src0segs (ms_mem ms5) x) /\
(forall x, ERRNO <= x < ERRNO + 4 -> writable_at src0segs (ms_mem ms5) x) /\
(forall x, bv_unsigned a <= x < bv_unsigned a + 8 -> writable_at src0segs (ms_mem ms5) x) /\
(forall k, (k < 4)%nat -> mbyte src0segs (ms_mem ms5) (CTX + 12 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (st_mmap_counter A) 4 k))) /\
mbyte src0segs (ms_mem ms5) (CTX + 912) = Some (Z_to_bv 8 (le_byte (st_seq (dA2 A n)) 1 0)) /\
(forall k, (k < 32)%nat -> mbyte src0segs (ms_mem ms5) (CTX + 848 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (nth k (st_unmap_seq (dA2 A n)) 0) 1 0)))).
{ assert (ESEQ : st_seq (dA2 A n) = (if st_seq A =? 255 then 1 else st_seq A + 1) /\
st_unmap_seq (dA2 A n) = (if st_seq A =? 255 then repeat 0 32 else st_unmap_seq A)).
{ unfold dA2, YN2c.A2, seqf, YN2c.A1. cbn [st_seq set_regions]. destruct (st_seq A =? 255); split; reflexivity. }
destruct ESEQ as [ES1 ES2].
destruct HS5 as [[Es HS] | [Ns HS]].
all: split; [exact (st_ok_mkst src0segs E _ ms5 HS eq_refl)|].
all: split; [sym_reg HS (1%bv : reg) as R; exact R|].
all: split; [sym_reg HS (2%bv : reg) as R; rewrite R; subst E; cbn [ew E_entry E_mi]; reflexivity|].
all: split; [sym_reg HS (3%bv : reg) as R; exact R|].
all: split; [sym_reg HS (4%bv : reg) as R; exact R|].
all: split; [sym_reg HS (8%bv : reg) as R; exact R|].
all: split; [sym_reg HS (9%bv : reg) as R; exact R|].
all: split; [sym_reg HS (18%bv : reg) as R; rewrite R; apply bv_eq; reflexivity|].
all: split; [sym_reg HS (19%bv : reg) as R; rewrite R; subst E; cbn [ew E_entry E_mi]; rewrite Hn'; reflexivity|].
all: split; [sym_reg HS (20%bv : reg) as R; exact R|].
all: split; [intros r Hr;
assert (Hr' : r = 21%bv \/ r = 22%bv \/ r = 23%bv \/ r = 24%bv \/ r = 25%bv \/ r = 26%bv \/ r = 27%bv)
by (destruct (Z.eq_dec (bv_unsigned r) 21) as [e1|n1]; [left; apply bv_eq; rewrite e1; reflexivity|];
destruct (Z.eq_dec (bv_unsigned r) 22) as [e2|n2]; [right; left; apply bv_eq; rewrite e2; reflexivity|];
destruct (Z.eq_dec (bv_unsigned r) 23) as [e3|n3]; [right; right; left; apply bv_eq; rewrite e3; reflexivity|];
destruct (Z.eq_dec (bv_unsigned r) 24) as [e4|n4]; [right; right; right; left; apply bv_eq; rewrite e4; reflexivity|];
destruct (Z.eq_dec (bv_unsigned r) 25) as [e5|n5]; [right; right; right; right; left; apply bv_eq; rewrite e5; reflexivity|];
destruct (Z.eq_dec (bv_unsigned r) 26) as [e6|n6]; [right; right; right; right; right; left; apply bv_eq; rewrite e6; reflexivity|];
right; right; right; right; right; right; apply bv_eq; change (bv_unsigned (27%bv : bv 5)) with 27; lia);
destruct Hr' as [->|[->|[->|[->|[->|[->| ->]]]]]];
[sym_reg HS (21%bv : reg) as R | sym_reg HS (22%bv : reg) as R | sym_reg HS (23%bv : reg) as R | sym_reg HS (24%bv : reg) as R
| sym_reg HS (25%bv : reg) as R | sym_reg HS (26%bv : reg) as R | sym_reg HS (27%bv : reg) as R]; exact R|].
all: split; [intros k off r Hin Hk;
st_region HS 1%nat RG; destruct RG as (_ & _ & _ & CH);
rewrite Forall_forall in CH; cbn [In] in Hin;
destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]]]; injection Hin as <- <-;
[ destruct (CH (mkChunk (-48) (CVal 8 (SOff 20 0))) ltac:(cbn; tauto) (Z.of_nat k) ltac:(cbn; lia)) as (b & Hb1 & Hb2)
| destruct (CH (mkChunk (-40) (CVal 8 (SOff 19 0))) ltac:(cbn; tauto) (Z.of_nat k) ltac:(cbn; lia)) as (b & Hb1 & Hb2)
| destruct (CH (mkChunk (-32) (CVal 8 (SOff 18 0))) ltac:(cbn; tauto) (Z.of_nat k) ltac:(cbn; lia)) as (b & Hb1 & Hb2)
| destruct (CH (mkChunk (-24) (CVal 8 (SOff 9 0))) ltac:(cbn; tauto) (Z.of_nat k) ltac:(cbn; lia)) as (b & Hb1 & Hb2)
| destruct (CH (mkChunk (-16) (CVal 8 (SOff 8 0))) ltac:(cbn; tauto) (Z.of_nat k) ltac:(cbn; lia)) as (b & Hb1 & Hb2)
| destruct (CH (mkChunk (-8) (CVal 8 (SOff 1 0))) ltac:(cbn; tauto) (Z.of_nat k) ltac:(cbn; lia)) as (b & Hb1 & Hb2) ];
cbn [c_off c_val cbyte base_val r_base] in Hb1, Hb2; injection Hb1 as <-;
subst E; cbn [sv_denot ew E_entry E_mi] in Hb2 |- *; fold sp in Hb2; rewrite Hb2; f_equal; f_equal;
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity |].
all: split; [intros x Hx; replace x with (sp + (x - sp)) by lia; subst E sp; st_writable HS 1%nat (x - bv_unsigned (getr regs 2)); cbn [r_wlo r_whi]; lia|].
all: split; [intros x Hx; replace x with (0 + x) by lia; st_writable HS 7%nat x; cbn [r_wlo r_whi]; unfold ERRNO, src0_tp in Hx; lia|].
all: split; [intros x Hx; replace x with (bv_unsigned a + (x - bv_unsigned a)) by lia; subst E; st_writable HS 0%nat (x - bv_unsigned a); cbn [r_wlo r_whi]; lia|].
all: split; [intros k Hk; st_chunk HS 4%nat (mkChunk (CTX + 12) (CVal 4 (SOff 33 0))) CK; rewrite <- (Z.add_0_l (CTX + 12));
apply (chunk_bytes_cval_exact src0segs E _ 0 (CTX + 12) 4 (SOff 33 0) (st_mmap_counter A) CK); [subst E; cbn [sv_denot ew E_entry E_mi]; rewrite u64_of_Z by lia; rewrite Z.add_0_r; reflexivity | lia | exact Hk] |].
-
rewrite (proj2 (Z.eqb_eq _ _) Es) in ES1, ES2. rewrite ES1, ES2. split.
+ st_chunk HS 6%nat (mkChunk (CTX + 912) (CVal 1 (SLit 1))) CK.
pose proof (chunk_bytes_cval_exact src0segs E _ 0 (CTX + 912) 1 (SLit 1) 1 CK eq_refl ltac:(lia) 0%nat ltac:(cbn; lia)) as Hb.
rewrite Z.add_0_l, Z.add_0_r in Hb. exact Hb.
+ intros k Hk. rewrite nth_repeat_lt by lia. change (le_byte 0 1 0) with 0.
assert (Hq : exists q rr, (k = 8 * q + rr)%nat /\ (rr < 8)%nat /\ (q < 4)%nat).
{ exists (Nat.div k 8), (Nat.modulo k 8). pose proof (Nat.div_mod_eq k 8). pose proof (Nat.mod_upper_bound k 8). split; [lia|]. split; [lia|].
apply Nat.Div0.div_lt_upper_bound. lia. }
destruct Hq as (q & rr & -> & Hrr & Hq).
st_region HS 5%nat RG. destruct RG as (_ & _ & _ & CH). rewrite Forall_forall in CH. cbn [base_val r_base] in CH.
assert (CK : chunk_ok src0segs E (ms_mem ms5) 0 (mkChunk (CTX + 848 + 8 * Z.of_nat q) (CVal 8 (SLit 0)))).
{ apply CH. cbn [r_chunks]. unfold CTX, src0_D_malloc_context.
destruct q as [|[|[|[|q]]]]; [right; right; right; left | right; right; left | right; left | left | lia]; reflexivity. }
pose proof (chunk_bytes_cval_exact src0segs E _ 0 _ 8 (SLit 0) 0 CK eq_refl ltac:(lia) rr ltac:(lia)) as Hb.
rewrite Z.add_0_l in Hb. replace (CTX + 848 + Z.of_nat (8 * q + rr)) with (CTX + 848 + 8 * Z.of_nat q + Z.of_nat rr) by lia. rewrite Hb.
unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
-
rewrite (proj2 (Z.eqb_neq _ _) Ns) in ES1, ES2. rewrite ES1, ES2. split.
+ st_chunk HS 6%nat (mkChunk (CTX + 912) (CVal 1 (SOff 32 1))) CK.
pose proof (chunk_bytes_cval_exact src0segs E _ 0 (CTX + 912) 1 (SOff 32 1) (st_seq A + 1) CK
ltac:(subst E; cbn [sv_denot ew E_entry E_mi]; rewrite u64_of_Z by lia; reflexivity) ltac:(lia) 0%nat ltac:(cbn; lia)) as Hb.
rewrite Z.add_0_l, Z.add_0_r in Hb. exact Hb.
+ intros k Hk. st_chunk HS 5%nat (mkChunk (CTX + 848) (CData 0 0 32)) CK. rewrite <- (Z.add_0_l (CTX + 848)). rewrite (chunk_bytes_cdata src0segs E _ 0 _ 0 32 CK k) by lia.
subst E. cbn [ed E_entry E_mi]. unfold useq_of. rewrite nth_error_map, nth_error_seq, (proj2 (Nat.ltb_lt k 32) Hk). reflexivity. }
destruct K as (Kst & K1 & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K2x & Kstk & Kws & Kwe & Kwa & Kctr & Kseq & Kuseq).
assert (ZB : forall i, 0 <= i < dlen n -> mbyte src0segs (ms_mem ms5) (bv_unsigned a + i) = Some (Z_to_bv 8 0)).
{ intros i Hi. destruct (Z_lt_le_dec i 8).
- destruct HS5 as [[_ HS]|[_ HS]];
(st_chunk HS 0%nat (mkChunk 0 (CZero 8)) CK; subst E; cbn [ew E_entry E_mi] in CK;
rewrite <- (Z.add_0_r (bv_unsigned a)); apply (chunk_bytes_czero src0segs _ _ _ 0 8 CK); lia).
- rewrite mbyte_off_img; [| lia | intros Hi2; apply (NI (bv_unsigned a + i)); [lia | apply in_img1_img; exact Hi2]].
rewrite FR5; [apply apply_zeros1_in; rewrite u64_of_Z, Elen; lia | lia |].
intros [[Hs|Hs]|[Hc|Hm]]; [unfold spZ in Hs; fold sp in Hs; lia | rewrite B_errno in Hs; apply (NI (bv_unsigned a + i)); [lia | apply src0_errno_img; exact Hs]
| apply (NI (bv_unsigned a + i)); [lia | apply (so_ctx_img _ (mc_syms _ _ _ _ _ M))]; rewrite B_ctx; unfold ctxw, CTX_SIZE in *; rewrite B_ctx in Hc; lia | lia]. }
assert (ZP : forall x, bv_unsigned a <= x < bv_unsigned a + dlen n -> present (ms_mem ms5) x).
{ intros x Hx. pose proof (ZB (x - bv_unsigned a) ltac:(lia)) as Hb. replace (bv_unsigned a + (x - bv_unsigned a)) with x in Hb by lia.
rewrite mbyte_off_img in Hb; [| lia | intros Hi2; apply (NI x); [lia | apply in_img1_img; exact Hi2]]. exists (Z_to_bv 8 0). exact Hb. }
assert (AG : forall x, 0 <= x < 2 ^ 64 -> ~ wr_g regs a x -> ~ (bv_unsigned a <= x < bv_unsigned a + dlen n) ->
ms_mem ms5 (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
{ intros x Hx Hw Hna. rewrite (FR5 x Hx Hw). rewrite apply_zeros1_out by (rewrite u64_of_Z, Elen; lia).
apply FR2; [exact Hx|]. intros Hs. apply Hw. left. exact Hs. }
split.
{
apply (midrep_after_seq B L A mem md a (dlen n) MX (dlen_pos n (proj1 Hrange)) GR (WF_ptrs_below A HW (MRx_ama _ _ _ _ _ MX)) (ms_mem ms5) (wr_g regs a)).
- exact AG.
- intros x Hw Hfs. destruct Hw as [[Hs|Hs]|[Hc|Hm]].
+ exfalso. unfold spZ in Hs. fold sp in Hs. destruct Hfs as [(rg & Hrg & Hxr) | Hst].
* pose proof (footprint_low B L A mem md rg x M Hrg Hxr). lia.
* pose proof (so_img_hi _ (mc_syms _ _ _ _ _ M) x (so_statics_img _ (mc_syms _ _ _ _ _ M) x Hst)). lia.
+ exfalso. rewrite B_errno in Hs. destruct Hfs as [Hfp | Hst].
* exact (errno_not_footprint L A mem md x M Hs Hfp).
* exact (src0_ENS x ltac:(rewrite B_errno; exact Hs) Hst).
+ exact Hc.
+ exfalso. destruct Hfs as [(rg & Hrg & Hxr) | Hst].
* exact (new_disjoint_footprint B L A mem md a (dlen n) MX (dlen_pos n (proj1 Hrange)) GR rg x Hrg Hxr ltac:(lia)).
* apply (NI x); [lia|]. apply (so_statics_img _ (mc_syms _ _ _ _ _ M)). exact Hst.
- exact ZP.
- intros k Hk. rewrite B_ctx. apply Kctr. exact Hk.
- rewrite B_ctx. change (A2 A (dlen n)) with (dA2 A n). exact Kseq.
- intros k Hk. rewrite B_ctx. change (A2 A (dlen n)) with (dA2 A n). apply Kuseq. exact Hk.
- intros c k Hc Hk Hi. destruct (tail_cell_region A HW c Hc) as (p & rg & Ep & Hr & Hkind & Hl & Ho & Hw).
rewrite Ep, loc_addr_LMem' in Hi.
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) (prid p) rg Hr Hl) as (_ & _ & _ & Himg). apply (Himg (ly_reg L (prid p) + poff p + Z.of_nat k)); [lia | exact Hi].
- exact src0_SNC. }
assert (Usp : bv_unsigned (Z_to_bv 64 (sp - 48)) = sp - 48) by (unfold ALLOC_STACK in Hceil; apply u64_of_Z; lia).
split.
{
unfold callee_pre, spZ. rewrite K1, K2, K4, B_tp, B_errno, B_segs, Usp. unfold AM_STACK, ALLOC_STACK in *.
split; [exact eq_refl|]. split; [rewrite <- Zminus_mod_idemp_l, Hal; reflexivity|]. split; [lia|]. split; [lia|].
split; [intros x Hx; apply Kws; lia|]. split; [reflexivity|]. exact Kwe. }
split.
{
intros Hid. unfold spZ. rewrite K2, Usp.
assert (Hid' : st_init_done A = false) by (rewrite <- Hid; symmetry; apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (dA2_fields A n))))))))).
apply (auxv_pre_mono B (ly_sec L) sp); [lia|].
pose proof (Hauxv Hid') as AX. unfold spZ in AX. fold sp in AX.
apply (auxv_pre_ext (ly_sec L) sp mem); [| | exact AX].
- intros x Hx. unfold mbyte. rewrite B_segs, (AG x); [reflexivity | unfold ALLOC_STACK in *; lia | | unfold ALLOC_STACK in *; lia].
intros [[Hs|Hs]|[Hc|Hm]]; [unfold spZ in Hs; fold sp in Hs; lia | rewrite B_errno in Hs; unfold ERRNO, src0_tp, ALLOC_STACK in *; lia
| unfold ctxw in Hc; rewrite B_ctx in Hc; unfold CTX, src0_D_malloc_context, ALLOC_STACK in *; lia | unfold ALLOC_STACK in *; lia].
- intros x Hx. cbn in Hx. unfold src0_D_libc in Hx. unfold mbyte. rewrite B_segs, (AG x); [reflexivity | lia | | intros Hx2; apply (NI x Hx2); apply src0_rwseg_img; lia].
intros [[Hs|Hs]|[Hc|Hm]]; [unfold spZ in Hs; fold sp in Hs; lia | rewrite B_errno in Hs; unfold ERRNO, src0_tp in *; lia
| unfold ctxw in Hc; rewrite B_ctx in Hc; unfold CTX, src0_D_malloc_context in *; lia | apply (NI x); [lia | apply src0_rwseg_img; lia]]. }
split; [exact Kst|]. split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
split; [exact K18|]. split; [exact K19|]. split; [exact K20|]. split; [exact K2x|]. split; [exact Kstk|]. split; [exact ZB|]. split; [exact ZP|].
split; [exact Kws | exact Kwe].
Qed.
Ltac bvlit := split; apply Z.leb_le; vm_compute; reflexivity.
Ltac creg := unfold callee_saved;
match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v end; lia.
Definition xr_of (regs6 : bvmap 5 word) (j : nat) : word :=
match j with
| 36 => getr regs6 1 | 37 => getr regs6 5 | 38 => getr regs6 6 | 39 => getr regs6 7
| 40 => getr regs6 11 | 41 => getr regs6 12 | 42 => getr regs6 13 | 43 => getr regs6 14
| 44 => getr regs6 15 | 45 => getr regs6 16 | 46 => getr regs6 17
| 47 => getr regs6 28 | 48 => getr regs6 29 | 49 => getr regs6 30 | 50 => getr regs6 31
| _ => Z_to_bv 64 0
end%nat.
Lemma sk_ret0 : map (fun r => (r_base r, r_wlo r, r_whi r)) (ss_mem ss_ret0) = [(Some 2%nat, -8192, 0); (None, 0, 0); (None, 0, 0); (None, ERRNO, ERRNO + 4)]
/\ map (fun r => (r_base r, r_wlo r, r_whi r)) (ss_mem ss_mun2) = [(Some 2%nat, -8192, 0); (None, 0, 0); (None, 0, 0); (None, ERRNO, ERRNO + 4)].
Proof. vm_compute. split; reflexivity. Qed.
Lemma in_wrange_ret0 : forall regs seq ctr useq a g xr rs x,
map (fun r => (r_base r, r_wlo r, r_whi r)) rs = [(Some 2%nat, -8192, 0); (None, 0, 0); (None, 0, 0); (None, ERRNO, ERRNO + 4)] ->
in_wrange (E_mi regs seq ctr useq a g xr) rs x -> scratch B regs x.
Proof.
intros regs seq ctr useq a g xr rs x Hsk Hw. apply in_wrange_list in Hw as (t & Hin & Hx). rewrite Hsk in Hin.
unfold scratch, spZ, ALLOC_STACK. rewrite B_errno. cbn [In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd base_val ew E_mi] in Hx; lia.
Qed.
Lemma layout_le_A3 : forall L A a n L3,
MMAP_THRESHOLD <= n -> layout_le (dA2 A n) (L1 L A a) L3 -> layout_le A L L3.
Proof.
intros L A a n L3 Hn (C1 & C2 & C3 & C4). pose proof (layout_le_L1 L A a (dlen n) (dlen_pos n Hn)) as (D1 & D2 & D3 & D4).
split; [congruence|]. split; [congruence|]. split; [congruence|].
intros r Hr. rewrite C4; [apply D4; exact Hr|].
pose proof (dA2_fields A n) as (_&_&_&_&_&_&_&ER&_). rewrite ER, length_app. cbn. lia.
Qed.
Lemma none_tail : forall L A regs mem md n (a : word) L3 A3 regs6 mem6 md3,
call_pre B (MRx B) L A regs mem md -> getr regs 10 = Z_to_bv 64 n -> MMAP_THRESHOLD <= n < 2 ^ 62 ->
let sp := bv_unsigned (getr regs 2) in
grant_ok (Z_to_bv 64 0) md a (dlen n) = true ->
midrep B L3 A3 mem6 md3 -> layout_le (dA2 A n) (L1 L A a) L3 -> am_frame (dA2 A n) A3 -> ub_same (dA2 A n) A3 ->
Inv [] None U0 A3 -> (forall g am, usedX [] A3 g am <-> usedX [] A g am) -> bounded A3 -> ama_ok A3 ->
(exists vm3, md3 = with_vmmaps vm3 (md1 md a (dlen n))) ->
getr regs6 10 = Z_to_bv 64 0 -> getr regs6 2 = Z_to_bv 64 (sp - 48) -> getr regs6 3 = getr regs 3 -> getr regs6 4 = Z_to_bv 64 TP ->
getr regs6 8 = getr regs 10 -> getr regs6 9 = Z_to_bv 64 LOCK -> getr regs6 18 = Z_to_bv 64 (2 ^ 64 - 1) ->
getr regs6 19 = Z_to_bv 64 (n + 20) -> getr regs6 20 = a -> (forall r, 21 <= bv_unsigned r <= 27 -> getr regs6 r = getr regs r) ->
(forall k off (r : reg), In (off, r) [(-48, 20%bv : reg); (-40, 19%bv : reg); (-32, 18%bv : reg); (-24, 9%bv : reg); (-16, 8%bv : reg); (-8, 1%bv : reg)] ->
(k < 8)%nat -> mbyte src0segs mem6 (sp + off + Z.of_nat k) = Some (byte_of_word (getr regs r) (Z.of_nat k))) ->
(forall x, sp - 8192 <= x < sp -> writable_at src0segs mem6 x) ->
(forall x, ERRNO <= x < ERRNO + 4 -> writable_at src0segs mem6 x) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ scratch B regs x -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE) -> ~ in_nonmap_region L3 A3 x ->
~ (bv_unsigned a <= x < bv_unsigned a + dlen n) -> mem6 (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
mreal src0segs (mkCfg (mkst regs6 (Z_to_bv 64 RA_AM) mem6 (seg_rom src0segs)) md3)
(IAsk (KMunmap (YN2c.r0 A) (n + IB + UNIT)) A3 (fun _ => IRet (None, dm_kill A A3)))
(fun r c' => malloc_post [] U0 A n r -> malloc_leaf B (MRx B) L A regs mem md n r c').
Proof.
intros L A regs mem md n a L3 A3 regs6 mem6 md3 PRE Hn Hrange sp GR MID3 LE3 FR3 UB3 HI3 EU3 HB3 HA3 VM3
R10 R2 R3 R4 R8 R9 R18 R19 R20 R2x STK Kws Kwe FR6.
pose proof PRE as (MX & HW & HB & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herr & Hauxv).
pose proof (MRx_MRc _ _ _ _ _ MX) as M. pose proof (proj1 alloc_ceiling_val) as AC. pose proof (u64_range a) as Ua.
pose proof (dlen_facts n (proj1 Hrange)) as (D1 & D2 & D3 & D4 & D5).
pose proof (grant_facts B L A mem md a (dlen n) MX (conj D1 D2) GR) as (Gal & Gpos & Gceil & _ & _).
assert (HT : MMAP_THRESHOLD = 131052) by reflexivity. assert (PG : PGSZ = 4096) by reflexivity. rewrite PG in Gal.
assert (Hn' : bv_unsigned (getr regs 10) = n) by (rewrite Hn; apply u64_of_Z; lia).
unfold spZ in *. fold sp in Hal, Hceil, Hsp63, Hstk. unfold ALLOC_STACK in Hceil, Hstk.
destruct (mid_md _ _ _ _ _ MID3) as (Hh3 & Hlz3 & Hmat3).
assert (NI : forall x, bv_unsigned a <= x < bv_unsigned a + dlen n -> ~ in_img B x).
{ intros x Hx Hi. exact (new_disjoint_img B L A mem md a (dlen n) MX (dlen_pos n (proj1 Hrange)) GR x Hi Hx). }
assert (Haimg : bv_unsigned a + 131072 <= 0x1f000 \/ 0x51000 <= bv_unsigned a).
{ destruct (Z_lt_le_dec (bv_unsigned a) 0x51000); [left|right; lia].
destruct (Z_lt_le_dec 0x1f000 (bv_unsigned a + 131072)); [|lia]. exfalso.
apply (NI (Z.max (bv_unsigned a) 0x1f000)); [lia|]. apply src0_rwseg_img. lia. }
set (E := E_mi regs (st_seq A) (st_mmap_counter A) (useq_of A) a (Z_to_bv 64 0) (xr_of regs6)).
assert (SV : forall off (r : reg), In (off, r) [(-48, 20%bv : reg); (-40, 19%bv : reg); (-32, 18%bv : reg); (-24, 9%bv : reg); (-16, 8%bv : reg); (-8, 1%bv : reg)] ->
word_at src0segs mem6 (sp - - off) (getr regs r)).
{ intros off r Hin k Hk. replace (sp - - off + Z.of_nat k) with (sp + off + Z.of_nat k) by lia. apply STK; assumption. }
assert (HS6 : st_ok src0segs E ss_ret0 (mkst regs6 (Z_to_bv 64 RA_AM) mem6 (seg_rom src0segs))).
{ subst E. apply (st_ok_ret0 regs (st_seq A) (st_mmap_counter A) (useq_of A) a (Z_to_bv 64 0) (xr_of regs6) regs6 mem6).
- repeat split; reflexivity.
- exact R2. - exact R3. - exact R4. - exact R8. - exact R9. - exact R18.
- rewrite R19, Hn'. reflexivity.
- exact R20.
- apply R2x; bvlit. - apply R2x; bvlit. - apply R2x; bvlit. - apply R2x; bvlit. - apply R2x; bvlit. - apply R2x; bvlit. - apply R2x; bvlit.
- fold sp. lia.
- exact Kws.
- exact (SV (-48) 20%bv ltac:(cbn; tauto)).
- exact (SV (-40) 19%bv ltac:(cbn; tauto)).
- exact (SV (-32) 18%bv ltac:(cbn; tauto)).
- exact (SV (-24) 9%bv ltac:(cbn; tauto)).
- exact (SV (-16) 8%bv ltac:(cbn; tauto)).
- exact (SV (-8) 1%bv ltac:(cbn; tauto)).
- intros k Hk. rewrite <- B_lock. apply (st_lock _ _ (mid_statics _ _ _ _ _ MID3)). exact Hk.
- rewrite <- B_nl. apply (st_needlocks _ _ (mid_statics _ _ _ _ _ MID3)).
- exact Kwe.
- rewrite Hn'. lia.
- lia.
- exact R10. }
destruct (D2_pack B L A mem md a n L3 A3 mem6 md3 sp mem6) as (_ & _ & _ & L3r0 & L3old & A3r0 & MAPS & UB3A); try assumption;
try (unfold ALLOC_STACK; lia).
1-4: first [exact src0_ENC | exact src0_ENS | exact src0_ERRIMG | exact src0_SNC].
1: exact (fun x _ _ _ => eq_refl).
apply mreal_IAsk.
eapply (SR_run_ecall src0segs src0tbl src0tbl_ok FUEL E ss_ret0 ss_mun); [exact Hh3 | exact Hlz3 | exact HS6 | apply run_ret0 |].
intros ms7 HS7 HF7. apply SR_ret.
destruct (st_ok_ecall_shape src0segs E ss_mun ms7 HS7 eq_refl) as (regs7 & mem7 & -> & Hregs7 & Hmem7 & HG7). clear HS7.
cbn [ms_mem pend_at] in HF7. rewrite ss_mun_pc.
assert (A0 : getr regs7 10 = a).
{ rewrite (Hregs7 10%bv). eval_sr_get. subst E; cbn [sv_denot ew E_mi]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. }
assert (A1 : getr regs7 11 = Z_to_bv 64 (n + 20)).
{ rewrite (Hregs7 11%bv). eval_sr_get. subst E; cbn [sv_denot ew E_mi]. rewrite Hn'. reflexivity. }
assert (PRZ : page_round_up_Z (n + 20) = dlen n).
{ unfold dlen, dm_len, page_round_up_Z, page_round, page_size. replace (n + IB + UNIT) with (n + 20) by (unfold IB, UNIT; lia). reflexivity. }
assert (PR : page_round_up (Z_to_bv 64 (n + 20)) = Z_to_bv 64 (dlen n)).
{ unfold page_round_up. rewrite u64_of_Z by lia. rewrite PRZ. reflexivity. }
assert (Elen : bv_unsigned (Z_to_bv 64 (dlen n)) = dlen n) by (apply u64_of_Z; lia).
eapply (knode_munmap src0segs regs7 _ mem7 (seg_rom src0segs) md3 A3 (YN2c.r0 A) (n + IB + UNIT)).
- exact Hh3. - exact Hlz3.
- rewrite (Hregs7 17%bv). vm_compute. reflexivity.
- rewrite A0. unfold page_size. exact Gal.
- rewrite A1. intros EQ. apply (f_equal bv_unsigned) in EQ. rewrite !u64_of_Z in EQ by lia. lia.
- rewrite A0, A1, u64_of_Z by lia. rewrite PRZ. unfold TASK_SIZE. pose proof (proj1 alloc_ceiling_val). lia.
- rewrite A0, A1, PR. unfold map_has. apply existsb_exists. exists (a, Z_to_bv 64 (dlen n)). split; [exact MAPS|]. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity.
-
unfold munmap_nx. rewrite A0, A1, PR. apply mreal_IRet.
pose proof (st_ok_mun2 regs (st_seq A) (st_mmap_counter A) (useq_of A) a (Z_to_bv 64 0) (xr_of regs6) regs7 mem7 a (Z_to_bv 64 (dlen n))
Hregs7 Hmem7 HG7 ltac:(fold sp; lia) ltac:(rewrite Elen; lia) ltac:(rewrite Elen; lia) ltac:(rewrite Elen; lia)) as HS8.
fold E in HS8.
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E ss_mun2 ss_none_end);
[rewrite munmap_model_halted; exact Hh3 | apply munmap_model_no_lazy; exact Hlz3 | exact HS8 | apply run_mun2 |].
intros ms8 HS9 HF9. cbn [ms_mem] in HF9.
eapply (SR_final_ret E ss_none_end ms8); [exact HS9 | reflexivity | reflexivity | vm_compute; reflexivity | subst E; exact Hret
| rewrite munmap_model_halted; exact Hh3 | apply munmap_model_no_lazy; exact Hlz3 |].
intros MP. subst E. cbn [ew E_mi].
set (mem8 := ms_mem ms8). set (md4 := munmap_model a (Z_to_bv 64 (dlen n)) md3).
assert (FR8 : forall x, 0 <= x < 2 ^ 64 -> ~ scratch B regs x -> ~ (bv_unsigned a <= x < bv_unsigned a + dlen n) -> mem8 (Z_to_bv 64 x) = mem6 (Z_to_bv 64 x)).
{ intros x Hx Hns Hna. subst mem8.
rewrite (HF9 (Z_to_bv 64 x)) by (rewrite u64_of_Z by exact Hx; intros W; apply Hns; eapply (in_wrange_ret0 regs); [apply (proj2 sk_ret0) | exact W]).
cbn [ms_mem mkst]. rewrite apply_unmaps1_out by (rewrite u64_of_Z, Elen; lia).
rewrite (HF7 (Z_to_bv 64 x)) by (rewrite u64_of_Z by exact Hx; intros W; apply Hns; eapply (in_wrange_ret0 regs); [apply (proj1 sk_ret0) | exact W]).
reflexivity. }
destruct (D2_pack B L A mem md a n L3 A3 mem6 md3 sp mem8) as (MX4 & UB4 & VM4 & _); try assumption; try (unfold ALLOC_STACK; lia).
1-4: first [exact src0_ENC | exact src0_ENS | exact src0_ERRIMG | exact src0_SNC].
exists L3, (ms_regs ms8), mem8, md4. split; [reflexivity|]. split.
2:{ cbn [fst snd]. split; [pose proof (st_ok_reg src0segs _ _ _ 10 HS9) as R; rewrite R; vm_compute; reflexivity | exact UB4]. }
assert (OWNA : forall x, ms_ctx B <= x < ms_ctx B + CTX_SIZE -> owned B L A x).
{ intros x Hx. left. split.
- exists (LCtx 0, CTX_SIZE). split; [left; reflexivity|]. cbn [fst snd loc_addr]. rewrite (mc_ctx _ _ _ _ _ M). lia.
- intros ([bp bn] & Hb & Hbx). cbn [fst snd] in Hbx.
destruct (blocks_facts B L A mem md bp bn (x - ptr_addr L bp) M Hb ltac:(unfold ptr_addr; lia)) as (_ & Hlo & Hhi & _).
destruct (block_region A bp bn HW Hb) as (k & o & rg & -> & Hr & Hk & Hl & Ho & Hbn & Hlen & _).
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) k rg Hr Hl) as (_ & _ & _ & Himg).
apply (Himg x); [unfold ptr_addr in *; cbn [loc_addr] in *; lia|]. apply (so_ctx_img _ (mc_syms _ _ _ _ _ M)). exact Hx. }
assert (NONMAP : forall x, in_nonmap_region L3 A3 x -> 4096 <= x < alloc_ceiling /\ ~ in_img B x).
{ intros x ((k & rg & Hk & Hl & Hkind & Hx) & _). pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID3) k rg Hk Hl) as (_ & Q1 & Q2 & Q3).
pose proof (reg_lo_le rg). split; [lia|]. apply Q3. lia. }
assert (FRall : forall x, 0 <= x < 2 ^ 64 -> (alloc_ceiling <= x \/ in_img B x) -> ~ owned B L A x -> ~ scratch B regs x ->
mem8 (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
{ intros x Hx Hhi Hno Hns. rewrite FR8; [| exact Hx | exact Hns | intros Hin; apply (NI x Hin); destruct Hhi as [Hhi|Hhi]; [lia | exact Hhi]].
apply FR6; [exact Hx | exact Hns | intros Hc; apply Hno; apply OWNA; exact Hc | intros Hnm; destruct (NONMAP x Hnm) as [Q1 Q2]; destruct Hhi as [Hhi|Hhi]; [lia | exact (Q2 Hhi)]
| intros Hin; apply (NI x Hin); destruct Hhi as [Hhi|Hhi]; [lia | exact Hhi]]. }
split; [exact MX4|]. split; [destruct MP as [MP _]; exact MP|]. split; [apply kill_bounded; exact HB3|].
split; [exact (layout_le_A3 L A a n L3 (proj1 Hrange) LE3)|].
split.
{ intros p k Hin _. destruct (block_region A p k HW Hin) as (kk & o & rg & -> & Hr & _). unfold ptr_addr. cbn [loc_addr].
rewrite L3old; [reflexivity|]. exact (region_of_lt A kk rg Hr). }
split; [eapply (regs_preserved_sym regs); [apply (proj1 none_end_checks) | exact HS9 | exact Htp]|].
split; [exact VM4|].
split.
{ intros x Hhi Hno _ Hns _.
assert (Hx : 0 <= x < 2 ^ 64) by (destruct Hhi as [Hhi|Hhi]; [lia | apply src0_img_range in Hhi; lia]).
unfold mbyte, writable_at, wview. rewrite B_segs. rewrite (FRall x Hx ltac:(destruct Hhi as [Hhi|Hhi]; [left; lia | right; exact Hhi]) Hno Hns). tauto. }
split.
{ intros p k i Hin _ Hi. destruct (blocks_facts B L A mem md p k i M Hin Hi) as (_ & Hlo & Hhi & Hno).
destruct (block_region A p k HW Hin) as (kk & o & rg & -> & Hr & Hkind & Hl & Ho & _ & Hlen & _).
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) kk rg Hr Hl) as (_ & _ & _ & Himg).
unfold ptr_addr in *. cbn [loc_addr] in *.
unfold mbyte. rewrite B_segs. rewrite FR8; [| lia | intros [Hs|Hs]; [unfold spZ, ALLOC_STACK in Hs; fold sp in Hs; lia | rewrite B_errno in Hs; apply (Himg (ly_reg L kk + o + i)); [lia | apply src0_errno_img; exact Hs]]
| intros Hin2; exact (new_disjoint_footprint B L A mem md a (dlen n) MX (dlen_pos n (proj1 Hrange)) GR (LMem (SP kk 0), rg_len rg) (ly_reg L kk + o + i)
(footprint_region_In A kk rg Hr Hkind Hl) ltac:(cbn [fst snd loc_addr]; lia) Hin2)].
rewrite FR6; [reflexivity | lia | | | |].
- intros [Hs|Hs]; [unfold spZ, ALLOC_STACK in Hs; fold sp in Hs; lia | rewrite B_errno in Hs; apply (Himg (ly_reg L kk + o + i)); [lia | apply src0_errno_img; exact Hs]].
- intros Hc. apply (Himg (ly_reg L kk + o + i)); [lia|]. apply (so_ctx_img _ (mc_syms _ _ _ _ _ M)). exact Hc.
- intros [_ NM]. apply NM. pose proof (old_region_A3 A n Hrange A3 FR3 kk rg Hr Hkind) as Hr3.
exists kk, rg. split; [exact Hr3|]. split; [exact Hl|]. split; [exact Hkind|].
rewrite (L3old kk (region_of_lt A kk rg Hr)). lia.
- intros Hin2. exact (new_disjoint_footprint B L A mem md a (dlen n) MX (dlen_pos n (proj1 Hrange)) GR (LMem (SP kk 0), rg_len rg) (ly_reg L kk + o + i)
(footprint_region_In A kk rg Hr Hkind Hl) ltac:(cbn [fst snd loc_addr]; lia) Hin2). }
intros x Hsx. eapply (scratch_writable_sym regs); [apply (proj2 none_end_checks) | exact HS9 |].
unfold scratch, spZ, ALLOC_STACK in Hsx. rewrite B_errno in Hsx. exact Hsx.
Qed.
End f.
End e.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
