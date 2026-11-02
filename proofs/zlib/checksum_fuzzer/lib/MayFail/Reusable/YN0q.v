(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0q.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO12.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN26.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2r.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (L : layout) (A : astate).
Variables (mem : word -> option byte) (md : Model).
Hypothesis HI : Inv X R U A.
Hypothesis HL : layout_ok L A.
Hypothesis SO : syms_ok B1.
Hypothesis Hctx : ly_ctx L = CTX.
Hypothesis MR : memrepX B1 X L A mem.
Hypothesis LG : ledger_ok B1 L A md.
Lemma key_facts q x : MT A q = Some x ->
4096 <= ptr_addr L q /\ ptr_addr L q + 40 <= alloc_ceiling /\ ptr_addr L q mod 8 = 0 /\
(forall y, ptr_addr L q <= y < ptr_addr L q + 40 -> ~ in_img B1 y) /\
(exists a, In a (st_areas A) /\ In (LMem a, PGSZ) (footprint A) /\ loc_addr L (LMem a) <= ptr_addr L q /\ ptr_addr L q + 40 <= loc_addr L (LMem a) + PGSZ).
Proof.
intros Mq.
pose proof (inv_keys HI) as (NDk & KP & _ & _ & Hcnt).
destruct (KP q (MT_Some_In_keys _ _ _ Mq)) as (a & k & Ha & Hk2 & Eq).
assert (Hk' : 0 <= k < METAS_PER_AREA) by (unfold handed in Hk2; destruct (sptr_eqb a _); lia).
destruct (proj1 (proj2 (inv_areas HI)) a Ha) as (ra & oa & rga & Ea & Hoa & Hoa2 & Hra & Hral & Hoalen & _).
destruct (lg_placed _ _ _ _ LG _ _ Hra Hral) as (Aal & A4096 & Aceil & Aimg).
assert (EQ : ptr_addr L q = ly_reg L ra + oa + AREA_HDR + META_SIZE * k).
{ unfold ptr_addr, loc_addr. rewrite Eq, Ea. cbn [padd]. lia. }
unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. pose proof (proj1 alloc_ceiling_val).
repeat match goal with |- _ /\ _ => split end; try lia.
- rewrite EQ.
pose proof (proj2 (Z.div_exact (ly_reg L ra) 4096 ltac:(lia)) Aal) as E1. pose proof (proj2 (Z.div_exact oa 4096 ltac:(lia)) Hoa) as E2.
replace (ly_reg L ra + oa + 24 + 40 * k) with ((512 * (ly_reg L ra / 4096) + 512 * (oa / 4096) + 3 + 5 * k) * 8) by lia.
apply Z_mod_mult.
- intros y Hy. apply Aimg. lia.
- exists a. split; [exact Ha|]. split; [right; apply in_app_iff; left; apply in_map_iff; exists a; auto|].
rewrite Ea. cbn [loc_addr]. lia.
Qed.
Lemma key_cell q x c : MT A q = Some x -> In c (meta_slot_cells q (Some x)) -> cell_mem B1 L mem c.
Proof.
intros Mq Hc. apply (CELL X L A mem MR). unfold imageX. apply in_app_iff. right. apply in_app_iff. left.
exact (slot_cells_in_areas X R U A HI q x c Mq Hc).
Qed.
Lemma key_old_cell q x c : MT A q = Some x -> In c (meta_slot_cells q (Some x)) -> In c (imageX X A ++ tail_cellsX X A).
Proof.
intros Mq Hc. apply in_app_iff. left. unfold imageX. apply in_app_iff. right. apply in_app_iff. left.
exact (slot_cells_in_areas X R U A HI q x c Mq Hc).
Qed.
Lemma key_present q x y : MT A q = Some x -> ptr_addr L q <= y < ptr_addr L q + 40 -> present mem y.
Proof.
intros Mq Hy. destruct (key_facts q x Mq) as (_ & _ & _ & _ & a & Ha & Hfa & Q1 & Q2).
apply (proj1 (Forall_forall _ _) (proj2 (proj2 MR)) _ Hfa). cbn [fst snd]. unfold PGSZ in *. lia.
Qed.
Lemma free_meta_bytes q pr nx : MT A q = Some (MFree pr nx) ->
bytes_are mem (ptr_addr L q + 0) 8 (optrZ L pr) /\ bytes_are mem (ptr_addr L q + 8) 8 (optrZ L nx) /\
bytes_are mem (ptr_addr L q + 16) 8 0 /\ bytes_are mem (ptr_addr L q + 24) 4 0 /\
bytes_are mem (ptr_addr L q + 28) 4 0 /\ bytes_are mem (ptr_addr L q + 32) 8 0.
Proof.
intros Mq.
assert (BY : forall dd w val, match val with VLo5 _ => False | _ => True end -> In (MCell (LMem (padd q dd)) w val) (meta_slot_cells q (Some (MFree pr nx))) ->
bytes_are mem (ptr_addr L q + dd) w (sval_num L val)).
{ intros dd w val Hv Hc kk Hkk. pose proof (key_cell q _ _ Mq Hc) as C. unfold cell_mem in C. cbn [mc_val mc_loc mc_w] in C.
rewrite loc_addr_padd in C. destruct val; first [exact (C kk Hkk) | destruct Hv]. }
repeat match goal with |- _ /\ _ => split end.
- pose proof (BY 0 8%nat (optr pr) ltac:(destruct pr; exact I) ltac:(cbn; tauto)) as B0. unfold optrZ. destruct pr; exact B0.
- pose proof (BY 8 8%nat (optr nx) ltac:(destruct nx; exact I) ltac:(cbn; tauto)) as B0. unfold optrZ. destruct nx; exact B0.
- exact (BY 16 8%nat (VZ 0) I ltac:(cbn; tauto)).
- exact (BY 24 4%nat (VZ 0) I ltac:(cbn; tauto)).
- exact (BY 28 4%nat (VZ 0) I ltac:(cbn; tauto)).
- exact (BY 32 8%nat (VZ 0) I ltac:(cbn; tauto)).
Qed.
Lemma ctx_fmh_cell : bytes_are mem (CTX + 16) 8 (optrZ L (st_free_meta_head A)).
Proof.
assert (Hc : In (MCell (LCtx CTX_free_meta_head) 8 (optr (st_free_meta_head A))) (ctx_cells A)) by (unfold ctx_cells; apply in_app_iff; left; cbn; tauto).
pose proof (CELL X L A mem MR _ ltac:(unfold imageX; apply in_app_iff; left; exact Hc)) as C.
unfold cell_mem in C. cbn [mc_val mc_loc mc_w loc_addr] in C. rewrite Hctx in C. unfold CTX_free_meta_head in C.
intros kk Hkk. destruct (st_free_meta_head A) as [q|]; cbn [optr optrZ sval_num] in *; exact (C kk Hkk).
Qed.
Lemma keys_apart p q xp xq : MT A p = Some xp -> MT A q = Some xq -> p <> q ->
ptr_addr L p + 40 <= ptr_addr L q \/ ptr_addr L q + 40 <= ptr_addr L p.
Proof. intros Mp Mq Hne. exact (metas_apart X R U A L p q xp xq HI HL Mp Mq Hne). Qed.
End d.
Lemma ledger_ok_same' L A1 A2 md : ledger_ok B1 L A1 md ->
st_regions A2 = st_regions A1 -> st_brk A2 = st_brk A1 -> ledger_ok B1 L A2 md.
Proof.
intros G ER EB.
assert (RO : forall k, region_of A2 k = region_of A1 k) by (intros k; unfold region_of; rewrite ER; reflexivity).
assert (NS : nslots A2 = nslots A1) by (unfold nslots; rewrite ER; reflexivity).
assert (LBy : live_bytes A2 = live_bytes A1) by (unfold live_bytes; rewrite ER; reflexivity).
split; try (exact (lg_reserved _ _ _ _ G) || exact (lg_limit _ _ _ _ G) || exact (lg_brk0 _ _ _ _ G)).
- intros k rg Hk. rewrite RO in Hk. exact (lg_maps _ _ _ _ G k rg Hk).
- intros k rg off Hk. rewrite RO in Hk. exact (lg_noaccess _ _ _ _ G k rg off Hk).
- rewrite EB. exact (lg_brk _ _ _ _ G).
- intros k rg Hk. rewrite RO in Hk. exact (lg_placed _ _ _ _ G k rg Hk).
- rewrite NS. exact (lg_count _ _ _ _ G).
- rewrite LBy. exact (lg_sizes _ _ _ _ G).
- rewrite LBy. exact (lg_backing _ _ _ _ G).
-   exact (lg_ceil _ _ _ _ G).
Qed.
Lemma layout_ok_same' L A1 A2 : layout_ok L A1 -> st_regions A2 = st_regions A1 -> footprint A2 = footprint A1 -> layout_ok L A2.
Proof.
intros (Y1 & Y2 & Y3 & Y4) ER EF. split; [exact Y1|]. split; [|rewrite EF; auto].
intros k rg Hk. unfold region_of in Hk. rewrite ER in Hk. exact (Y2 k rg Hk).
Qed.
Lemma alloc_owned_same L A1 A2 a : footprint A2 = footprint A1 -> user_blocks A2 = user_blocks A1 ->
alloc_owned L A2 a -> alloc_owned L A1 a.
Proof.
intros EF EU [HF HU]. unfold alloc_owned, in_footprint, in_user_block in *. rewrite EF in HF. rewrite EU in HU. exact (conj HF HU).
Qed.
Lemma footprint_regions_areas A1 A2 : st_regions A2 = st_regions A1 -> st_areas A2 = st_areas A1 -> footprint A2 = footprint A1.
Proof. intros ER EA. unfold footprint, region_of. rewrite ER, EA. reflexivity. Qed.
Lemma regs_lit_nth l n : (n < 32)%nat ->
nth n (regs_lit l) (SLit 0) =
match find (fun p => Nat.eqb (fst p) n) l with
| Some (_, z) => SLit z
| None => if Nat.eqb n 0 then SLit 0 else SOff n 0
end.
Proof.
intros Hn. unfold regs_lit.
set (f := fun i : nat => match find (fun p : nat * Z => Nat.eqb (fst p) i) l with Some (_, z) => SLit z | None => if Nat.eqb i 0 then SLit 0 else SOff i 0 end).
change (nth n (map f (seq 0 32)) (SLit 0) = f n).
rewrite (nth_indep _ (SLit 0) (f 32%nat)) by (rewrite length_map, length_seq; exact Hn).
rewrite map_nth, seq_nth by exact Hn. reflexivity.
Qed.
Lemma regs_ok_lit xv l regs :
(forall n, (1 <= n <= 31)%nat ->
match find (fun p => Nat.eqb (fst p) n) l with
| Some (_, z) => getr regs (nat_to_reg n) = Z_to_bv 64 z
| None => getr regs (nat_to_reg n) = Z_to_bv 64 (xv n)
end) ->
regs_ok (EV xv) (regs_lit l) regs.
Proof.
intros H r. unfold sr_get. pose proof (u5_range r) as Hr. destruct (bv_eqb r 0) eqn:E.
- unfold getr. rewrite E. reflexivity.
- assert (Hr0 : bv_unsigned r <> 0).
{ intros Z0. assert (r = 0%bv) as -> by (apply bv_eq; exact Z0). rewrite bv_eqb_refl in E. discriminate. }
unfold ridx. rewrite regs_lit_nth by lia.
specialize (H (Z.to_nat (bv_unsigned r)) ltac:(lia)). rewrite nat_to_reg_ridx in H.
destruct (find _ l) as [[k z]|].
+ rewrite H. reflexivity.
+ replace (Nat.eqb (Z.to_nat (bv_unsigned r)) 0) with false by (symmetry; apply Nat.eqb_neq; lia).
cbn [sv_denot EV ew]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H.
Qed.
Lemma chunk_bytes xv m base off (w : N) e v :
chunk_ok src0segs (EV xv) m base (mkChunk off (CVal w e)) ->
bv_unsigned (sv_denot (EV xv) e) = v -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
bytes_are m (base + off) (N.to_nat w) v.
Proof.
intros Hc Hv Hr k Hk. destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (bb & Eb & Mb). cbn [c_off c_val cbyte] in Eb, Mb.
rewrite Mb. injection Eb as <-. f_equal. unfold byte_of_word, le_byte. rewrite Hv, Z_to_bv8_mod. f_equal. rewrite N_nat_Z. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma SR_nt_ret' E ss ms md k Q :
st_ok src0segs E ss ms -> ss_resv ss = None -> ss_pc ss = NT_RET ->
sr_get (ss_regs ss) 1 = SOff k 0 -> YK0s.ret_ok (ew E k) ->
m_halted md = None -> m_vm_lazy md = [] ->
Q (mkCfg (mkst (ms_regs ms) (ew E k) (ms_mem ms) (seg_rom src0segs)) md) ->
SR src0segs (mkCfg ms md) Q.
Proof.
intros HS Hrv Hpc Hra Hret Hh Hlz HQ.
pose proof (st_ok_reg src0segs E ss ms 1 HS) as R1. rewrite Hra in R1. cbn [sv_denot] in R1.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned in R1.
rewrite (st_ok_mkst src0segs E ss ms HS Hrv). rewrite Hpc.
eapply SR_step; [exact Hh | exact Hlz | reflexivity | |].
- eapply step_jalr_x0; [apply fetch_nt_ret | reflexivity | apply decode_ret | exact R1].
- cbn [ms_regs ms_mem mkst]. change (bv_signed (0%bv : bv 12)) with 0. unfold YK0s.ret_ok in Hret. rewrite Hret.
apply SR_ret. exact HQ.
Qed.
Definition vF (fc : fcase) : fvar := match fc with FC0 => F0 | FC1a _ _ => F1a | FC1b _ _ _ _ => F1b end.
Definition sF (g : sptr) (s : astate) (fc : fcase) : astate :=
match fc with
| FC0 => A_F0 g s
| FC1a h hnx => A_F1a g s h
| FC1b h hp hnx hpp => A_F1b g s h hp hnx hpp
end.
Definition fc_h (g : sptr) (fc : fcase) : sptr := match fc with FC0 => g | FC1a h _ => h | FC1b h _ _ _ => h end.
Definition fc_hp (g : sptr) (fc : fcase) : sptr := match fc with FC0 => g | FC1a h _ => h | FC1b _ hp _ _ => hp end.
Lemma free_meta_eval Y s g fc : fcase_facts Y s g fc -> free_meta g s = IRet (tt, sF g s fc).
Proof.
destruct fc as [|h hnx|h hp hnx hpp]; cbn [fcase_facts sF].
- intros Hh. apply free_meta_F0. exact Hh.
- intros (Hh & Mh & _ & Hhg). apply (free_meta_F1a g s h h hnx Hhg Mh Hh eq_refl).
- intros (Hh & Mh & _ & Hhg & Hph & Hpg & Mhp & _). apply (free_meta_F1b g s h hp hnx hpp Hhg Mh Mhp Hh Hph Hpg).
Qed.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
