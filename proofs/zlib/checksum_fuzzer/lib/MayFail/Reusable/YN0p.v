(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0p.v, with its module paths changed. *)
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (L : layout) (A : astate).
Variables (mem : word -> option byte) (md : Model).
Hypothesis HI : Inv X R U A.
Hypothesis HL : layout_ok L A.
Hypothesis SO : syms_ok B1.
Hypothesis Hctx : ly_ctx L = CTX.
Hypothesis MR : memrepX B1 X L A mem.
Hypothesis ST : statics_ok B1 mem.
Hypothesis LG : ledger_ok B1 L A md.
Lemma meta_facts q aq : usedX X A q aq ->
4096 <= ptr_addr L q /\ ptr_addr L q + 40 <= alloc_ceiling /\ ptr_addr L q mod 8 = 0 /\
(forall x, ptr_addr L q <= x < ptr_addr L q + 40 -> ~ in_img B1 x) /\
(exists a, In a (st_areas A) /\ In (LMem a, PGSZ) (footprint A) /\ loc_addr L (LMem a) <= ptr_addr L q /\ ptr_addr L q + 40 <= loc_addr L (LMem a) + PGSZ).
Proof.
intros Huq.
pose proof (usedX_MT _ _ _ _ Huq) as [Mq _].
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
- intros x Hx. apply Aimg. lia.
- exists a. split; [exact Ha|]. split; [right; apply in_app_iff; left; apply in_map_iff; exists a; auto|].
rewrite Ea. cbn [loc_addr]. lia.
Qed.
Lemma CELL c : In c (imageX X A) -> cell_mem B1 L mem c.
Proof. intros Hc. exact (proj1 (Forall_forall _ _) (proj1 MR) _ Hc). Qed.
Lemma meta_cell q aq c : usedX X A q aq -> In c (meta_slot_cells q (Some (MUsed aq))) -> cell_mem B1 L mem c.
Proof.
intros Huq Hc. apply CELL. unfold imageX. apply in_app_iff. right. apply in_app_iff. left.
exact (meta_cells_in_areas X R U A HI q aq c (proj1 (usedX_MT _ _ _ _ Huq)) Hc).
Qed.
Lemma ctx_active_cell k : (k < 48)%nat ->
bytes_are mem (CTX + 80 + 8 * Z.of_nat k) 8 (optrZ L (nth k (st_active A) None)).
Proof.
intros Hk. assert (Hc : In (MCell (LCtx (CTX_active + 8 * Z.of_nat k)) 8 (optr (nth k (st_active A) None))) (ctx_cells A)).
{ unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia]. }
pose proof (CELL _ ltac:(unfold imageX; apply in_app_iff; left; exact Hc)) as C.
unfold cell_mem in C. cbn [mc_val mc_loc mc_w loc_addr] in C. rewrite Hctx in C. unfold CTX_active in C.
intros kk Hkk. destruct (nth k (st_active A) None) as [q|]; cbn [optr optrZ sval_num] in *;
(etransitivity; [|exact (C kk Hkk)]; unfold ptr_addr; f_equal; lia).
Qed.
Lemma ctx_usage_cell k : (k < 48)%nat ->
bytes_are mem (CTX + 464 + 8 * Z.of_nat k) 8 (nth k (st_usage A) 0).
Proof.
intros Hk. assert (Hc : In (MCell (LCtx (CTX_usage + 8 * Z.of_nat k)) 8 (VZ (nth k (st_usage A) 0))) (ctx_cells A)).
{ unfold ctx_cells. rewrite !in_app_iff. right; right; left. apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia]. }
pose proof (CELL _ ltac:(unfold imageX; apply in_app_iff; left; exact Hc)) as C.
unfold cell_mem in C. cbn [mc_val mc_loc mc_w loc_addr sval_num] in C. rewrite Hctx in C. unfold CTX_usage in C.
intros kk Hkk. etransitivity; [|exact (C kk Hkk)]. f_equal. lia.
Qed.
Lemma ctx_bounces_cell k : (k < 32)%nat ->
bytes_are mem (CTX + 880 + Z.of_nat k) 1 (nth k (st_bounces A) 0).
Proof.
intros Hk. assert (Hc : In (MCell (LCtx (CTX_bounces + Z.of_nat k)) 1 (VZ (nth k (st_bounces A) 0))) (ctx_cells A)).
{ unfold ctx_cells. rewrite !in_app_iff. right; right; right; right. apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia]. }
pose proof (CELL _ ltac:(unfold imageX; apply in_app_iff; left; exact Hc)) as C.
unfold cell_mem in C. cbn [mc_val mc_loc mc_w loc_addr sval_num] in C. rewrite Hctx in C. unfold CTX_bounces in C.
intros kk Hkk. etransitivity; [|exact (C kk Hkk)]. f_equal. lia.
Qed.
Lemma ctx_writable x : CTX <= x < CTX + CTX_SIZE -> writable_at src0segs mem x.
Proof. intros Hx. exact (proj1 (so_ctx_rw _ SO mem x Hx)). Qed.
Lemma ctx_img x : CTX <= x < CTX + CTX_SIZE -> in_img1 x.
Proof. unfold CTX, src0_D_malloc_context, CTX_SIZE, in_img1. lia. Qed.
Lemma meta_present q aq x : usedX X A q aq -> ptr_addr L q <= x < ptr_addr L q + 40 -> present mem x.
Proof.
intros Huq Hx. destruct (meta_facts q aq Huq) as (_ & _ & _ & _ & a & Ha & Hfa & Q1 & Q2).
apply (proj1 (Forall_forall _ _) (proj2 (proj2 MR)) _ Hfa). cbn [fst snd]. unfold PGSZ in *. lia.
Qed.
Lemma tq_bytes sc : 0 <= sc < 48 -> bytes_are mem (TBL + 2 * sc) 2 (scl_of sc).
Proof.
intros Hsc. pose proof SO as SO'.
assert (Escl : scl_of (sc) = znth (sc) size_classes) by (unfold scl_of; replace (sc <? 48) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
pose proof (scl_range (sc) Hsc) as SR. rewrite Escl.
destruct (so_size_classes _ SO' (Z.to_nat (sc)) ltac:(lia)) as (lo & hi & Hlo & Hhi & Hsum). rewrite Z2Nat.id in Hlo, Hhi by lia.
pose proof (u8_range lo). pose proof (u8_range hi).
pose proof (st_tables _ _ ST) as STB. unfold table_addr in STB.
cbn [ms_segs ms_debruijn ms_size_classes ms_small_cnt ms_med_cnt src0_msyms] in STB.
cbn [ms_segs ms_size_classes src0_msyms] in Hlo, Hhi. unfold w64 in STB, Hlo, Hhi.
unfold znth. rewrite <- Hsum.
intros kk Hkk. unfold TBL. rewrite STB by (unfold src0_D_size_classes, src0_D_debruijn32, src0_D_small_cnt_tab, src0_D_med_cnt_tab; lia).
destruct kk as [|[|]]; [| | lia]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
+ rewrite Z.add_0_r, Hlo. f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 lo) at 1. f_equal.
unfold le_byte. change (2 ^ (8 * Z.of_nat 2)) with 65536. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite (Z.mod_small _ 65536) by lia. rewrite (Z.mul_comm 256 (bv_unsigned hi)), Z_mod_plus_full. symmetry. apply Z.mod_small. lia.
+ change (Z.of_nat 1) with 1. rewrite Hhi. f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 hi) at 1. f_equal.
unfold le_byte. change (2 ^ (8 * Z.of_nat 2)) with 65536. change (8 * Z.of_nat 1) with 8.
rewrite (Z.mod_small _ 65536) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
rewrite (Z.mul_comm 256 (bv_unsigned hi)), Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. symmetry. apply Z.mod_small. lia.
Qed.
Lemma old_meta_cell q aq c : usedX X A q aq -> In c (meta_slot_cells q (Some (MUsed aq))) -> In c (imageX X A ++ tail_cellsX X A).
Proof.
intros Huq Hc. apply in_app_iff. left. unfold imageX. apply in_app_iff. right. apply in_app_iff. left.
exact (meta_cells_in_areas X R U A HI q aq c (proj1 (usedX_MT _ _ _ _ Huq)) Hc).
Qed.
Lemma footprint_hi e : In e (footprint A) -> loc_addr L (fst e) + snd e <= alloc_ceiling.
Proof.
intros He. pose proof SO as SO'.
destruct (In_footprint_inv A e He) as [-> | [(a & Ha & ->) | (k & r & Hr & Hk & Hl & ->)]]; cbn [fst snd loc_addr].
- rewrite Hctx. pose proof (so_ctx_hi _ SO'). unfold CTX. cbn [ms_ctx src0_msyms] in *. lia.
- destruct (proj1 (proj2 (inv_areas HI)) a Ha) as (r & o & rg & -> & _ & Ho & Hr & Hl & Hlen & _). cbn [loc_addr].
destruct (lg_placed _ _ _ _ LG r rg Hr Hl) as (_ & H1 & H2 & _). unfold PGSZ in *. lia.
- destruct (lg_placed _ _ _ _ LG k r Hr Hl) as (_ & H1 & H2 & _). lia.
Qed.
Lemma footprint_below e x : In e (footprint A) -> loc_addr L (fst e) <= x < loc_addr L (fst e) + snd e -> 4096 <= x < alloc_ceiling.
Proof.
intros He Hx. pose proof SO as SO'.
destruct (In_footprint_inv A e He) as [-> | [(a & Ha & ->) | (k & r & Hr & Hk & Hl & ->)]]; cbn [fst snd loc_addr] in Hx.
- rewrite Hctx in Hx. pose proof (so_ctx_lo _ SO'). pose proof (so_ctx_hi _ SO'). unfold CTX in Hx. cbn [ms_ctx src0_msyms] in *. lia.
- destruct (proj1 (proj2 (inv_areas HI)) a Ha) as (r & o & rg & -> & _ & Ho & Hr & Hl & Hlen & _). cbn [loc_addr] in Hx.
destruct (lg_placed _ _ _ _ LG r rg Hr Hl) as (_ & H1 & H2 & _). unfold PGSZ in *. lia.
- destruct (lg_placed _ _ _ _ LG k r Hr Hl) as (_ & H1 & H2 & _). lia.
Qed.
End f.
Section g.
Variables (xv : nat -> Z) (L : layout) (mem1 : word -> option byte).
Hypothesis XR : forall n, 0 <= xv n < 2 ^ 64.
Lemma chunk8_cell base off e z loc (val : sval) :
chunk_ok src0segs (EV xv) mem1 base (mkChunk off (CVal 8 e)) ->
bv_unsigned (sv_denot (EV xv) e) = z mod 2 ^ 64 -> loc_addr L loc = base + off -> sval_num L val = z ->
match val with VLo5 _ => False | _ => True end ->
cell_mem B1 L mem1 (MCell loc 8 val).
Proof.
intros Hc Hv Hloc Hval Hnl. unfold cell_mem. cbn [mc_val mc_loc mc_w]. rewrite Hloc.
assert (K : forall k, (k < 8)%nat -> mbyte src0segs mem1 (base + off + Z.of_nat k) = Some (Z_to_bv 8 (le_byte z 8 k))).
{ intros k Hk. destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (b & Eb & Mb). cbn [c_off c_val cbyte] in Eb, Mb. rewrite Mb. injection Eb as <-. f_equal.
unfold byte_of_word. rewrite Hv. unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z_to_bv8_mod. reflexivity. }
destruct val; cbn [sval_num] in Hval |- *; rewrite ?Hval; first [exact K | destruct Hnl].
Qed.
Lemma chunk4_cell_sx base off e y loc :
chunk_ok src0segs (EV xv) mem1 base (mkChunk off (CVal 4 e)) ->
bv_unsigned (sv_denot (EV xv) e) = sx32 y -> 0 <= y -> loc_addr L loc = base + off ->
cell_mem B1 L mem1 (MCell loc 4 (VZ y)).
Proof.
intros Hc Hv Hy Hloc. unfold cell_mem. cbn [mc_val mc_loc mc_w sval_num]. rewrite Hloc. intros k Hk.
enough (E : mbyte src0segs mem1 (base + off + Z.of_nat k) = Some (Z_to_bv 8 (le_byte y 4 k))) by exact E.
destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (b & Eb & Mb). cbn [c_off c_val cbyte] in Eb, Mb. rewrite Mb. injection Eb as <-. f_equal.
unfold byte_of_word. rewrite Hv. apply byte_sx32; [exact Hy | exact Hk].
Qed.
Lemma chunk4_cell base off e y loc :
chunk_ok src0segs (EV xv) mem1 base (mkChunk off (CVal 4 e)) ->
bv_unsigned (sv_denot (EV xv) e) = y -> 0 <= y < 2 ^ 32 -> loc_addr L loc = base + off ->
cell_mem B1 L mem1 (MCell loc 4 (VZ y)).
Proof.
intros Hc Hv Hy Hloc. unfold cell_mem. cbn [mc_val mc_loc mc_w sval_num]. rewrite Hloc. intros k Hk.
enough (E : mbyte src0segs mem1 (base + off + Z.of_nat k) = Some (Z_to_bv 8 (le_byte y 4 k))) by exact E.
destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (b & Eb & Mb). cbn [c_off c_val cbyte] in Eb, Mb. rewrite Mb. injection Eb as <-. f_equal.
unfold byte_of_word, le_byte. rewrite Hv, Z_to_bv8_mod. f_equal. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma byte_of_lo32 (w y : Z) (k : nat) : (k < 4)%nat -> 0 <= w -> lo32 w = y ->
Z_to_bv 8 (Z.shiftr w (8 * Z.of_nat k)) = Z_to_bv 8 (le_byte y 4 k).
Proof.
intros Hk Hw Hy. subst y. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
unfold le_byte, lo32. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_mod _ 256) by lia. change 256 with (2 ^ 8).
apply Z.bits_inj'. intros j Hj.
destruct (Z_lt_dec j 8).
- rewrite !Z.mod_pow2_bits_low, !Z.shiftr_spec, Z.mod_pow2_bits_low by lia.
rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma chunk4_cell_lo32 base off e y loc :
chunk_ok src0segs (EV xv) mem1 base (mkChunk off (CVal 4 e)) ->
lo32 (bv_unsigned (sv_denot (EV xv) e)) = y -> loc_addr L loc = base + off ->
cell_mem B1 L mem1 (MCell loc 4 (VZ y)).
Proof.
intros Hc Hv Hloc. unfold cell_mem. cbn [mc_val mc_loc mc_w sval_num]. rewrite Hloc. intros k Hk.
enough (E : mbyte src0segs mem1 (base + off + Z.of_nat k) = Some (Z_to_bv 8 (le_byte y 4 k))) by exact E.
destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (b & Eb & Mb). cbn [c_off c_val cbyte] in Eb, Mb. rewrite Mb. injection Eb as <-. f_equal.
unfold byte_of_word. apply byte_of_lo32; [exact Hk | pose proof (u64_range (sv_denot (EV xv) e)); lia | exact Hv].
Qed.
End g.
Lemma ldiff_as_sub a b : 0 <= a -> 0 <= b -> Z.ldiff a b = a - Z.land a b.
Proof.
intros Ha Hb. pose proof (Z.lor_ldiff_and a b) as E.
assert (D : Z.land (Z.ldiff a b) (Z.land a b) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
rewrite <- Z.lxor_lor in E by exact D. rewrite <- Z.add_nocarry_lxor in E by exact D. lia.
Qed.
Lemma off_img a0 : (forall x, a0 <= x < a0 + 40 -> ~ in_img B1 x) -> a0 + 40 <= 0x10000 \/ 0x51000 <= a0.
Proof.
intros Ho. destruct (img_gap 0x10000 (0x51000 - 0x10000) a0 40 ltac:(intros x Hx; unfold in_img1; lia) ltac:(lia) Ho ltac:(lia)); lia.
Qed.
Lemma M64w z : 0 <= z mod 2 ^ 64 < 2 ^ (8 * Z.of_N 8).
Proof. apply Z.mod_pos_bound. cbn. lia. Qed.
Lemma bytes_are_at' m a a' w x : bytes_are m a w x -> a = a' -> bytes_are m a' w x.
Proof. intros Hb <-. exact Hb. Qed.
Lemma optr_facts L (o : option sptr) : sval_num L (optr o) = optrZ L o /\ match optr o with VLo5 _ => False | _ => True end.
Proof. destruct o; cbn; auto. Qed.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
