(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN1e.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO12.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0y.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN31.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN26.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1y.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma statics_layout :
0x10000 <= DEB /\ DEB + 32 <= 0x51000 /\ 0x10000 <= YN0j.CTX /\ YN0j.CTX + 928 <= 0x51000 /\
0x10000 <= GOT /\ GOT + 8 <= 0x51000 /\ 0x10000 <= GUARD /\ GUARD + 8 <= 0x51000 /\ 0x10000 <= LIBC /\ LIBC + 56 <= 0x51000 /\
YN0j.LOCK + 8 = YN0j.CTX /\ (DEB + 32 <= GOT \/ GOT + 8 <= DEB) /\ (DEB + 32 <= GUARD \/ GUARD + 8 <= DEB) /\
(DEB + 32 <= LIBC \/ LIBC + 56 <= DEB) /\ (DEB + 32 <= YN0j.CTX \/ YN0j.CTX + 928 <= DEB).
Proof.
unfold DEB, YN0j.CTX, YN0j.LOCK, GOT, GUARD, LIBC, src0_D_debruijn32, src0_D_malloc_context, src0_D_malloc_lock,
src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_libc. lia.
Qed.
Lemma finalS_check_F1 : finalS_check SSF1 (SOff aJ 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma U_sext32' E a : bv_unsigned (sv_denot E (SExt true 32 a)) = sx32 (bv_unsigned (sv_denot E a)).
Proof.
cbn [sv_denot]. rewrite sext64_32_unsigned, bv_extract_unsigned, Z.shiftr_0_r, bv_wrap32.
change (bv_unsigned (sv_denot E a) mod 2 ^ 32) with (lo32 (bv_unsigned (sv_denot E a))). apply sx32_lo32.
Qed.
Lemma den_atom E k v z : ew E k = Z_to_bv 64 v -> 0 <= v + z < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff k z) = Z_to_bv 64 (v + z).
Proof. intros Hk Hvz Hv. cbn [sv_denot]. rewrite Hk, lit64_small by exact Hv. reflexivity. Qed.
Lemma den_atom0 E k v : ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff k 0) = Z_to_bv 64 v.
Proof. intros Hk Hv. rewrite (den_atom E k v 0 Hk) by lia. rewrite Z.add_0_r. reflexivity. Qed.
Lemma chunk_ok_val' E m base off (w : N) (e : sv) v :
bv_unsigned (sv_denot E e) = v -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
bytes_are m (base + off) (N.to_nat w) v ->
chunk_ok src0segs E m base (mkChunk off (CVal w e)).
Proof.
intros Hv Hr Hb i Hi. cbn [c_off c_val c_len cv_len] in *.
exists (byte_of_word (sv_denot E e) i). split; [reflexivity|].
specialize (Hb (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hb by lia. rewrite Hb. f_equal.
unfold byte_of_word, le_byte. rewrite Hv. rewrite Z_to_bv8_mod. f_equal.
rewrite Z2Nat.id by lia. rewrite N_nat_Z. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma chunk_bytes' E m base off (w : N) e v :
chunk_ok src0segs E m base (mkChunk off (CVal w e)) -> bv_unsigned (sv_denot E e) = v ->
bytes_are m (base + off) (N.to_nat w) (v mod 2 ^ (8 * Z.of_N w)).
Proof.
intros Hc Hv k Hk. destruct (Hc (Z.of_nat k) ltac:(cbn [c_len c_val cv_len]; lia)) as (b & Hb1 & Hb2).
cbn [c_off c_val cbyte] in Hb1, Hb2. rewrite Hb2. injection Hb1 as <-. f_equal.
unfold byte_of_word, le_byte. rewrite Hv, <- (Z_to_bv8_mod (Z.shiftr v _)). f_equal. rewrite N_nat_Z.
rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). change 256 with (2 ^ 8). symmetry. apply shiftr_mod_byte; lia.
Qed.
Lemma base_atom E k v : ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v.
Proof. intros Hk Hv. cbn [base_val]. rewrite Hk. apply lit64_small. exact Hv. Qed.
Section h.
Variables (X : list sptr) (U : Z -> Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (sc n stk : Z).
Hypothesis HI : Inv X None U A.
Hypothesis XR : rawX X A.
Hypothesis AMA : ama_ok A.
Hypothesis BND : bounded A.
Hypothesis RSV : rsv_ok A.
Hypothesis SPOK : span_ok A.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hn : 0 <= n < MMAP_THRESHOLD.
Hypothesis MID : midrep B L A mem md.
Hypothesis AUXP : st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem.
Hypothesis PRE : callee_pre B regs mem stk.
Hypothesis Hstk : ASF <= stk <= AS_STACK.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 sc.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 n.
Hypothesis AMH : alloc_meta_hyp B.
Variable g : Z.
Hypothesis Hg : word_mem src0segs mem GUARD g.
Let sp : Z := bv_unsigned (getr regs 2).
Lemma rawX_notused s x am : rawX X s -> In x X -> MT s x = Some (MUsed am) -> False.
Proof. intros RX Hx H. pose proof (RX x Hx) as E. first [rewrite E in H; discriminate | destruct E as [E|E]; rewrite E in H; discriminate]. Qed.
Let XC : Xclean X A := fun x am Hx H => rawX_notused A x am XR Hx H.
Lemma used_metasX_all' s : rawX X s -> (forall g am, In (g, am) (used_metas s) -> MT s g = Some (MUsed am)) -> used_metasX X s = used_metas s.
Proof.
intros RX UM. unfold used_metasX. apply filter_all. intros [g' am] Hin. cbn [fst].
destruct (memb g' X) eqn:E; [| reflexivity]. exfalso. apply (proj1 (memb_In g' X)) in E. exact (rawX_notused s g' am RX E (UM g' am Hin)).
Qed.
Let E00 : env := E0 regs (cs L A sc g 0 0).
Let ms0 := mkst regs (Z_to_bv 64 src0_A_alloc_slot) mem (seg_rom src0segs).
Let rom := seg_rom src0segs.
Lemma pre_factsT : YK0s.ret_ok (getr regs 1) /\ sp mod 16 = 0 /\ alloc_ceiling + stk <= sp /\ sp < 2 ^ 63 /\
(forall a, sp - stk <= a < sp -> writable_at src0segs mem a) /\ getr regs 4 = Z_to_bv 64 TP /\
(forall a, ERRNO <= a < ERRNO + 4 -> writable_at src0segs mem a).
Proof. exact (pre_facts regs mem stk PRE). Qed.
Lemma md_factsT : m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [].
Proof. exact (mid_md _ _ _ _ _ MID). Qed.
Lemma MRX : memrepX B [] L A mem.
Proof. apply (proj2 (memrepX_nil B L A mem)). exact (mid_mem _ _ _ _ _ MID). Qed.
Lemma HctxT : ly_ctx L = YN0t.CTX.
Proof. exact (mid_ctx _ _ _ _ _ MID). Qed.
Lemma memrepX_X s m : rawX X s -> Inv X None U s \/ (exists R, Inv X R U s) -> memrepX B [] L s m <-> memrepX B X L s m.
Proof.
intros RXs HIs.
assert (HI' : exists R, Inv X R U s) by (destruct HIs as [H|H]; [exists None; exact H | exact H]). destruct HI' as [R HIR].
assert (E : used_metasX X s = used_metas s).
{ apply used_metasX_all'; [exact RXs|]. intros g' am Hin. exact (proj1 (usedX_MT _ _ _ _ (proj1 (used_metas_usedX' X R U s HIR (fun x am' Hx Hm => rawX_notused s x am' RXs Hx Hm) g' am) Hin))). }
unfold memrepX, imageX, tail_cellsX. rewrite E, used_metasX_nil. split; intros H; exact H.
Qed.
Lemma MRXX : memrepX B X L A mem.
Proof. exact (proj1 (memrepX_X A mem XR (or_introl HI)) MRX). Qed.
Section T1.
Variables (m : sptr) (am : ameta).
Hypothesis Hhd : active_hd A sc = Some m.
Hypothesis Mg : MT A m = Some (MUsed am).
Hypothesis Hav : am_avail am <> 0.
Definition mask : Z := am_avail am.
Definition first : Z := lowbit mask.
Definition idx : Z := ctz32 first.
Definition jidx : Z := srlw (mul64 (sx32 first) DBJ_MUL) 27.
Definition am1 : ameta := am_set_avail (mask - first) am.
Definition A1 : astate := upd_meta m (MUsed am1) A.
Definition M0 : Z := ptr_addr L m.
Lemma m_facts : usedX X A m am /\ am_sc am = sc /\
4096 <= M0 /\ M0 + 40 <= alloc_ceiling /\ M0 mod 8 = 0 /\ (forall x, M0 <= x < M0 + 40 -> ~ in_img B x) /\
0 < mask < 2 ^ 32 /\ 0 <= am_freed am < 2 ^ 32 /\ cs L A sc g 0 0 34 = M0.
Proof.
destruct (head_used X None U A sc m HI Hsc Hhd) as (am' & Hu & Hsc'). pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as M'. rewrite Mg in M'. injection M' as <-.
destruct (YN0p.meta_facts X None U L A md HI (mid_ledger _ _ _ _ _ MID) m am Hu) as (F1 & F2 & F3 & F4 & _).
pose proof (inv_groups HI m am Hu) as ((Glast & _ & _ & Gav & Gfr & _ & Gabove & _) & _).
assert (Hav32 : am_avail am < 2 ^ 32) by (apply (mask_u32 _ (am_last am)); [lia|lia|intros i Hi; apply (proj1 (Gabove i Hi))]).
assert (Hfr32 : am_freed am < 2 ^ 32) by (apply (mask_u32 _ (am_last am)); [lia|lia|intros i Hi; apply (proj2 (Gabove i Hi))]).
unfold mask, M0. repeat (split; [assumption || (pose proof Hav; unfold mask; lia)|]). cbn [cs]. rewrite Hhd. reflexivity.
Qed.
Lemma take_factsT : 0 <= idx < 32 /\ first = bit idx /\ Z.testbit mask idx = true /\ Inv X (Some (m, idx)) U A1 /\
0 <= idx <= am_last am /\ class_size sc <= stride_of am /\ 0 <= jidx < 32 /\ znth jidx DEBRUIJN = idx /\
0 < first <= mask /\ length (am_slots am) = Z.to_nat (am_last am + 1).
Proof.
pose proof m_facts as (Hu & Hsc' & _ & _ & _ & _ & Mr & _).
pose proof (take_bit_Inv X U A m am HI Hu ltac:(lia) ltac:(rewrite Hsc'; exact Hhd) Hav) as (K1 & K2 & K3 & K4).
pose proof (inv_groups HI m am Hu) as ((Glast & Gaidx & Glen & _) & _).
pose proof (avail_bit_not_undersized X None U A m am idx HI Hu ltac:(lia) ltac:(unfold idx, first, mask in *; lia) ltac:(rewrite Z.lor_spec; unfold idx, first, mask in *; rewrite K3; reflexivity)) as US.
pose proof (dbj_ctz32 mask ltac:(lia)) as [J1 J2]. pose proof (lowbit_le mask ltac:(lia)) as LB.
pose proof (ctz32_lt (lowbit mask) 32 ltac:(lia) ltac:(lia)) as CR.
assert (CZ : ctz32 (lowbit (am_avail am)) = ctz32 (am_avail am)) by (pose proof Mr as Mr'; unfold mask in Mr'; unfold ctz32; rewrite lowbit_lowbit by lia; reflexivity).
unfold A1, am1, jidx, idx, first, mask in *. rewrite Hsc' in US. rewrite !CZ in *.
repeat (split; [assumption || lia|]). exact Glen.
Qed.
Lemma meta_mask_cellsT : bytes_are mem (M0 + 24) 4 mask /\ bytes_are mem (M0 + 28) 4 (am_freed am).
Proof.
pose proof m_facts as (Hu & _).
pose proof (YN0p.meta_cell X None U L A mem HI MRXX m am _ Hu ltac:(cbn; do 3 right; left; reflexivity)) as C1.
pose proof (YN0p.meta_cell X None U L A mem HI MRXX m am _ Hu ltac:(cbn; do 4 right; left; reflexivity)) as C2.
unfold cell_mem in C1, C2. cbn [mc_val mc_loc mc_w sval_num] in C1, C2. rewrite loc_addr_padd' in C1, C2.
change (ms_segs B) with src0segs in C1, C2. unfold META_avail in C1. unfold META_freed in C2. unfold M0, mask, ptr_addr. split; [exact C1 | exact C2].
Qed.
Definition E1_of (E : env) : env :=
ewset (ewset (ewset E aAV (Z_to_bv 64 mask)) aTQ (Z_to_bv 64 (DEB + jidx))) aJ (Z_to_bv 64 idx).
Lemma E1_agree E : env_agree 40 E (E1_of E).
Proof.
unfold E1_of. eapply env_agree_trans; [| eapply env_agree_le; [| apply env_agree_ewset]; unfold aJ; lia].
eapply env_agree_trans; [| eapply env_agree_le; [| apply env_agree_ewset]; unfold aTQ; lia].
eapply env_agree_le; [| apply env_agree_ewset]. unfold aAV; lia.
Qed.
Lemma E1_vals E : ew (E1_of E) aAV = Z_to_bv 64 mask /\ ew (E1_of E) aTQ = Z_to_bv 64 (DEB + jidx) /\ ew (E1_of E) aJ = Z_to_bv 64 idx /\
forall k, (k < 40)%nat -> ew (E1_of E) k = ew E k.
Proof.
unfold E1_of. split; [rewrite !ew_ewset_other by (unfold aAV, aTQ, aJ; lia); apply ew_ewset_same|].
split; [rewrite ew_ewset_other by (unfold aTQ, aJ; lia); apply ew_ewset_same|]. split; [apply ew_ewset_same|].
intros k Hk. rewrite !ew_ewset_other by (unfold aAV, aTQ, aJ; lia). reflexivity.
Qed.
Section j.
Variables (E : env) (ms : machine_state).
Hypothesis HS : st_ok src0segs E ss_hd ms.
Hypothesis HA : env_agree 40 E00 E.
Hypothesis HF : FRM mem (WS regs) (ms_mem ms).
Let E1 := E1_of E.
Lemma HA1 : env_agree 40 E00 E1.
Proof. eapply env_agree_trans; [exact HA | apply E1_agree]. Qed.
Lemma E1_34 : ew E1 34 = Z_to_bv 64 M0.
Proof. pose proof m_facts as (_ & _ & _ & _ & _ & _ & _ & _ & C34). rewrite <- C34. exact (agree_cs L A regs sc g 0 0 E1 34 HA1 ltac:(lia)). Qed.
Lemma E1_2 : ew E1 2 = getr regs 2.
Proof. exact (agree_reg L A regs sc g 0 0 E1 2 HA1 ltac:(lia)). Qed.
Lemma mask_denotT : bv_unsigned (sv_denot E1 MASKX) = sx32 mask.
Proof.
pose proof m_facts as (_ & _ & _ & _ & _ & _ & Mr & _). destruct (E1_vals E) as (V1 & _).
unfold MASKX. rewrite U_sext32'. subst E1. rewrite (den_atom0 _ aAV mask V1) by lia. rewrite lit64_small by lia. reflexivity.
Qed.
Lemma lowbit_denotT : bv_unsigned (sv_denot E1 LOWBIT) = sx32 first /\ bv_unsigned (sv_denot E1 LOWBIT) <> 0.
Proof.
pose proof m_facts as (_ & _ & _ & _ & _ & _ & Mr & _).
exact (take_first_word (sv_denot E1 MASKX) (sv_denot E1 LOWBIT) mask Mr mask_denotT eq_refl).
Qed.
Lemma tqaddr_denotT : sv_denot E1 TQADDR = Z_to_bv 64 (DEB + jidx).
Proof.
pose proof take_factsT as (_ & _ & _ & _ & _ & _ & J & _). destruct lowbit_denotT as [L1 _]. pose proof statics_layout as (D1 & D2 & _).
apply word_eq. unfold TQADDR. cbn [sv_denot]. rewrite alu64_add, srlw_rr_unsigned, mul64_unsigned, L1.
change (bv_unsigned (Z_to_bv 64 DBJ)) with DBJ_MUL. change (bv_unsigned (Z_to_bv 64 27)) with 27. fold jidx.
rewrite (lit64_small DEB) by lia. rewrite (lit64_small (DEB + jidx)) by lia. apply add64_small. lia.
Qed.
Lemma avail'_denotT : bv_unsigned (sv_denot E1 AVAIL') mod 2 ^ 32 = mask - first.
Proof.
pose proof m_facts as (_ & _ & _ & _ & _ & _ & Mr & _). destruct lowbit_denotT as [L1 _].
unfold AVAIL'. cbn [sv_denot]. fold (sv_denot E1 MASKX). fold (sv_denot E1 LOWBIT).
pose proof (take_rest_word (sv_denot E1 MASKX) (sv_denot E1 LOWBIT) _ mask Mr mask_denotT L1 eq_refl) as R.
rewrite low32_unsigned in R. unfold lo32 in R. exact R.
Qed.
Lemma F1_st_ok : st_ok src0segs E1 ss_F1 ms.
Proof.
pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_factsT as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
pose proof m_facts as (Hu & Hsc' & G1 & G2 & G8 & Gimg & Mr & _). pose proof take_factsT as (I1 & _ & _ & _ & _ & _ & J & Jz & _).
pose proof statics_layout as SL. destruct (E1_vals E) as (V42 & V43 & V44 & Vlt). fold E1 in V42, V43, V44, Vlt.
pose proof E1_34 as V34. pose proof E1_2 as V2. pose proof (YN0p.off_img M0 Gimg) as GF. destruct lowbit_denotT as [L1 L2].
pose proof (st_ok_agree src0segs 40 E E1 ss_hd ms HS (E1_agree E) ss_hd_atoms) as HS1.
destruct HS1 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & (Swf & Sreg & Spd) & (Sat & Scd & Sal)).
assert (B34 : base_val E1 (Some 34%nat) = M0) by (apply (base_atom E1 34 M0 V34); lia).
assert (B43 : base_val E1 (Some aTQ) = DEB + jidx) by (apply (base_atom E1 aTQ _ V43); lia).
assert (B33 : base_val E1 (Some 33%nat) = YN0j.LOCK + 8 * sc).
{ apply (base_atom E1 33); [exact (agree_cs L A regs sc g 0 0 E1 33 HA1 ltac:(lia)) | lia]. }
assert (B2 : base_val E1 (Some 2%nat) = sp) by (cbn [base_val]; rewrite V2; reflexivity).
assert (ST : statics_ok B mem) by exact (mid_statics _ _ _ _ _ MID).
unfold st_ok, ss_F1. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|]. split; [exact S6|]. split; [exact S7|]. split.
- apply mem_ok_intro.
+ vm_compute. reflexivity.
+ apply Forall_cons; [|apply Forall_cons; [|exact Sreg]].
* apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_m0]; rewrite B34; [lia | lia | |].
{ intros o Ho. apply (writable_ext1 mem); [apply HF; [lia | unfold WS; lia]|].
apply present_writable. apply (YN0p.meta_present X None U L A mem md HI MRXX (mid_ledger _ _ _ _ _ MID) m am _ Hu). unfold M0 in *. lia. }
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val' E1 _ _ _ 4 _ mask); [rewrite (den_atom0 E1 aAV mask V42) by lia; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia |].
apply (bytes_are_ext mem); [intros i Hi; apply HF; [lia | unfold WS; lia]|].
exact (proj1 meta_mask_cellsT).
* apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_tqj]; rewrite B43; [lia | lia | intros; lia |].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val' E1 _ _ _ 1 _ idx); [rewrite (den_atom0 E1 aJ idx V44) by lia; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 1)) with 256; lia |].
apply (bytes_are_ext mem); [intros i Hi; apply HF; [lia | unfold WS; lia]|]. rewrite Z.add_0_r, <- Jz. apply (deb_byte mem ST). exact J.
+
assert (OLD : map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_hd) =
[(Some 33%nat, 88, 96); (Some 2%nat, -384, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56)]) by (vm_compute; reflexivity).
assert (DJ : forall r, In r (ss_mem ss_hd) -> extent_disjoint E1 R_m0 r /\ extent_disjoint E1 R_tqj r).
{ intros r Hr. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr. rewrite OLD in Hr. unfold extent_disjoint. cbn [r_base r_lo r_hi R_m0 R_tqj]. rewrite B34, B43.
cbn [In] in Hr. decompose [or] Hr; try contradiction;
match goal with H : (_, _, _) = (r_base r, r_lo r, r_hi r) |- _ => injection H as <- <- <- end; rewrite ?B33, ?B2; cbn [base_val]; unfold ASF in *; lia. }
cbn [pairwise_disjoint all_disjoint app]. split; [| split; [| exact Spd]].
* split; [unfold extent_disjoint; cbn [r_base r_lo r_hi R_m0 R_tqj]; rewrite B34, B43; lia|].
clear - DJ. induction (ss_mem ss_hd) as [|r l IH]; [exact I|]. split; [exact (proj1 (DJ r (or_introl eq_refl))) | apply IH; intros r' H'; apply DJ; right; exact H'].
* clear - DJ. induction (ss_mem ss_hd) as [|r l IH]; [exact I|]. split; [exact (proj2 (DJ r (or_introl eq_refl))) | apply IH; intros r' H'; apply DJ; right; exact H'].
- unfold f1_facts, facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split].
+ unfold f1_atoms. cbn [app atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite V34, V42, V43, V44, !lit64_small by lia.
change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact Sat].
+ split; [|split; [|exact I]]; unfold acond_ok; cbn [ac_c ac_a ac_b C_mask C_lb]; rewrite branch_ne; cbn [sv_denot]; fold (sv_denot E1 MASKX); fold (sv_denot E1 LOWBIT); rewrite (lit64_small 0) by lia.
* rewrite mask_denotT. destruct (Z.eqb_spec (sx32 mask) 0) as [E0|]; [exfalso; exact (sx32_nonzero_u32 mask ltac:(lia) E0) | reflexivity].
* destruct (Z.eqb_spec (bv_unsigned (sv_denot E1 LOWBIT)) 0); [exfalso; exact (L2 e) | reflexivity].
+ split; [|exact I]. rewrite tqaddr_denotT, (den_atom0 E1 aTQ _ V43) by lia. reflexivity.
Qed.
Record at_RET (rg : bvmap 5 word) (mc : word -> option byte) : Prop := RET_ {
rt_pres : regs_preserved regs rg;
rt_10 : getr rg 10 = Z_to_bv 64 idx;
rt_out : forall x, 0 <= x < 2 ^ 64 -> ~ WS regs x -> ~ (M0 + 24 <= x < M0 + 28) -> mc (Z_to_bv 64 x) = mem (Z_to_bv 64 x);
rt_avail : bytes_are mc (M0 + 24) 4 (mask - first);
rt_win : forall a, M0 + 24 <= a < M0 + 28 -> writable_at src0segs mc a;
rt_stk : forall a, WS regs a -> writable_at src0segs mc a;
rt_guard : word_mem src0segs mc GUARD g }.
Lemma F1_post ms1 : st_ok src0segs E1 SSF1 ms1 -> frame_of E1 (ss_mem ss_F1) (ms_mem ms) (ms_mem ms1) ->
ms1 = mkst (ms_regs ms1) (Z_to_bv 64 PS_JR) (ms_mem ms1) rom /\ sr_get (ss_regs SSF1) 1 = SOff 1 0 /\ ew E1 1 = getr regs 1 /\ at_RET (ms_regs ms1) (ms_mem ms1).
Proof.
intros HS1 HFR. pose proof SSF1_shape as (Hpc & Hrv & Hmem & Hra & H10). pose proof (proj1 alloc_ceiling_val) as AC.
pose proof m_facts as (Hu & Hsc' & G1 & G2 & G8 & Gimg & Mr & _). pose proof take_factsT as (I1 & _).
destruct (E1_vals E) as (V42 & V43 & V44 & Vlt). fold E1 in V42, V43, V44, Vlt. pose proof E1_34 as V34. pose proof E1_2 as V2.
destruct (finalS L A regs mem sc stk PRE g 0 0 E1 SSF1 ms1 (SOff aJ 0) finalS_check_F1 HS1 HA1) as (RP & Era & _ & _ & _ & G10).
pose proof (st_ok_mem_ok src0segs _ _ _ HS1) as (_ & MOK & _). rewrite Hmem in MOK.
pose proof (Forall_inv MOK) as RM. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail MOK)))) as RS.
destruct RM as (_ & _ & WRm & CHm). cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_m0'] in WRm, CHm. rewrite (base_atom E1 34 M0 V34) in WRm, CHm by lia.
assert (SKR : (r_base R_stackS, r_wlo R_stackS, r_whi R_stackS) = (Some 2%nat, -ASF, 0)) by reflexivity.
destruct RS as (_ & _ & WRs & _). destruct R_stackS as [sb slo shi swlo swhi sch]. cbn [r_base r_wlo r_whi] in WRs, SKR. injection SKR as -> -> ->.
cbn [base_val] in WRs. rewrite V2 in WRs. fold sp in WRs.
split; [rewrite <- Hpc; exact (YN1d.st_ok_mkst E1 SSF1 ms1 HS1 Hrv)|]. split; [exact Hra|]. split; [exact Era|]. split.
- exact RP.
- rewrite G10. apply (den_atom0 E1 aJ idx V44). lia.
- intros x Hx Hns Hnm. rewrite <- (HF x Hx Hns). apply (HFR (Z_to_bv 64 x)). rewrite lit64_small by exact Hx.
intros (r & Hin & Hr). cbn [ss_mem ss_F1 app] in Hin.
assert (OLDW : forall r', In r' (ss_mem ss_hd) -> r_wlo r' = r_whi r' \/ (r_base r', r_wlo r', r_whi r') = (Some 2%nat, -ASF, 0)).
{ intros r' Hr'. assert (OW : map (fun r => (r_base r, r_wlo r, r_whi r)) (ss_mem ss_hd) = [(Some 33%nat, 0, 0); (Some 2%nat, -ASF, 0); (None, 0, 0); (None, 0, 0); (None, 0, 0)]) by (vm_compute; reflexivity).
apply (in_map (fun r => (r_base r, r_wlo r, r_whi r))) in Hr'. rewrite OW in Hr'. cbn [In] in Hr'.
decompose [or] Hr'; try contradiction; match goal with H : (_, _, _) = _ |- _ => first [right; symmetry; exact H | left; injection H as _ <- <-; reflexivity] end. }
destruct Hin as [<- | [<- | Hin]].
+ cbn [r_base r_wlo r_whi R_m0] in Hr. rewrite (base_atom E1 34 M0 V34) in Hr by lia. lia.
+ cbn [r_base r_wlo r_whi R_tqj] in Hr. lia.
+ destruct (OLDW r Hin) as [W0 | Wr]; [rewrite W0 in Hr; lia|]. injection Wr as Eb Ewl Ewh. rewrite Eb, Ewl, Ewh in Hr. cbn [base_val] in Hr. rewrite V2 in Hr. unfold WS in Hns. fold sp in Hr. lia.
- rewrite <- avail'_denotT. change (2 ^ 32) with (2 ^ (8 * Z.of_N 4)). apply (chunk_bytes' E1 _ _ _ 4 AVAIL'); [exact (Forall_inv CHm) | reflexivity].
- intros a Ha. replace a with (M0 + (a - M0)) by lia. apply WRm. lia.
- intros a Ha. unfold WS, ASF in Ha. fold sp in Ha. replace a with (sp + (a - sp)) by lia. apply WRs. lia.
- exact (guard_of_state L A regs sc g 0 0 E1 SSF1 ms1 5 HS1 HA1 ltac:(vm_compute; reflexivity)).
Qed.
End j.
Section p.
Variables (rg : bvmap 5 word) (mc : word -> option byte).
Hypothesis RET : at_RET rg mc.
Lemma A1_facts : footprint A1 = footprint A /\ st_regions A1 = st_regions A /\ st_areas A1 = st_areas A /\
MT A1 m = Some (MUsed am1) /\ usedX X A1 m am1 /\ user_blocks A1 = user_blocks A /\ ub_same A A1 /\ rawX X A1 /\
(forall g' a', usedX X A1 g' a' <-> (g' = m /\ a' = am1) \/ (g' <> m /\ usedX X A g' a')).
Proof.
pose proof m_facts as (Hu & _). pose proof take_factsT as (_ & _ & _ & HI2 & _).
assert (UB : ub_same A A1).
{ unfold A1. apply ub_same_upd_In; [eapply MT_Some_In_keys; exact Mg|]. rewrite Mg. cbn. unfold am1. apply blocks_of_avail. }
unfold A1. rewrite footprint_upd_meta. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [apply MT_upd_same|]. split; [apply usedX_upd; left; split; [reflexivity | split; [exact (proj2 (usedX_MT _ _ _ _ Hu)) | reflexivity]]|].
split; [apply ub_same_user_blocks; [exact (proj1 (inv_keys HI)) | exact (proj1 (inv_keys HI2)) | exact UB]|]. split; [exact UB|]. split.
- intros x Hx. unfold A1. rewrite MT_upd_other; [exact (XR x Hx)|]. intros ->.
pose proof (proj2 (usedX_MT _ _ _ _ Hu)) as NX. apply (proj2 (memb_In m X)) in Hx. rewrite Hx in NX. discriminate.
- intros g' a'. rewrite usedX_upd. split.
+ intros [(-> & _ & E)|[Hne Hu']]; [left; split; [reflexivity | congruence] | right; auto].
+ intros [[-> ->]|[Hne Hu']]; [left; split; [reflexivity | split; [exact (proj2 (usedX_MT _ _ _ _ Hu)) | reflexivity]] | right; auto].
Qed.
Definition cAV : mcell := MCell (LMem (padd m META_avail)) 4 (VZ (mask - first)).
Lemma memrepT : memrepX B X L A1 mc.
Proof.
pose proof m_facts as (Hu & Hsc' & G1 & G2 & G8 & Gimg & Mr & _). pose proof take_factsT as (I1 & _ & _ & HI2 & _ & _ & _ & _ & LB & _).
pose proof A1_facts as (Efp & Erg & Ear & M1 & Hu1 & _). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof pre_factsT as (_ & _ & P3 & _).
pose proof (mid_layout _ _ _ _ _ MID) as HL.
pose proof MRXX as MR0.
refine (memrepX_after B X X None (Some (m, idx)) U U A A1 L mem mc [cAV] [] (sp - ASF, ASF) HI HI2 HL Efp Erg MR0 _ _ _ _ _ _ _ _).
- intros c Hc. apply in_app_iff in Hc as [Hc|Hc].
+ destruct (imageX_upd_meta X A m am am1 c Mg ltac:(unfold am1; apply grp_same_avail) Hc) as [Hm|Ho]; [|right; apply in_app_iff; left; exact Ho].
assert (OLD : forall c', In c' (meta_slot_cells m (Some (MUsed am))) -> In c' (imageX X A ++ tail_cellsX X A)).
{ intros c' Hc'. exact (YN0p.old_meta_cell X None U A HI m am c' Hu Hc'). }
unfold am1, mask, first in Hm. unfold cAV, mask, first. destruct am as [pr nx mm av fr lst sc' ml ai sl] eqn:Eam.
cbn [am_prev am_next am_mem am_avail am_freed meta_bits am_last am_sc am_maplen am_set_avail meta_slot_cells] in Hm |- *.
cbn [meta_slot_cells am_prev am_next am_mem am_avail am_freed meta_bits am_last am_sc am_maplen] in OLD.
destruct Hm as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
[ right; apply OLD; left; reflexivity
| right; apply OLD; right; left; reflexivity
| right; apply OLD; do 2 right; left; reflexivity
| left; left; reflexivity
| right; apply OLD; do 4 right; left; reflexivity
| right; apply OLD; do 5 right; left; unfold meta_bits; cbn [am_last am_sc am_maplen]; reflexivity ].
+ right. apply in_app_iff. right. exact (tail_cellsX_upd_meta X A m am am1 c Mg ltac:(unfold am1; apply grp_same_avail) Hc).
- intros c [<-|[]]. left. apply (YN2o.meta_cells_in_areas X (Some (m, idx)) U A1 HI2 m am1 _ M1). unfold am1, cAV. destruct am; cbn. auto 10.
- intros c [<-|[]]. unfold cell_mem, cAV. cbn [mc_val mc_loc mc_w sval_num]. rewrite loc_addr_padd'. change (ms_segs B) with src0segs. unfold META_avail. fold M0.
intros k Hk. rewrite (rt_avail _ _ RET k Hk). reflexivity.
- intros c k [<-|[]] Hk _. unfold cAV in Hk |- *. cbn [mc_loc mc_w] in Hk |- *. rewrite loc_addr_padd'. fold M0. unfold META_avail.
apply writable_off_img_present; [lia | | apply (rt_win _ _ RET); lia]. intros Hi. apply (Gimg (M0 + 24 + Z.of_nat k)); [lia|]. apply in_img1_in_img. exact Hi.
- intros d c [].
- intros d a [].
- intros e He. cbn [fst]. pose proof (YN0p.footprint_hi X None U L A md HI (mid_syms _ _ _ _ _ MID) HctxT (mid_ledger _ _ _ _ _ MID) e He). unfold ASF in *. lia.
- intros a Ha Hno _ Hns.
assert (NW : ~ (M0 + 24 <= a < M0 + 28)).
{ intros W. apply (Hno cAV (or_introl eq_refl)). unfold in_range, cell_range, cAV. cbn [fst snd mc_loc mc_w]. rewrite loc_addr_padd'. fold M0. unfold META_avail. lia. }
assert (NS : ~ WS regs a) by (unfold WS; unfold in_range in Hns; cbn [fst snd] in Hns; fold sp; unfold ASF in *; lia).
pose proof (rt_out _ _ RET a Ha NS NW) as E. split; [apply mbyte_ext1; exact E|]. intros [b Hb]. exists b. rewrite E. exact Hb.
Qed.
Lemma midrepT : midrep B L A1 mc md.
Proof.
pose proof m_facts as (Hu & Hsc' & G1 & G2 & G8 & Gimg & Mr & _). pose proof take_factsT as (I1 & _ & _ & HI2 & _).
pose proof A1_facts as (Efp & Erg & Ear & M1 & Hu1 & UBe & UB & RX1 & _). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof (YN0p.off_img M0 Gimg) as GF.
pose proof pre_factsT as (_ & _ & P3 & _). pose proof (mid_syms _ _ _ _ _ MID) as SO.
split.
- exact SO.
- apply (proj1 (memrepX_nil B L A1 mc)). apply (proj2 (memrepX_X A1 mc RX1 (or_intror (ex_intro _ (Some (m, idx)) HI2)))). apply memrepT.
- unfold tail_geom. apply Forall_forall. intros c Hc k Hk.
assert (Hc' : In c (tail_cells A)).
{ pose proof (tail_cellsX_upd_meta [] A m am am1 c Mg ltac:(unfold am1; apply grp_same_avail)) as T. unfold tail_cellsX in T. rewrite !used_metasX_nil in T. exact (T Hc). }
apply (alloc_owned_same L A1 A _ (eq_sym Efp) (eq_sym UBe)). exact (proj1 (Forall_forall _ _) (mid_tailg _ _ _ _ _ MID) c Hc' k Hk).
- apply (YN26.statics_ok_ext B mem mc (mid_statics _ _ _ _ _ MID)). intros a Hs. apply mbyte_ext1.
pose proof (src0_img_range a (so_statics_img _ SO a Hs)) as Ra. apply (rt_out _ _ RET); [lia | unfold WS; fold sp; lia |].
intros W. apply (Gimg a); [lia|]. exact (so_statics_img _ SO a Hs).
- unfold A1. apply ledger_ok_upd_meta. exact (mid_ledger _ _ _ _ _ MID).
- eapply ledger_x_same_regions; [exact (mid_ledgerx _ _ _ _ _ MID) | exact Erg | reflexivity | reflexivity].
- unfold A1. apply (proj2 (layout_ok_upd_meta L m _ A)). exact (mid_layout _ _ _ _ _ MID).
- exact (mid_ctx _ _ _ _ _ MID).
- exact (mid_sec _ _ _ _ _ MID).
- exact (mid_md _ _ _ _ _ MID).
Qed.
Lemma rsvT : rsv_ok A1.
Proof.
pose proof m_facts as (Hu & _). pose proof take_factsT as (I1 & _ & _ & HI2 & I2 & _ & _ & _ & _ & Glen).
assert (SE : shape_eq am am1 idx) by (unfold am1; destruct am; cbn; repeat split; reflexivity).
destruct (inv_reserved HI2 m idx eq_refl) as (am_ & Hu_ & _ & Hfr_ & _).
pose proof (usedX_fun _ _ _ _ _ Hu_ (proj1 (proj2 (proj2 (proj2 (proj2 A1_facts)))))) as ->.
intros g0 am0 i fr Hin Hk. destruct (frames_upd A m am am1 idx g0 am0 i fr Mg SE Hfr_ Hin) as (am2 & Hin1 & Hst).
unfold reserved_of. rewrite <- Hst. apply (RSV g0 am2 i fr Hin1 Hk).
Qed.
Lemma POST_T1 : POST X L A regs mem md sc stk g (idx, A1) (mkCfg (mkst rg (getr regs 1) mc rom) md).
Proof.
pose proof (proj1 alloc_ceiling_val) as HCV. pose proof pre_factsT as (P1 & P2 & P3 & P4 & P5 & P6 & P7). pose proof md_factsT as (Mh & Mlz & Mmat).
pose proof m_facts as (Hu & Hsc' & G1 & G2 & G8 & Gimg & Mr & _). pose proof take_factsT as (I1 & _ & Hbit & HI2 & I2 & Hfit & _).
pose proof A1_facts as (Efp & Erg & Ear & M1 & Hu1 & UBe & UB & RX1 & USED).
exists L, rg, mc, md. split; [reflexivity|]. split; [apply midrepT|]. split; [unfold ama_ok, A1 in *; cbn; exact AMA|].
split; [unfold A1; apply (proj2 (bounded_upd_meta _ _ _)); exact BND|]. split; [apply rsvT|].
split; [unfold A1, am1; apply (span_ok_upd_set_avail A m am _ SPOK Mg)|]. split; [apply layout_le_refl|].
split; [exact (rt_pres _ _ RET)|]. split; [exists (m_vmmaps md); apply with_vmmaps_self; assumption|]. split.
{ intros x Hx _ NO _ _ NS. apply (rt_out _ _ RET x Hx).
- unfold WS. unfold call_scratch in NS. fold sp. unfold spZ in NS. fold sp in NS. intros W. apply NS. left. lia.
- intros W. apply NO. left. apply (YN2u.meta_bytes_owned X None U A L HI (mid_layout _ _ _ _ _ MID) m _ (MUsed am) Mg). unfold META_SIZE. unfold M0 in W. lia. }
split.
{ intros a Ha. unfold call_scratch in Ha. unfold spZ in Ha. fold sp in Ha.
destruct (Z_le_dec (sp - ASF) a) as [L1|L1]; [destruct (Z_lt_dec a sp) as [L2|L2]; [apply (rt_stk _ _ RET); unfold WS; fold sp; lia|]|].
- exfalso. destruct Ha as [Ha|Ha]; [lia|]. pose proof (src0_img_range a (src0_errno_img a Ha)). unfold ERRNO in *. lia.
- assert (Ha64 : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [lia | pose proof (src0_img_range a (src0_errno_img a Ha)); lia]).
apply (writable_ext1 mem); [apply (rt_out _ _ RET a Ha64); [unfold WS; fold sp; lia | intros W; destruct Ha as [Ha|Ha]; [lia | apply (Gimg a); [lia | exact (src0_errno_img a Ha)]]]|].
destruct Ha as [Ha|Ha]; [apply P5; lia | apply P7; exact Ha]. }
split; [exact (rt_10 _ _ RET)|].
split.
{
cbn [fst snd]. intros _ gg am' Hgg Mgg US. exfalso.
unfold A1 in Hgg. rewrite active_hd_upd_meta, Hhd in Hgg. injection Hgg as <-. rewrite M1 in Mgg. injection Mgg as <-.
replace (stride_of am1) with (stride_of am) in US by (unfold am1; destruct am; reflexivity). lia. }
split; [cbn [snd]; unfold A1; apply as_keep_upd_meta; rewrite Mg; discriminate | exact (rt_guard _ _ RET)].
Qed.
End p.
Theorem slice_T1 : forall fuel, mreal src0segs (mkCfg ms0 md) (alloc_slot (S (S fuel)) sc n A) (POST X L A regs mem md sc stk g).
Proof.
intros fuel. pose proof md_factsT as (Mh & Mlz & _). pose proof pre_factsT as (P1 & _). pose proof m_facts as (_ & _ & _ & _ & _ & _ & Mr & _).
rewrite alloc_slot_tree, (try_avail_fast sc A m am Hhd Mg Hav). cbn [ibind]. unfold after_try. cbn [fst snd].
replace (lowbit (am_avail am) =? 0) with false by (symmetry; apply Z.eqb_neq; pose proof (lowbit_le (am_avail am) ltac:(unfold mask in Mr; lia)); lia).
cbn [negb mreal]. change (set_metas _ A) with A1. change (ctz32 (lowbit (am_avail am))) with idx.
eapply SR_bind; [exact (reach_hd X U L A regs mem md sc n stk HI Hsc Hn MID PRE Hstk R10 R11 g Hg 0 0)|].
intros c1 (E & ms & -> & HS & HA & HF).
eapply SR_bind; [eapply (F1_run (E1_of E) ms md (F1_st_ok E ms HS HA HF) Mh Mlz)|].
intros c2 (ms1 & -> & HS1 & HFR). destruct (F1_post E ms HA HF ms1 HS1 HFR) as (SHAPE & Hra & Era & RET).
pose proof SSF1_shape as (Hpc & Hrv & _).
eapply (SR_final_retS (E1_of E) SSF1 ms1 md); [exact HS1 | exact Hrv | exact Hpc | exact Hra | rewrite Era; exact P1 | exact Mh | exact Mlz |].
rewrite Era. exact (POST_T1 (ms_regs ms1) (ms_mem ms1) RET).
Qed.
End T1.
End h.
End f.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
