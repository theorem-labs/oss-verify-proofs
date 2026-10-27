(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0o.v, with its module paths changed. *)
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0r.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition fmh_cell (v : option sptr) : mcell := MCell (LCtx CTX_free_meta_head) 8 (optr v).
Lemma ctx_cells_set_fmh s v c :
In c (ctx_cells (set_free_meta_head v s)) -> c = fmh_cell v \/ In c (ctx_cells s).
Proof.
intros Hc. unfold ctx_cells in *. cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk st_active st_usage st_unmap_seq st_bounces set_free_meta_head] in Hc.
apply in_app_iff in Hc as [H|Hc]; [| right; apply in_app_iff; right; exact Hc].
cbn [In] in H. unfold fmh_cell.
destruct H as [H|[H|[H|[H|H]]]]; try (right; apply in_app_iff; left; cbn; tauto). left. symmetry. exact H.
Qed.
Lemma fmh_cell_In s v : In (fmh_cell v) (ctx_cells (set_free_meta_head v s)).
Proof. unfold ctx_cells, fmh_cell. apply in_app_iff. left. cbn. tauto. Qed.
Lemma imageX_set_fmh Y s v c :
In c (imageX Y (set_free_meta_head v s)) -> c = fmh_cell v \/ In c (imageX Y s).
Proof.
intros Hc. unfold imageX in *. rewrite (areas_cells_ext' s) in Hc by reflexivity.
change (st_areas (set_free_meta_head v s)) with (st_areas s) in Hc.
change (used_metasX Y (set_free_meta_head v s)) with (used_metasX Y s) in Hc.
apply in_app_iff in Hc as [Hc|Hc].
- destruct (ctx_cells_set_fmh s v c Hc) as [H|H]; [left; exact H | right; apply in_app_iff; left; exact H].
- right. apply in_app_iff. right. exact Hc.
Qed.
Lemma tail_cellsX_set_fmh Y s v : tail_cellsX Y (set_free_meta_head v s) = tail_cellsX Y s.
Proof. reflexivity. Qed.
Lemma MT_set_fmh v s p : MT (set_free_meta_head v s) p = MT s p.
Proof. reflexivity. Qed.
Section i.
Variables (X : list sptr) (U : Z -> Z) (fuel : nat) (L : layout) (A s4 : astate) (g : sptr) (mi : option (nat * Z)).
Variables (regs regs1 : bvmap 5 word) (mem mem1 : word -> option byte) (md : Model) (gv : Z).
Variables (e : fentry) (x4 : mslot) (fc : fcase).
Hypothesis NF : ntmidF e (g :: X) fuel L A s4 g mi regs regs1 mem mem1 md gv.
Hypothesis HI4 : Inv (g :: X) None U s4.
Hypothesis Mg4 : MT s4 g = Some x4.
Hypothesis FC : fcase_facts (g :: X) s4 g fc.
Hypothesis AO4 : forall a, alloc_owned L s4 a -> alloc_owned L A a.
Let G := ptr_addr L g.
Let SP0 := spZ regs.
Definition h : sptr := fc_h g fc.
Definition hp : sptr := fc_hp g fc.
Let H := ptr_addr L h.
Let HP := ptr_addr L hp.
Definition v : fvar := vF fc.
Definition s5 : astate := sF g s4 fc.
Lemma HL4 : layout_ok L s4. Proof. exact (nf_layout _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF). Qed.
Lemma SO : syms_ok B1. Proof. exact (nf_syms _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF). Qed.
Lemma Hctx : ly_ctx L = CTX. Proof. exact (nf_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF). Qed.
Lemma MR4 : memrepX B1 (g :: X) L s4 mem1. Proof. exact (nf_rep _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF). Qed.
Lemma ST4 : statics_ok B1 mem1. Proof. exact (nf_statics _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF). Qed.
Lemma LG4 : ledger_ok B1 L s4 md. Proof. exact (nf_ledger _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF). Qed.
Definition key_factsF := key_facts (g :: X) None U L s4 md HI4 LG4.
Definition key_presentF := key_present (g :: X) None U L s4 mem1 md HI4 MR4 LG4.
Lemma Mh : exists x, MT s4 h = Some x.
Proof. unfold h. destruct fc as [|h0 hnx|h0 hp0 hnx hpp]; cbn [fc_h fcase_facts] in FC |- *; [exists x4; exact Mg4 | |]; destruct FC as (_ & M & _); eexists; exact M. Qed.
Lemma Mhp : exists x, MT s4 hp = Some x.
Proof.
unfold hp. destruct fc as [|h0 hnx|h0 hp0 hnx hpp]; cbn [fc_hp fcase_facts] in FC |- *; [exists x4; exact Mg4 | |].
- destruct FC as (_ & M & _); eexists; exact M.
- destruct FC as (_ & _ & _ & _ & _ & _ & M & _); eexists; exact M.
Qed.
Lemma g_factsF : 4096 <= G /\ G + 40 <= alloc_ceiling /\ G mod 8 = 0 /\ (forall y, G <= y < G + 40 -> ~ in_img B1 y).
Proof. destruct (key_factsF g _ Mg4) as (A1 & A2 & A3 & A4 & _). unfold G. auto. Qed.
Lemma h_factsF : 4096 <= H /\ H + 40 <= alloc_ceiling /\ H mod 8 = 0 /\ (forall y, H <= y < H + 40 -> ~ in_img B1 y).
Proof. destruct Mh as [x M]. destruct (key_factsF h _ M) as (A1 & A2 & A3 & A4 & _). unfold H. auto. Qed.
Lemma hp_factsF : 4096 <= HP /\ HP + 40 <= alloc_ceiling /\ HP mod 8 = 0 /\ (forall y, HP <= y < HP + 40 -> ~ in_img B1 y).
Proof. destruct Mhp as [x M]. destruct (key_factsF hp _ M) as (A1 & A2 & A3 & A4 & _). unfold HP. auto. Qed.
Lemma sp_factsF :
SP0 mod 16 = 0 /\ alloc_ceiling + 96 + 96 * Z.of_nat fuel <= SP0 /\ SP0 < 2 ^ 63 /\
(forall x, SP0 - 96 * Z.of_nat (S fuel) <= x < SP0 -> writable_at src0segs mem1 x).
Proof.
pose proof (nf_spf _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF) as (S1 & S2 & S3). pose proof (nf_stkw _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF) as W.
unfold NT_FRAME in *. unfold SP0. split; [exact S1|]. split; [lia|]. split; [exact S3|]. intros x Hx. apply W. lia.
Qed.
Definition xvF (k : nat) : Z :=
if (k <? 32)%nat then bv_unsigned (getr regs1 (nat_to_reg k))
else match k with
| 47%nat => gv mod 2 ^ 64
| 50%nat => H
| 51%nat => HP
| 80%nat => bv_unsigned (getr regs (nat_to_reg 1))
| 81%nat => bv_unsigned (getr regs (nat_to_reg 8))
| 82%nat => bv_unsigned (getr regs (nat_to_reg 9))
| 83%nat => bv_unsigned (getr regs (nat_to_reg 18))
| 84%nat => bv_unsigned (getr regs (nat_to_reg 19))
| _ => 0
end.
Lemma XR : forall k, 0 <= xvF k < 2 ^ 64.
Proof.
intros k. pose proof h_factsF as (H1 & H2 & _). pose proof hp_factsF as (P1 & P2 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
unfold xvF. destruct (k <? 32)%nat; [apply u64_range|].
assert (M64 : 0 <= gv mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
do 85 (destruct k as [|k]; [first [apply M64 | apply u64_range | unfold H, HP in *; lia] |]). lia.
Qed.
Lemma EGF : xvF (aGF e) = G.
Proof.
pose proof (nf_g _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF) as R. pose proof g_factsF as (G1 & G2 & _). pose proof (proj1 alloc_ceiling_val).
unfold xvF. destruct e; cbn [aGF Nat.ltb Nat.leb] in *; rewrite R; apply lit64_small; unfold G in *; lia.
Qed.
Lemma ESP : xvF 2 = SP0 - 96.
Proof.
pose proof (nf_sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF) as R. pose proof sp_factsF as (_ & S2 & S3 & _). pose proof (proj1 alloc_ceiling_val).
unfold xvF. cbn [Nat.ltb Nat.leb]. rewrite R. apply lit64_small. unfold SP0 in *. lia.
Qed.
Lemma EBASE : xvF (aBASE e) = mi_base L mi.
Proof.
pose proof (nf_base _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF) as R. pose proof (nf_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF) as [M _].
unfold xvF. destruct e; cbn [aBASE Nat.ltb Nat.leb] in *; rewrite R; apply lit64_small; lia.
Qed.
Lemma ELEN : xvF 11 = mi_len mi.
Proof.
pose proof (nf_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF) as R. pose proof (nf_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF) as [_ M].
unfold xvF. cbn [Nat.ltb Nat.leb]. rewrite R. apply lit64_small. lia.
Qed.
Ltac factsF := pose proof XR as XR0; pose proof EGF as EGF0; pose proof ESP as ESP0.
Lemma regsF_ok : regs_ok (EV xvF) (regs_lit [(18%nat, CTX); (9%nat, GUARD)]) regs1.
Proof.
pose proof (nf_s1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF) as R9. pose proof (nf_s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF) as R18.
apply regs_ok_lit. intros n Hn.
do 32 (destruct n as [|n]; [cbn [find fst Nat.eqb]; first [exact R9 | exact R18 | unfold xvF; cbn [Nat.ltb Nat.leb]; symmetry; apply Z_to_bv_bv_unsigned] |]). lia.
Qed.
Lemma atomsF_ok : atoms_ok (EV xvF) (f_atoms e v).
Proof.
factsF. pose proof g_factsF as (G1 & G2 & G8 & _). pose proof h_factsF as (H1 & H2 & H8 & _). pose proof hp_factsF as (P1 & P2 & P8 & _).
pose proof sp_factsF as (S16 & Sceil & S63 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
assert (M64 : forall z, 0 <= z mod 2 ^ 64 <= 2 ^ 64 - 1) by (intros z; pose proof (Z.mod_pos_bound z (2 ^ 64) ltac:(lia)); lia).
assert (UR : forall rr (r : bvmap 5 word), 0 <= bv_unsigned (getr r rr) <= 2 ^ 64 - 1) by (intros; pose proof (u64_range (getr r rr)); lia).
unfold f_atoms. apply atoms_ok_app.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite !(ew_EV xvF XR0). rewrite EGF0, ESP0.
unfold aGV, aE1, aE8, aE9, aE18, aE19, xvF. cbn [Nat.ltb Nat.leb]. unfold CEIL.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite ?Z.mod_1_r.
pose proof (M64 gv). unfold G, SP0 in *.
repeat split; try lia; try apply UR.
replace (spZ regs - 96) with (spZ regs + (-6) * 16) by lia. unfold spZ in *. rewrite Z_mod_plus_full. exact S16.
- unfold v, vF. destruct fc; cbn [atoms_ok]; [exact I| |]; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite !(ew_EV xvF XR0); unfold aH, aHP, xvF; cbn [Nat.ltb Nat.leb];
change (2 ^ 3) with 8; unfold H, HP in *; repeat split; lia.
Qed.
Lemma factsF_ok : facts_ok (EV xvF) (mkFacts (f_atoms e v) [] []).
Proof. split; [apply atomsF_ok | split; exact I]. Qed.
Lemma frame_bytes :
bytes_are mem1 (SP0 - 48) 8 gv /\
bytes_are mem1 (SP0 - 40) 8 (bv_unsigned (getr regs (nat_to_reg 19))) /\
bytes_are mem1 (SP0 - 32) 8 (bv_unsigned (getr regs (nat_to_reg 18))) /\
bytes_are mem1 (SP0 - 24) 8 (bv_unsigned (getr regs (nat_to_reg 9))) /\
bytes_are mem1 (SP0 - 16) 8 (bv_unsigned (getr regs (nat_to_reg 8))) /\
bytes_are mem1 (SP0 - 8) 8 (bv_unsigned (getr regs (nat_to_reg 1))).
Proof. exact (nf_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF). Qed.
Lemma rok_gF : region_ok src0segs (EV xvF) mem1 (reg_gF e).
Proof.
factsF. pose proof g_factsF as (G1 & G2 & G8 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_gF]; rewrite (base_val_EV _ XR0), EGF0; [unfold G in *; lia | unfold G in *; lia | | apply Forall_nil].
intros o Ho. apply present_writable. apply (key_presentF g _ _ Mg4). unfold G. lia.
Qed.
Lemma rok_fstk : region_ok src0segs (EV xvF) mem1 reg_fstk.
Proof.
factsF. pose proof sp_factsF as (S16 & Sceil & S63 & WSTK). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof frame_bytes as (F48 & F40 & F32 & F24 & F16 & F8).
assert (UR : forall rr, 0 <= bv_unsigned (getr regs rr) < 2 ^ (8 * Z.of_N 8)) by (intros; cbn; pose proof (u64_range (getr regs rr)); lia).
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_fstk fstk_chunks]; rewrite (base_val_EV _ XR0), ESP0; [unfold SP0 in *; lia | unfold SP0 in *; lia | intros o Ho; apply WSTK; lia |].
repeat apply Forall_cons; [| | | | | | apply Forall_nil].
- apply (chunk_ok_val _ _ _ _ 8%N _ (gv mod 2 ^ 64)); [apply (U_off0 _ XR0) | apply M64w | intros kk Hkk; rewrite le_byte_mod64; replace (SP0 - 96 + 48) with (SP0 - 48) by lia; exact (F48 kk Hkk)].
- apply (chunk_ok_val _ _ _ _ 8%N _ (bv_unsigned (getr regs (nat_to_reg 19)))); [apply (U_off0 _ XR0) | apply UR | replace (SP0 - 96 + 56) with (SP0 - 40) by lia; exact F40].
- apply (chunk_ok_val _ _ _ _ 8%N _ (bv_unsigned (getr regs (nat_to_reg 18)))); [apply (U_off0 _ XR0) | apply UR | replace (SP0 - 96 + 64) with (SP0 - 32) by lia; exact F32].
- apply (chunk_ok_val _ _ _ _ 8%N _ (bv_unsigned (getr regs (nat_to_reg 9)))); [apply (U_off0 _ XR0) | apply UR | replace (SP0 - 96 + 72) with (SP0 - 24) by lia; exact F24].
- apply (chunk_ok_val _ _ _ _ 8%N _ (bv_unsigned (getr regs (nat_to_reg 8)))); [apply (U_off0 _ XR0) | apply UR | replace (SP0 - 96 + 80) with (SP0 - 16) by lia; exact F16].
- apply (chunk_ok_val _ _ _ _ 8%N _ (bv_unsigned (getr regs (nat_to_reg 1)))); [apply (U_off0 _ XR0) | apply UR | replace (SP0 - 96 + 88) with (SP0 - 8) by lia; exact F8].
Qed.
Lemma rok_guardF : region_ok src0segs (EV xvF) mem1 reg_guard.
Proof.
factsF. pose proof (nf_guard _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF) as Hgv.
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_guard base_val]; unfold GUARD, src0_D_stack_chk_guard; [lia | lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 8%N _ (gv mod 2 ^ 64)); [apply (U_off0 _ XR0) | apply M64w |].
intros kk Hkk. rewrite le_byte_mod64. exact (Hgv kk Hkk).
Qed.
Lemma head_val : optrZ L (st_free_meta_head s4) = match fc with FC0 => 0 | _ => H end.
Proof. unfold H, h. destruct fc; cbn [fcase_facts fc_h] in FC |- *; [rewrite FC; reflexivity | |]; destruct FC as (-> & _); reflexivity. Qed.
Lemma rok_fhd : region_ok src0segs (EV xvF) mem1 (reg_fhd v).
Proof.
factsF. pose proof SO as SO0. pose proof h_factsF as (H1 & H2 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof (ctx_fmh_cell (g :: X) L s4 mem1 Hctx MR4) as HB. rewrite head_val in HB.
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_fhd base_val]; [unfold CTX, src0_D_malloc_context; lia | unfold CTX, src0_D_malloc_context; lia | |].
- intros o Ho. apply (ctx_writable mem1 SO0). unfold v, vF in Ho. unfold CTX_SIZE. destruct fc; lia.
- apply Forall_cons; [| apply Forall_nil]. unfold v, vF. destruct fc.
+ apply (chunk_ok_val _ _ _ _ 8%N _ 0); [apply U_lit | cbn; lia | rewrite Z.add_0_l; exact HB].
+ apply (chunk_ok_val _ _ _ _ 8%N _ H); [apply (U_off0 _ XR0) | change (8 * Z.of_N 8) with 64; unfold H in *; lia | rewrite Z.add_0_l; exact HB].
+ apply (chunk_ok_val _ _ _ _ 8%N _ H); [apply (U_off0 _ XR0) | change (8 * Z.of_N 8) with 64; unfold H in *; lia | rewrite Z.add_0_l; exact HB].
Qed.
Lemma vmem_facts :
match fc with
| FC0 => True
| FC1a _ _ => bytes_are mem1 (H + 0) 8 H
| FC1b _ _ _ _ => bytes_are mem1 (H + 0) 8 HP
end.
Proof.
unfold H, HP, h, hp. destruct fc as [|h0 hnx|h0 hp0 hnx hpp]; cbn [fcase_facts fc_h fc_hp] in FC |- *; [exact I | |].
- destruct FC as (_ & M & _). pose proof (free_meta_bytes (g :: X) None U L s4 mem1 HI4 MR4 h0 _ _ M) as (B0 & _). exact B0.
- destruct FC as (_ & M & _). pose proof (free_meta_bytes (g :: X) None U L s4 mem1 HI4 MR4 h0 _ _ M) as (B0 & _). exact B0.
Qed.
Lemma h_present y : H <= y < H + 40 -> present mem1 y.
Proof. destruct Mh as [x M]. intros Hy. exact (key_presentF h _ _ M Hy). Qed.
Lemma hp_present y : HP <= y < HP + 40 -> present mem1 y.
Proof. destruct Mhp as [x M]. intros Hy. exact (key_presentF hp _ _ M Hy). Qed.
Lemma rok_vmem : Forall (region_ok src0segs (EV xvF) mem1) (f_vmem v).
Proof.
factsF. pose proof h_factsF as (H1 & H2 & _). pose proof hp_factsF as (P1 & P2 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof vmem_facts as VF. pose proof h_present as HPR. pose proof hp_present as PPR.
unfold v, vF. destruct fc as [|h0 hnx|h0 hp0 hnx hpp]; cbn [f_vmem]; [apply Forall_nil | |].
- apply Forall_cons; [| apply Forall_nil].
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks]; rewrite (base_val_EV _ XR0); unfold aH, xvF; cbn [Nat.ltb Nat.leb]; [lia | lia | |].
+ intros o Ho. apply present_writable. apply HPR. lia.
+ apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 8%N _ H); [apply (U_off0 _ XR0) | change (8 * Z.of_N 8) with 64; lia | exact VF].
- apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
+ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks]; rewrite (base_val_EV _ XR0); unfold aH, xvF; cbn [Nat.ltb Nat.leb]; [lia | lia | |].
* intros o Ho. apply present_writable. apply HPR. lia.
* apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 8%N _ HP); [apply (U_off0 _ XR0) | change (8 * Z.of_N 8) with 64; lia | exact VF].
+ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks]; rewrite (base_val_EV _ XR0); unfold aHP, xvF; cbn [Nat.ltb Nat.leb]; [lia | lia | | apply Forall_nil].
intros o Ho. apply present_writable. apply PPR. lia.
Qed.
Lemma regionsF_ok : Forall (region_ok src0segs (EV xvF) mem1) (f_mem e v).
Proof.
unfold f_mem. apply Forall_app. split; [| apply rok_vmem].
repeat apply Forall_cons; [apply rok_gF | apply rok_fstk | apply rok_guardF | apply rok_fhd | apply Forall_nil].
Qed.
Lemma apartF :
match fc with FC0 => True | _ => G + 40 <= H \/ H + 40 <= G end /\
match fc with FC1b _ _ _ _ => (G + 40 <= HP \/ HP + 40 <= G) /\ (H + 40 <= HP \/ HP + 40 <= H) | _ => True end.
Proof.
pose proof HL4 as HL0. unfold G, H, HP, h, hp.
destruct fc as [|h0 hnx|h0 hp0 hnx hpp]; cbn [fcase_facts fc_h fc_hp] in FC |- *; [split; exact I | |].
- destruct FC as (_ & M & _ & Hne). split; [| exact I]. apply (keys_apart (g :: X) None U L s4 HI4 HL0 g h0 _ _ Mg4 M). intros E; exact (Hne (eq_sym E)).
- destruct FC as (_ & M & _ & Hne & Hph & Hpg & Mp & _). split; [| split].
+ apply (keys_apart (g :: X) None U L s4 HI4 HL0 g h0 _ _ Mg4 M). intros E; exact (Hne (eq_sym E)).
+ apply (keys_apart (g :: X) None U L s4 HI4 HL0 g hp0 _ _ Mg4 Mp). intros E; exact (Hpg (eq_sym E)).
+ apply (keys_apart (g :: X) None U L s4 HI4 HL0 h0 hp0 _ _ M Mp). intros E; exact (Hph (eq_sym E)).
Qed.
Lemma pdF : pairwise_disjoint (EV xvF) (f_mem e v).
Proof.
factsF. pose proof g_factsF as (G1 & G2 & G8 & Gimg). pose proof h_factsF as (H1 & H2 & H8 & Himg). pose proof hp_factsF as (P1 & P2 & P8 & Pimg).
pose proof sp_factsF as (S16 & Sceil & S63 & WS). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof (off_img G Gimg) as GI. pose proof (off_img H Himg) as HI. pose proof (off_img HP Pimg) as PI. pose proof apartF as [AP1 AP2].
clear Gimg Himg Pimg WS G8 H8 P8 S16.
unfold f_mem, v, vF.
destruct fc; cbn [app pairwise_disjoint all_disjoint f_vmem]; unfold extent_disjoint;
cbn [r_base r_lo r_hi reg_gF reg_fstk reg_guard reg_fhd]; rewrite !(base_val_EV _ XR0); cbn [base_val];
rewrite EGF0, ESP0; unfold xvF, aH, aHP; cbn [Nat.ltb Nat.leb];
unfold GUARD, src0_D_stack_chk_guard, CTX, src0_D_malloc_context; unfold G, H, HP, SP0 in *;
clear XR0 EGF0 ESP0 NF HI4 Mg4 FC AO4; repeat split;
first [ (clear HI PI AP1 AP2; lia) | (clear GI AP1 AP2; lia) | (clear GI HI PI; lia) ].
Qed.
Theorem memF_ok : mem_ok src0segs (EV xvF) mem1 (f_mem e v).
Proof.
split; [unfold v, vF; destruct e, fc; vm_compute; reflexivity|]. split; [apply regionsF_ok | apply pdF].
Qed.
Definition pcF : Z := match e with FE_XF => XF | FE_RET2 => XJ end.
Theorem A4_entry_st_ok :
st_ok src0segs (EV xvF) (ss_F e v) (mkst regs1 (Z_to_bv 64 pcF) mem1 (seg_rom src0segs)).
Proof.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts ss_F resv_denot].
split; [reflexivity|]. split; [unfold pcF; destruct e; reflexivity|].
repeat (split; [reflexivity|]). split; [apply regsF_ok|]. split; [apply memF_ok | apply factsF_ok].
Qed.
Lemma h_eq : match fc with FC0 => h = g /\ hp = g | FC1a h0 _ => h = h0 /\ hp = h0 | FC1b h0 hp0 _ _ => h = h0 /\ hp = hp0 end.
Proof. clear FC. unfold h, hp. destruct fc; cbn; auto. Qed.
Lemma Hhg : match fc with FC0 => True | _ => h <> g end /\ match fc with FC1b _ _ _ _ => hp <> g /\ hp <> h | _ => True end.
Proof. unfold h, hp. destruct fc; cbn [fcase_facts fc_h fc_hp] in FC |- *; [split; exact I | |]; [destruct FC as (_&_&_&N); auto | destruct FC as (_&_&_&N1&N2&N3&_); auto]. Qed.
Lemma s5_facts :
MT s5 g = Some (MFree (Some hp) (Some h)) /\
footprint s5 = footprint s4 /\ st_regions s5 = st_regions s4 /\ st_areas s5 = st_areas s4 /\
match fc with
| FC0 => s5 = set_free_meta_head (Some g) (upd_meta g (MFree (Some g) (Some g)) s4)
| FC1a _ _ => s5 = upd_meta h (MFree (Some g) (Some g)) (upd_meta g (MFree (Some h) (Some h)) s4) /\ MT s5 h = Some (MFree (Some g) (Some g))
| FC1b _ _ hnx hpp => s5 = upd_meta h (MFree (Some g) hnx) (upd_meta hp (MFree hpp (Some g)) (upd_meta g (MFree (Some hp) (Some h)) s4)) /\
MT s5 h = Some (MFree (Some g) hnx) /\ MT s5 hp = Some (MFree hpp (Some g))
end.
Proof.
pose proof Hhg as [N1 N2]. pose proof h_eq as HE. unfold s5, sF.
destruct fc as [|h0 hnx|h0 hp0 hnx hpp]; destruct HE as [E1 E2]; unfold A_F0, A_F1a, A_F1b.
- rewrite E1, E2. split; [apply MT_upd_same|]. repeat split; reflexivity.
- rewrite E2, <- E1. split; [rewrite MT_upd_other by (intros E; exact (N1 (eq_sym E))); apply MT_upd_same|].
rewrite !footprint_upd_meta. repeat split; try reflexivity. apply MT_upd_same.
- rewrite <- E1, <- E2. destruct N2 as [N2 N3]. split; [rewrite MT_upd_other by (intros E; exact (N1 (eq_sym E))); rewrite MT_upd_other by (intros E; exact (N2 (eq_sym E))); apply MT_upd_same|].
rewrite !footprint_upd_meta. repeat split; try reflexivity; [apply MT_upd_same|].
rewrite MT_upd_other by exact N3. apply MT_upd_same.
Qed.
Definition NEWg : list mcell := meta_slot_cells g (Some (MFree (Some hp) (Some h))).
Definition NEWo : list mcell :=
match fc with
| FC0 => [fmh_cell (Some g)]
| FC1a _ _ => [MCell (LMem (padd h 0)) 8 (VP g); MCell (LMem (padd h 8)) 8 (VP g)]
| FC1b _ _ _ _ => [MCell (LMem (padd h 0)) 8 (VP g); MCell (LMem (padd hp 8)) 8 (VP g)]
end.
Definition NEW : list mcell := NEWg ++ NEWo.
Hypothesis HI5 : Inv X None U s5.
Lemma cellsF c : In c (imageX X s5 ++ tail_cellsX X s5) -> In c NEW \/ In c (imageX (g :: X) s4 ++ tail_cellsX (g :: X) s4).
Proof.
pose proof s5_facts as (M5 & _ & _ & _ & S5). pose proof Hhg as [N1 N2]. pose proof Mh as [xh Mh0]. pose proof Mhp as [xhp Mhp0]. pose proof HI4 as HI. pose proof Mg4 as Mg.
pose proof (proj1 (inv_keys HI5)) as ND5. pose proof FC as FC0'.
assert (NU : forall a, MT s5 g <> Some (MUsed a)) by (intros a; rewrite M5; discriminate).
rewrite <- (imageX_uncons X g s5 NU ND5), <- (tail_cellsX_uncons X g s5 NU ND5).
assert (Ng : MT s4 g <> None) by (rewrite Mg; discriminate).
assert (NF' : forall pr nx a, MFree pr nx <> MUsed a) by (intros; discriminate).
assert (OLD : forall q x c', MT s4 q = Some x -> In c' (meta_slot_cells q (Some x)) -> In c' (imageX (g :: X) s4 ++ tail_cellsX (g :: X) s4)).
{ intros q x c' M Hc'. exact (key_old_cell (g :: X) None U s4 HI q x c' M Hc'). }
pose proof h_eq as HE. unfold NEW, NEWg, NEWo. intros Hc.
destruct fc as [|h0 hnx|h0 hp0 hnx hpp]; cbn [fcase_facts] in FC0'.
- rewrite S5 in Hc. apply in_app_iff in Hc as [Hc|Hc].
+ destruct (imageX_set_fmh _ _ _ c Hc) as [->|Hc1]; [left; apply in_app_iff; right; left; reflexivity|].
destruct (imageX_upd_notused (g :: X) s4 g _ c Ng (NF' _ _) Hc1) as [K|K]; [| right; apply in_app_iff; left; exact K].
destruct HE as [E1 E2]. rewrite E1, E2. left. apply in_app_iff. left. exact K.
+ rewrite tail_cellsX_set_fmh in Hc. right. apply in_app_iff. right. exact (tail_cellsX_upd_notused (g :: X) s4 g _ c Ng (NF' _ _) Hc).
- destruct S5 as [S5 M5h]. destruct FC0' as (_ & Mh4 & _). destruct HE as [E1 E2]. rewrite <- E1 in Mh4. rewrite S5 in Hc.
assert (Nh : MT (upd_meta g (MFree (Some h) (Some h)) s4) h <> None) by (rewrite MT_upd_other by exact N1; rewrite Mh4; discriminate).
apply in_app_iff in Hc as [Hc|Hc].
+ destruct (imageX_upd_notused (g :: X) _ h _ c Nh (NF' _ _) Hc) as [K|Hc1].
{ cbn [meta_slot_cells optr] in K. destruct K as [<-|[<-|K]]; [left; apply in_app_iff; right; cbn; tauto | left; apply in_app_iff; right; cbn; tauto |].
right. apply (OLD h _ _ Mh4). cbn [meta_slot_cells]. cbn in K |- *. tauto. }
destruct (imageX_upd_notused (g :: X) s4 g _ c Ng (NF' _ _) Hc1) as [K|K]; [| right; apply in_app_iff; left; exact K].
left. apply in_app_iff. left. rewrite E2, <- E1. exact K.
+ right. apply in_app_iff. right. exact (tail_cellsX_upd_notused (g :: X) s4 g _ c Ng (NF' _ _ ) (tail_cellsX_upd_notused (g :: X) _ h _ c Nh (NF' _ _) Hc)).
- destruct S5 as (S5 & M5h & M5p). destruct N2 as [N2 N3]. destruct FC0' as (_ & Mh4 & _ & _ & _ & _ & Mp4 & _). destruct HE as [E1 E2]. rewrite <- E1 in Mh4. rewrite <- E2 in Mp4, Mh4. rewrite S5 in Hc.
assert (Np : MT (upd_meta g (MFree (Some hp) (Some h)) s4) hp <> None) by (rewrite MT_upd_other by exact N2; rewrite Mp4; discriminate).
assert (Nh : MT (upd_meta hp (MFree hpp (Some g)) (upd_meta g (MFree (Some hp) (Some h)) s4)) h <> None).
{ rewrite MT_upd_other by (intros E; exact (N3 (eq_sym E))). rewrite MT_upd_other by exact N1. rewrite Mh4. discriminate. }
apply in_app_iff in Hc as [Hc|Hc].
+ destruct (imageX_upd_notused (g :: X) _ h _ c Nh (NF' _ _) Hc) as [K|Hc1].
{ cbn [meta_slot_cells optr] in K. destruct K as [<-|K]; [left; apply in_app_iff; right; cbn; tauto |].
right. apply (OLD h _ _ Mh4). cbn [meta_slot_cells]. cbn in K |- *. tauto. }
destruct (imageX_upd_notused (g :: X) _ hp _ c Np (NF' _ _) Hc1) as [K|Hc2].
{ cbn [meta_slot_cells optr] in K. destruct K as [K|[<-|K]]; [| left; apply in_app_iff; right; cbn; tauto |].
- right. apply (OLD hp _ _ Mp4). cbn [meta_slot_cells]. cbn in K |- *. tauto.
- right. apply (OLD hp _ _ Mp4). cbn [meta_slot_cells]. cbn in K |- *. tauto. }
destruct (imageX_upd_notused (g :: X) s4 g _ c Ng (NF' _ _) Hc2) as [K|K]; [| right; apply in_app_iff; left; exact K].
left. apply in_app_iff. left. exact K.
+ right. apply in_app_iff. right.
exact (tail_cellsX_upd_notused (g :: X) s4 g _ c Ng (NF' _ _) (tail_cellsX_upd_notused (g :: X) _ hp _ c Np (NF' _ _) (tail_cellsX_upd_notused (g :: X) _ h _ c Nh (NF' _ _) Hc))).
Qed.
Lemma new_homeF c : In c NEW -> In c (areas_cells s5 (st_areas s5)) \/ In c (ctx_cells s5).
Proof.
pose proof s5_facts as (M5 & _ & _ & _ & S5). pose proof HI5 as HI5'. clear HI5.
unfold NEW, NEWg, NEWo. intros Hn. apply in_app_iff in Hn as [Hn|Hn].
- left. exact (slot_cells_in_areas X None U s5 HI5' g _ c M5 Hn).
- destruct fc as [|h0 hnx|h0 hp0 hnx hpp].
+ destruct Hn as [<-|[]]. right. rewrite S5. apply fmh_cell_In.
+ destruct S5 as [S5 M5h]. left. apply (slot_cells_in_areas X None U s5 HI5' h _ c M5h). cbn. cbn in Hn. tauto.
+ destruct S5 as (S5 & M5h & M5p). left. destruct Hn as [<-|[<-|[]]].
* apply (slot_cells_in_areas X None U s5 HI5' h _ _ M5h). cbn. tauto.
* apply (slot_cells_in_areas X None U s5 HI5' hp _ _ M5p). cbn. tauto.
Qed.
Section j.
Variable ms2 : machine_state.
Hypothesis HS2 : st_ok src0segs (EV xvF) (SSF e v) ms2.
Hypothesis HF2 : frame_of (EV xvF) (f_mem e v) mem1 (ms_mem ms2).
Let mem2 := ms_mem ms2.
Let regs2 := ms_regs ms2.
Lemma post_shapeF : ms2 = mkst regs2 (Z_to_bv 64 NT_RET) mem2 (seg_rom src0segs) /\ sr_get (ss_regs (SSF e v)) 1 = SOff aE1 0.
Proof.
pose proof (SSF_shape e v) as SH. pose proof HS2 as HS. remember (SSF e v) as ss eqn:Ess. clear Ess.
destruct SH as (Hpc & Hrv & Hview & _). split.
- rewrite <- Hpc. apply (st_ok_mkst src0segs _ _ _ HS Hrv).
- unfold view, kept, keptU in Hview. cbn [map app] in Hview. injection Hview as V1 _. exact V1.
Qed.
Lemma post_regsF :
getr regs2 (nat_to_reg 10) = Z_to_bv 64 (mi_base L mi) /\ getr regs2 (nat_to_reg 11) = Z_to_bv 64 (mi_len mi) /\
regs_preserved regs regs2.
Proof.
factsF. pose proof EBASE as EB. pose proof ELEN as EL. pose proof (nf_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF) as KEEP.
pose proof sp_factsF as (_ & Sceil & S63 & _). pose proof (proj1 alloc_ceiling_val).
pose proof (SSF_shape e v) as SH. pose proof HS2 as HS. remember (SSF e v) as ss eqn:Ess. clear Ess.
destruct SH as (Hpc & Hrv & Hview & _).
pose proof (fun r => st_ok_reg src0segs _ _ ms2 r HS) as RR.
unfold view, kept, keptU in Hview. cbn [map app] in Hview.
injection Hview as V1 V2 V8 V9 V10 V11 V18 V19 V3 V4 V20 V21 V22 V23 V24 V25 V26 V27.
assert (NR : forall k, (1 <= k <= 31)%nat -> nat_to_reg k = Z_to_bv 5 (Z.of_nat k)).
{ intros k Hk. clear -Hk. apply bv_eq. rewrite nat_to_reg_unsigned by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity. }
assert (K : forall k ex (V : sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat k)) = ex), (1 <= k <= 31)%nat -> getr regs2 (nat_to_reg k) = sv_denot (EV xvF) ex).
{ intros k ex V Hk. unfold regs2. rewrite (NR k Hk), (RR (Z_to_bv 5 (Z.of_nat k))), V. reflexivity. }
split; [rewrite (K 10%nat _ V10 ltac:(lia)), (den_off0 _ XR0), EB; reflexivity|].
split; [rewrite (K 11%nat _ V11 ltac:(lia)), (den_off0 _ XR0), EL; reflexivity|].
intros r Hr. destruct (callee_saved_cases r Hr) as [Hr32 Hin]. rewrite (Z_to_bv5_nat_to_reg r Hr32).
assert (KE : forall k (V : sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat k)) = SOff k 0), (1 <= k <= 31)%nat -> In k kept_regs -> getr regs2 (nat_to_reg k) = getr regs (nat_to_reg k)).
{ intros k V Hk HK. rewrite (K k _ V Hk), (den_off0 _ XR0). unfold xvF.
replace (k <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite Z_to_bv_bv_unsigned. apply KEEP. exact HK. }
assert (KX : forall k a (V : sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat k)) = SOff a 0), (1 <= k <= 31)%nat -> (32 <= a)%nat -> xvF a = bv_unsigned (getr regs (nat_to_reg k)) -> getr regs2 (nat_to_reg k) = getr regs (nat_to_reg k)).
{ intros k a V Hk Ha Ex. rewrite (K k _ V Hk), (den_off0 _ XR0), Ex. apply Z_to_bv_bv_unsigned. }
cbn [In] in Hin.
destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]]]]; rewrite <- E.
- exfalso. unfold callee_saved in Hr. lia.
- rewrite (K 2%nat _ V2 ltac:(lia)). rewrite (den_off _ XR0) by (rewrite ESP0; unfold SP0 in *; lia). rewrite ESP0. unfold SP0, spZ. replace (bv_unsigned (getr regs 2) - 96 + 96) with (bv_unsigned (getr regs 2)) by lia. apply Z_to_bv_bv_unsigned.
- apply (KE 3%nat V3); [lia | cbn; tauto].
- apply (KE 4%nat V4); [lia | cbn; tauto].
- apply (KX 8%nat aE8 V8); [lia | unfold aE8; lia | reflexivity].
- apply (KX 9%nat aE9 V9); [lia | unfold aE9; lia | reflexivity].
- apply (KX 18%nat aE18 V18); [lia | unfold aE18; lia | reflexivity].
- apply (KX 19%nat aE19 V19); [lia | unfold aE19; lia | reflexivity].
- apply (KE 20%nat V20); [lia | cbn; tauto].
- apply (KE 21%nat V21); [lia | cbn; tauto].
- apply (KE 22%nat V22); [lia | cbn; tauto].
- apply (KE 23%nat V23); [lia | cbn; tauto].
- apply (KE 24%nat V24); [lia | cbn; tauto].
- apply (KE 25%nat V25); [lia | cbn; tauto].
- apply (KE 26%nat V26); [lia | cbn; tauto].
- apply (KE 27%nat V27); [lia | cbn; tauto].
Qed.
Lemma final_regionsF :
region_ok src0segs (EV xvF) mem2 (YP09.mkRegion (Some (aGF e)) 0 40 0 40 (gF_chunks e v)) /\
region_ok src0segs (EV xvF) mem2 (YP09.mkRegion (Some 2%nat) 0 96 8 48 fstk_out) /\
region_ok src0segs (EV xvF) mem2 (match v with F0 => YP09.mkRegion None (CTX + 16) (CTX + 24) (CTX + 16) (CTX + 24) [mkChunk (CTX + 16) (CVal 8 (SOff (aGF e) 0))] | _ => reg_fhd v end) /\
Forall (region_ok src0segs (EV xvF) mem2) (f_vmem_out e v).
Proof.
pose proof (SSF_shape e v) as SH. pose proof HS2 as HS. remember (SSF e v) as ss eqn:Ess. clear Ess.
destruct SH as (_ & _ & _ & Hm). pose proof (st_ok_mem_ok _ _ _ _ HS) as (_ & ROK & _). rewrite Hm in ROK. unfold f_mem_out in ROK.
apply Forall_app in ROK as [R1 R2].
apply Forall_cons_iff in R1 as [Ra R1]. apply Forall_cons_iff in R1 as [Rb R1]. apply Forall_cons_iff in R1 as [_ R1]. apply Forall_cons_iff in R1 as [Rd _].
unfold mem2. auto.
Qed.
Lemma zero_chunk_cell base off (w : nat) loc d :
chunk_ok src0segs (EV xvF) mem2 base (mkChunk off (CVal 8 (SLit 0))) ->
loc_addr L loc = base + off + d -> 0 <= d -> d + Z.of_nat w <= 8 ->
cell_mem B1 L mem2 (MCell loc w (VZ 0)).
Proof.
intros Hc Hloc Hd Hw. unfold cell_mem. cbn [mc_val mc_loc mc_w sval_num]. rewrite Hloc. intros k Hk.
destruct (Hc (d + Z.of_nat k) ltac:(cbn; lia)) as (b & Eb & Mb). cbn [c_off c_val cbyte] in Eb, Mb.
enough (E : mbyte src0segs mem2 (base + off + d + Z.of_nat k) = Some (Z_to_bv 8 (le_byte 0 w k))) by exact E.
replace (base + off + d + Z.of_nat k) with (base + off + (d + Z.of_nat k)) by lia. rewrite Mb. injection Eb as <-. f_equal.
unfold byte_of_word. change (bv_unsigned (Z_to_bv 64 0)) with 0. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite !Z.shiftr_0_l. reflexivity.
Qed.
Lemma EH : xvF aH = H. Proof. reflexivity. Qed.
Lemma EHP : xvF aHP = HP. Proof. reflexivity. Qed.
Lemma new_memF n : In n NEW -> cell_mem B1 L mem2 n.
Proof.
factsF. pose proof g_factsF as (G1 & G2 & _). pose proof h_factsF as (H1 & H2 & _). pose proof hp_factsF as (P1 & P2 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof h_eq as HE. pose proof Hctx as HC. destruct final_regionsF as (Rg & _ & Rd & Rv).
assert (C8 : forall (base : Z) (off : Z) (k : nat) (qq rr : sptr),
chunk_ok src0segs (EV xvF) mem2 base (mkChunk off (CVal 8 (SOff k 0))) -> xvF k = ptr_addr L rr ->
ptr_addr L qq + off = base + off -> cell_mem B1 L mem2 (MCell (LMem (padd qq off)) 8 (VP rr))).
{ intros base off k qq rr C Hk Hb. eapply (chunk8_cell xvF L mem2 base off _ (ptr_addr L rr) _ _ C); [| rewrite loc_addr_padd; exact Hb | reflexivity | exact I].
rewrite (U_off0 _ XR0), Hk. symmetry. apply Z.mod_small. pose proof (XR0 k). lia. }
destruct Rg as (_ & _ & _ & Cg). cbn [r_chunks r_base] in Cg. rewrite (base_val_EV _ XR0), EGF0 in Cg.
unfold gF_chunks in Cg. apply Forall_app in Cg as [Cg1 Cg2].
apply Forall_cons_iff in Cg2 as [C32 Cg2]. apply Forall_cons_iff in Cg2 as [C24 Cg2]. apply Forall_cons_iff in Cg2 as [C16 _].
intros Hn. unfold NEW, NEWg, NEWo in Hn. apply in_app_iff in Hn as [Hn|Hn].
-
cbn [meta_slot_cells optr] in Hn. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hn.
destruct Hn as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
+ unfold v, vF in Cg1. destruct fc; destruct HE as [E1 E2]; apply Forall_cons_iff in Cg1 as [Ca Cg1]; apply Forall_cons_iff in Cg1 as [Cb _].
* apply (C8 G 0 (aGF e) g hp Cb); [rewrite EGF0, E2; reflexivity | reflexivity].
* apply (C8 G 0 aH g hp Ca); [rewrite EH, E2, <- E1; reflexivity | reflexivity].
* apply (C8 G 0 aHP g hp Ca); [rewrite EHP; reflexivity | reflexivity].
+ unfold v, vF in Cg1. destruct fc; destruct HE as [E1 E2]; apply Forall_cons_iff in Cg1 as [Ca Cg1]; apply Forall_cons_iff in Cg1 as [Cb _].
* apply (C8 G 8 (aGF e) g h Ca); [rewrite EGF0, E1; reflexivity | reflexivity].
* apply (C8 G 8 aH g h Cb); [rewrite EH; reflexivity | reflexivity].
* apply (C8 G 8 aH g h Cb); [rewrite EH; reflexivity | reflexivity].
+ apply (zero_chunk_cell G 16 8 _ 0 C16); [rewrite loc_addr_padd; unfold G; lia | lia | cbn; lia].
+ apply (zero_chunk_cell G 24 4 _ 0 C24); [rewrite loc_addr_padd; unfold G; lia | lia | cbn; lia].
+ apply (zero_chunk_cell G 24 4 _ 4 C24); [rewrite loc_addr_padd; unfold G; lia | lia | cbn; lia].
+ apply (zero_chunk_cell G 32 8 _ 0 C32); [rewrite loc_addr_padd; unfold G; lia | lia | cbn; lia].
- unfold v, vF in Rd, Rv. destruct fc.
+ destruct Hn as [<-|[]]. destruct Rd as (_ & _ & _ & Cd). cbn [r_chunks r_base base_val] in Cd. apply Forall_cons_iff in Cd as [Cd _].
unfold fmh_cell. eapply (chunk8_cell xvF L mem2 0 (CTX + 16) _ G _ _ Cd); [| cbn [loc_addr]; rewrite HC; unfold CTX_free_meta_head; lia | reflexivity | exact I].
rewrite (U_off0 _ XR0), EGF0. symmetry. apply Z.mod_small. unfold G in *. lia.
+ cbn [f_vmem_out] in Rv. apply Forall_cons_iff in Rv as [Ra _]. destruct Ra as (_ & _ & _ & Ca). cbn [r_chunks r_base] in Ca. rewrite (base_val_EV _ XR0), EH in Ca.
apply Forall_cons_iff in Ca as [C0 Ca]. apply Forall_cons_iff in Ca as [C8' _].
destruct Hn as [<-|[<-|[]]]; [apply (C8 H 0 (aGF e) h g C0) | apply (C8 H 8 (aGF e) h g C8')]; try reflexivity; exact EGF0.
+ cbn [f_vmem_out] in Rv. apply Forall_cons_iff in Rv as [Ra Rv]. apply Forall_cons_iff in Rv as [Rb _].
destruct Ra as (_ & _ & _ & Ca). cbn [r_chunks r_base] in Ca. rewrite (base_val_EV _ XR0), EH in Ca. apply Forall_cons_iff in Ca as [C0 _].
destruct Rb as (_ & _ & _ & Cb). cbn [r_chunks r_base] in Cb. rewrite (base_val_EV _ XR0), EHP in Cb. apply Forall_cons_iff in Cb as [C8' _].
destruct Hn as [<-|[<-|[]]]; [apply (C8 H 0 (aGF e) h g C0) | apply (C8 HP 8 (aGF e) hp g C8')]; try reflexivity; exact EGF0.
Qed.
Lemma off_img_presentF x o (m : word -> option byte) :
(forall y, x <= y < x + 40 -> ~ in_img B1 y) -> 4096 <= x -> x + 40 <= alloc_ceiling -> 0 <= o < 40 ->
writable_at src0segs m (x + o) -> present m (x + o).
Proof.
pose proof (proj1 alloc_ceiling_val). intros Himg Hx1 Hx2 Ho W. apply writable_off_img_present; [lia | | exact W].
intros Hi. apply (Himg (x + o)); [lia|]. apply in_img1_in_img. exact Hi.
Qed.
Lemma new_presentF n k : In n NEW -> (k < mc_w n)%nat -> (exists q, mc_loc n = LMem q) -> present mem2 (loc_addr L (mc_loc n) + Z.of_nat k).
Proof.
factsF. pose proof g_factsF as (G1 & G2 & G8 & Gimg). pose proof h_factsF as (H1 & H2 & H8 & Himg). pose proof hp_factsF as (P1 & P2 & P8 & Pimg).
destruct final_regionsF as (Rg & _ & _ & Rv).
destruct Rg as (_ & _ & Wg & _). cbn [r_base r_wlo r_whi] in Wg. rewrite (base_val_EV _ XR0), EGF0 in Wg.
intros Hn Hk Hl. unfold NEW, NEWg, NEWo in Hn. apply in_app_iff in Hn as [Hn|Hn].
- cbn [meta_slot_cells optr] in Hn. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hn.
assert (PG : forall dd w, n = MCell (LMem (padd g dd)) w (mc_val n) -> 0 <= dd -> dd + Z.of_nat w <= 40 -> present mem2 (loc_addr L (mc_loc n) + Z.of_nat k)).
{ intros dd w En Hdd Hw. rewrite En in Hk |- *. cbn [mc_loc mc_w] in Hk |- *. rewrite loc_addr_padd. fold G.
replace (G + dd + Z.of_nat k) with (G + (dd + Z.of_nat k)) by lia. apply (off_img_presentF G _ mem2 Gimg G1 G2); [lia|]. apply Wg. lia. }
destruct Hn as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
[apply (PG 0 8%nat) | apply (PG 8 8%nat) | apply (PG 16 8%nat) | apply (PG 24 4%nat) | apply (PG 28 4%nat) | apply (PG 32 8%nat)]; try reflexivity; cbn; lia.
- unfold v, vF in Rv. destruct fc.
+ destruct Hn as [<-|[]]. destruct Hl as [q Hq]. discriminate Hq.
+ cbn [f_vmem_out] in Rv. apply Forall_cons_iff in Rv as [Ra _]. destruct Ra as (_ & _ & Wa & _). cbn [r_base r_wlo r_whi] in Wa. rewrite (base_val_EV _ XR0) in Wa. change (xvF aH) with H in Wa.
destruct Hn as [<-|[<-|[]]]; cbn [mc_loc mc_w] in Hk |- *; rewrite loc_addr_padd; fold H.
* replace (H + 0 + Z.of_nat k) with (H + Z.of_nat k) by lia. apply (off_img_presentF H _ mem2 Himg H1 H2); [lia|]. apply Wa. lia.
* replace (H + 8 + Z.of_nat k) with (H + (8 + Z.of_nat k)) by lia. apply (off_img_presentF H _ mem2 Himg H1 H2); [lia|]. apply Wa. lia.
+ cbn [f_vmem_out] in Rv. apply Forall_cons_iff in Rv as [Ra Rv]. apply Forall_cons_iff in Rv as [Rb _].
destruct Ra as (_ & _ & Wa & _). cbn [r_base r_wlo r_whi] in Wa. rewrite (base_val_EV _ XR0) in Wa. change (xvF aH) with H in Wa.
destruct Rb as (_ & _ & Wb & _). cbn [r_base r_wlo r_whi] in Wb. rewrite (base_val_EV _ XR0) in Wb. change (xvF aHP) with HP in Wb.
destruct Hn as [<-|[<-|[]]]; cbn [mc_loc mc_w] in Hk |- *; rewrite loc_addr_padd; fold H HP.
* replace (H + 0 + Z.of_nat k) with (H + Z.of_nat k) by lia. apply (off_img_presentF H _ mem2 Himg H1 H2); [lia|]. apply Wa. lia.
* replace (HP + 8 + Z.of_nat k) with (HP + (8 + Z.of_nat k)) by lia. apply (off_img_presentF HP _ mem2 Pimg P1 P2); [lia|]. apply Wb. lia.
Qed.
Definition in_winF (a : Z) : Prop :=
(G <= a < G + 40) \/ (SP0 - 88 <= a < SP0 - 48) \/
match fc with
| FC0 => CTX + 16 <= a < CTX + 24
| FC1a _ _ => H <= a < H + 16
| FC1b _ _ _ _ => (H <= a < H + 8) \/ (HP + 8 <= a < HP + 16)
end.
Lemma wrange_winF a : in_wrange (EV xvF) (f_mem e v) a -> in_winF a.
Proof.
factsF. intros (r & Hr & Ha). unfold f_mem, v, vF in Hr. unfold in_winF.
apply in_app_iff in Hr as [Hr|Hr].
- cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]].
+ left. cbn [reg_gF r_base r_wlo r_whi] in Ha. rewrite (base_val_EV _ XR0), EGF0 in Ha. lia.
+ right; left. cbn [reg_fstk r_base r_wlo r_whi] in Ha. rewrite (base_val_EV _ XR0), ESP0 in Ha. lia.
+ exfalso. cbn [reg_guard r_base r_wlo r_whi base_val] in Ha. lia.
+ right; right. destruct fc; cbn [reg_fhd r_base r_wlo r_whi base_val] in Ha; lia.
- right; right. destruct fc; cbn [f_vmem In] in Hr; [destruct Hr | |].
+ destruct Hr as [<-|[]]. cbn [r_base r_wlo r_whi] in Ha. rewrite (base_val_EV _ XR0) in Ha. change (xvF aH) with H in Ha. lia.
+ destruct Hr as [<-|[<-|[]]]; cbn [r_base r_wlo r_whi] in Ha; rewrite (base_val_EV _ XR0) in Ha; [change (xvF aH) with H in Ha | change (xvF aHP) with HP in Ha]; lia.
Qed.
Lemma frame1F a : 0 <= a < 2 ^ 64 -> ~ in_winF a -> mem2 (Z_to_bv 64 a) = mem1 (Z_to_bv 64 a).
Proof.
intros Ha Hw. unfold mem2. apply (HF2 (Z_to_bv 64 a)). intros Hin. apply Hw. apply wrange_winF. rewrite Z_to_bv_unsigned in Hin.
unfold bv_wrap in Hin. change (bv_modulus 64) with (2 ^ 64) in Hin. rewrite Z.mod_small in Hin by lia. exact Hin.
Qed.
Lemma win_coveredF a :
in_winF a -> (SP0 - 96 <= a < SP0) \/ exists c, In c NEW /\ in_range a (cell_range L c).
Proof.
pose proof Hctx as HC.
assert (CM : forall qq off w val, In (MCell (LMem (padd qq off)) w val) NEW -> ptr_addr L qq + off <= a < ptr_addr L qq + off + Z.of_nat w ->
exists c, In c NEW /\ in_range a (cell_range L c)).
{ intros qq off w val Hc Ha. exists (MCell (LMem (padd qq off)) w val). split; [exact Hc|]. unfold in_range, cell_range. cbn [mc_loc mc_w fst snd]. rewrite loc_addr_padd. lia. }
assert (NG : forall dd w val, In (MCell (LMem (padd g dd)) w val) (meta_slot_cells g (Some (MFree (Some hp) (Some h)))) -> In (MCell (LMem (padd g dd)) w val) NEW).
{ intros dd w val Hc. unfold NEW, NEWg. apply in_app_iff. left. exact Hc. }
assert (NO : forall c, In c NEWo -> In c NEW) by (intros c Hc; unfold NEW; apply in_app_iff; right; exact Hc).
unfold NEWo in NO.
intros [W | [W | W]]; [right | left; lia | right].
- destruct (Z_lt_dec a (G + 8)); [apply (CM g 0 8%nat (VP hp)); [apply NG; cbn; tauto | unfold G in *; lia]|].
destruct (Z_lt_dec a (G + 16)); [apply (CM g 8 8%nat (VP h)); [apply NG; cbn; tauto | unfold G in *; lia]|].
destruct (Z_lt_dec a (G + 24)); [apply (CM g 16 8%nat (VZ 0)); [apply NG; cbn; tauto | unfold G in *; lia]|].
destruct (Z_lt_dec a (G + 28)); [apply (CM g 24 4%nat (VZ 0)); [apply NG; cbn; tauto | unfold G in *; lia]|].
destruct (Z_lt_dec a (G + 32)); [apply (CM g 28 4%nat (VZ 0)); [apply NG; cbn; tauto | unfold G in *; lia]|].
apply (CM g 32 8%nat (VZ 0)); [apply NG; cbn; tauto | unfold G in *; lia].
- destruct fc.
+ exists (fmh_cell (Some g)). split; [apply NO; left; reflexivity|]. unfold fmh_cell, in_range, cell_range. cbn [mc_loc mc_w fst snd loc_addr]. rewrite HC. unfold CTX_free_meta_head. lia.
+ destruct (Z_lt_dec a (H + 8)); [apply (CM h 0 8%nat (VP g)); [apply NO; cbn; tauto | unfold H in *; lia] | apply (CM h 8 8%nat (VP g)); [apply NO; cbn; tauto | unfold H in *; lia]].
+ destruct W as [W|W]; [apply (CM h 0 8%nat (VP g)); [apply NO; cbn; tauto | unfold H in *; lia] | apply (CM hp 8 8%nat (VP g)); [apply NO; cbn; tauto | unfold HP in *; lia]].
Qed.
Lemma win_ownedF a : in_winF a -> (SP0 - 96 <= a < SP0) \/ alloc_owned L s4 a.
Proof.
pose proof HL4 as HL0. pose proof Mg4 as Mg0. pose proof Mh as [xh Mh0]. pose proof Mhp as [xp Mp0]. pose proof Hctx as HC. pose proof HI4 as HI.
assert (OG : G <= a < G + 40 -> alloc_owned L s4 a) by (intros W; apply (meta_bytes_owned (g :: X) None U s4 L HI HL0 g _ _ Mg0); unfold META_SIZE; unfold G in W; lia).
assert (OH : H <= a < H + 40 -> alloc_owned L s4 a) by (intros W; apply (meta_bytes_owned (g :: X) None U s4 L HI HL0 h _ _ Mh0); unfold META_SIZE; unfold H in W; lia).
assert (OP : HP <= a < HP + 40 -> alloc_owned L s4 a) by (intros W; apply (meta_bytes_owned (g :: X) None U s4 L HI HL0 hp _ _ Mp0); unfold META_SIZE; unfold HP in W; lia).
assert (OC : CTX + 16 <= a < CTX + 24 -> alloc_owned L s4 a) by (intros W; apply (ctx_bytes_owned (g :: X) None U s4 L HI HL0); rewrite HC; unfold CTX_SIZE; lia).
intros [W | [W | W]]; [right; exact (OG W) | left; lia | right].
destruct fc; [exact (OC W) | apply OH; lia | destruct W as [W|W]; [apply OH; lia | apply OP; lia]].
Qed.
Lemma s5_same : footprint s5 = footprint s4 /\ st_regions s5 = st_regions s4.
Proof. pose proof s5_facts as (_ & E1 & E2 & _). exact (conj E1 E2). Qed.
Theorem memrep5 : memrepX B1 X L s5 mem2.
Proof.
pose proof sp_factsF as (S16 & Sceil & S63 & _). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof s5_same as [Efp Erg].
pose proof SO as SO0. pose proof Hctx as HC. pose proof LG4 as LG0.
refine (memrepX_after B1 (g :: X) X None None U U s4 s5 L mem1 mem2 NEW [] (SP0 - 96, 96) HI4 HI5 HL4 Efp Erg MR4 cellsF new_homeF new_memF new_presentF _ _ _ _).
- intros dd c [].
- intros dd a [].
- intros e0 He. cbn [fst]. pose proof (footprint_hi (g :: X) None U L s4 md HI4 SO0 HC LG0 e0 He). lia.
- intros a Ha Hno _ Hns.
assert (NW : ~ in_winF a).
{ intros W. destruct (win_coveredF a W) as [S | (c & Hc & Hin)]; [apply Hns; unfold in_range; cbn [fst snd]; lia | exact (Hno c Hc Hin)]. }
pose proof (frame1F a Ha NW) as E. split; [exact (proj1 (same_byte_views mem1 mem2 a E))|].
intros [b Hb]. exists b. rewrite E. exact Hb.
Qed.
Lemma outside_winF x : 0x10000 <= x < 0x51000 -> ~ (CTX + 16 <= x < CTX + 24) -> ~ in_winF x.
Proof.
pose proof g_factsF as (G1 & G2 & G8 & Gimg). pose proof h_factsF as (H1 & H2 & H8 & Himg). pose proof hp_factsF as (P1 & P2 & P8 & Pimg).
pose proof (proj1 alloc_ceiling_val) as HCV. pose proof sp_factsF as (S16 & Sceil & S63 & _).
pose proof (off_img G Gimg) as GI. pose proof (off_img H Himg) as HI. pose proof (off_img HP Pimg) as PI.
intros Hx Hc [W|[W|W]]; [lia | lia |]. destruct fc; lia.
Qed.
Lemma statics5 : statics_ok B1 mem2.
Proof.
pose proof ST4 as ST0.
apply (statics_ok_ext B1 mem1 mem2 ST0). intros x Hs.
assert (R : 0x10000 <= x < 0x51000 /\ ~ (CTX + 16 <= x < CTX + 24)).
{ unfold static_owned in Hs. cbn [ms_lock ms_libc ms_got_guard ms_guard ms_debruijn ms_size_classes ms_small_cnt ms_med_cnt B1 src0_msyms] in Hs.
unfold src0_D_malloc_lock, src0_D_libc, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_debruijn32, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab in Hs.
unfold CTX, src0_D_malloc_context. lia. }
destruct R as [R1 R2]. exact (proj1 (same_byte_views mem1 mem2 x (frame1F x ltac:(lia) (outside_winF x R1 R2)))).
Qed.
Theorem A4_post :
nt_post B1 X (S fuel) L A regs mem md (mi, s5) (mkCfg (mkst regs2 (getr regs (nat_to_reg 1)) mem2 (seg_rom src0segs)) md).
Proof.
factsF. pose proof sp_factsF as (S16 & Sceil & S63 & WSTK). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof (nf_unch _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF) as UNCH. pose proof AO4 as AO.
destruct post_regsF as (R10 & R11 & RP). destruct final_regionsF as (_ & Rs & _).
exists regs2, mem2. split; [reflexivity|]. split; [apply memrep5|]. split; [apply statics5|]. split; [exact RP|].
split; [exact R10|]. split; [exact R11|]. unfold NT_FRAME in *. fold SP0. fold SP0 in UNCH. split.
- intros a Ha NO NS.
assert (NW : ~ in_winF a) by (intros W; destruct (win_ownedF a W) as [W'|W']; [apply NS; lia | exact (NO (AO a W'))]).
destruct (UNCH a Ha NO NS) as [U1 U2]. destruct (same_byte_views mem1 mem2 a (frame1F a Ha NW)) as [F1 F2].
split; [exact (eq_trans F1 U1) | exact (iff_trans U2 F2)].
- intros a Ha. destruct (Z_le_dec (SP0 - 88) a) as [L1|L1]; [destruct (Z_lt_dec a (SP0 - 48)) as [L2|L2]|].
+ destruct Rs as (_ & _ & W & _). cbn [r_base r_wlo r_whi] in W. rewrite (base_val_EV _ XR0), ESP0 in W.
replace a with (SP0 - 96 + (a - (SP0 - 96))) by lia. apply W. lia.
+ assert (NW : ~ in_winF a).
{ pose proof g_factsF as (G1 & G2 & _). pose proof h_factsF as (H1 & H2 & _). pose proof hp_factsF as (P1 & P2 & _). pose proof SO as SO0. pose proof (so_ctx_hi _ SO0) as CH.
cbn [ms_ctx B1 src0_msyms] in CH. unfold CTX_SIZE in CH. intros [W|[W|W]]; [lia | lia |]. unfold CTX in W. destruct fc; lia. }
apply (writable_same mem1 mem2 a (frame1F a ltac:(lia) NW)). apply WSTK. lia.
+ assert (NW : ~ in_winF a).
{ pose proof g_factsF as (G1 & G2 & _). pose proof h_factsF as (H1 & H2 & _). pose proof hp_factsF as (P1 & P2 & _). pose proof SO as SO0. pose proof (so_ctx_hi _ SO0) as CH.
cbn [ms_ctx B1 src0_msyms] in CH. unfold CTX_SIZE in CH. intros [W|[W|W]]; [lia | lia |]. unfold CTX in W. destruct fc; lia. }
apply (writable_same mem1 mem2 a (frame1F a ltac:(lia) NW)). apply WSTK. lia.
Qed.
End j.
Theorem A4_SR :
SR src0segs (mkCfg (mkst regs1 (Z_to_bv 64 pcF) mem1 (seg_rom src0segs)) md)
(nt_post B1 X (S fuel) L A regs mem md (mi, s5)).
Proof.
pose proof (nf_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF) as (Hh & Hlz & Hmat). pose proof (nf_ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ NF) as Hret.
eapply SR_bind; [eapply (stage_run NT_RET (ss_F e v) (SSF e v) (EV xvF) _ md (F_run_ok e v) A4_entry_st_ok Hh Hlz)|].
intros c' (ms2 & -> & HS2 & HF2). cbn [ms_mem mkst] in HF2.
destruct (post_shapeF ms2 HS2) as [Ems Hra].
eapply (SR_nt_ret' (EV xvF) (SSF e v) ms2 md aE1 _ HS2).
- exact (proj1 (proj2 (SSF_shape e v))).
- exact (proj1 (SSF_shape e v)).
- exact Hra.
- cbn [EV ew]. unfold xvF, aE1. cbn [Nat.ltb Nat.leb]. rewrite Z_to_bv_bv_unsigned. exact Hret.
- exact Hh.
- exact Hlz.
- cbn [EV ew]. unfold xvF at 1. unfold aE1. cbn [Nat.ltb Nat.leb]. rewrite Z_to_bv_bv_unsigned.
exact (A4_post ms2 HS2 HF2).
Qed.
End i.
End f.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
