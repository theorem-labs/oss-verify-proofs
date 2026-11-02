(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0l.v, with its module paths changed. *)
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0r.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition toMq (q : apath) : apathM :=
match q with Q1 => MQ1 | Q2 => MQ2 | Q3 => MQ3 | Q4V1 => MQ4V1 | Q4V2 => MQ4V2 | Q5V1 => MQ5V1 | Q5V2 => MQ5V2
| Q6V1 => MQ6V1 | Q6V2 => MQ6V2 | Q7V1 => MQ7V1 | Q7V2 => MQ7V2 end.
Definition toMd (d : dvar) : dvarM :=
match d with D0 => MD0 | D1 => MD1 | D2a => MD2a | D2b => MD2b | D2a' => MD2a' | D2b' => MD2b' end.
Lemma validA_M q d : validA q d = validAM (toMq q) (toMd d).
Proof. destruct q, d; reflexivity. Qed.
Section t.
Variables (X : list sptr) (U : Z -> Z) (fuel : nat) (L : layout) (A : astate) (g : sptr) (i : Z) (am : ameta).
Variables (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (gv : Z).
Variables (q : apath) (d : dvar) (p n : sptr) (ap an : ameta).
Hypothesis HI : Inv X (Some (g, i)) U A.
Hypothesis Hu : usedX X A g am.
Hypothesis HB : bounded A.
Hypothesis NPRE : nt_pre B1 X (S fuel) L A regs mem md g i.
Hypothesis Hgv : word_mem src0segs mem GUARD gv.
Hypothesis HC1 : nt_C1 A g i am = true.
Hypothesis VALID : validA q d = true.
Hypothesis QF : qfacts A g i am (toMq q).
Hypothesis DF : dfacts X A g am (toMd d) p n ap an.
Let G := ptr_addr L g.
Let SP0 := spZ regs.
Lemma Mg : MT A g = Some (MUsed am). Proof. exact (proj1 (usedX_MT _ _ _ _ Hu)). Qed.
Lemma HL : layout_ok L A. Proof. exact (proj1 (proj2 NPRE)). Qed.
Lemma SO : syms_ok B1. Proof. exact (proj1 NPRE). Qed.
Lemma Hctx : ly_ctx L = CTX. Proof. exact (proj1 (proj2 (proj2 NPRE))). Qed.
Lemma MR : memrepX B1 X L A mem. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 NPRE))))). Qed.
Lemma ST : statics_ok B1 mem. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 NPRE)))))). Qed.
Lemma LG : ledger_ok B1 L A md. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 NPRE))))))). Qed.
Definition meta_factsA := meta_facts X (Some (g, i)) U L A md HI LG.
Definition CELLA := CELL X L A mem MR.
Definition meta_cellA := meta_cell X (Some (g, i)) U L A mem HI MR.
Definition meta_presentA := meta_present X (Some (g, i)) U L A mem md HI MR LG.
Definition ctx_active_cellA := ctx_active_cell X L A mem Hctx MR.
Definition ctx_usage_cellA := ctx_usage_cell X L A mem Hctx MR.
Definition ctx_bounces_cellA := ctx_bounces_cell X L A mem Hctx MR.
Definition tq_bytesA := tq_bytes mem SO ST.
Definition footprint_hiA := footprint_hi X (Some (g, i)) U L A md HI SO Hctx LG.
Definition old_meta_cellA := old_meta_cell X (Some (g, i)) U A HI.
Definition hdv : Z := optrZ L (active_hd A (am_sc am)).
Definition NM : Z := ptr_addr L (am_mem an).
Definition aidxb : Z := match mbyte src0segs mem (NM + 8) with Some b => bv_unsigned b | None => 0 end.
Definition P : Z := ptr_addr L p.
Definition N : Z := ptr_addr L n.
Definition xvA (k : nat) : Z :=
if (k <? 32)%nat then bv_unsigned (getr regs (nat_to_reg k))
else match k with
| 41%nat => optrZ L (am_prev am) mod 2 ^ 64
| 42%nat => optrZ L (am_next am) mod 2 ^ 64
| 43%nat => ptr_addr L (am_mem am) mod 2 ^ 64
| 44%nat => am_avail am
| 45%nat => am_freed am
| 46%nat => meta_bits am
| 47%nat => gv mod 2 ^ 64
| 48%nat => am_sc am
| 49%nat => CTX + 80 + 8 * am_sc am
| 52%nat => if am_sc am <? 48 then TBL + 2 * am_sc am else TBL
| 53%nat => scl_of (am_sc am)
| 54%nat => usage_of A (am_sc am) mod 2 ^ 64
| 55%nat => znth (am_sc am - 7) (st_bounces A) mod 256
| 56%nat => am_last am
| 57%nat => (am_maplen am * 4096) mod 2 ^ 64
| 58%nat => P
| 59%nat => N
| 60%nat => NM
| 61%nat => aidxb
| 62%nat => am_freed an
| 63%nat => hdv mod 2 ^ 64
| _ => 0
end.
Lemma g_facts :
0 <= i <= am_last am /\ 0 <= am_last am <= 31 /\
0 <= am_avail am < 2 ^ 32 /\ 0 <= am_freed am < 2 ^ 32 /\
0 <= meta_bits am < 2 ^ 64 /\ Z.land (meta_bits am) 32 = 32 /\
4096 <= G /\ G + 40 <= alloc_ceiling /\ G mod 8 = 0 /\ (forall x, G <= x < G + 40 -> ~ in_img B1 x) /\
(exists a, In a (st_areas A) /\ In (LMem a, PGSZ) (footprint A) /\ loc_addr L (LMem a) <= G /\ G + 40 <= loc_addr L (LMem a) + PGSZ) /\
0 <= am_maplen am < 2 ^ 40 /\ 0 <= am_sc am < 64.
Proof.
destruct (inv_reserved HI g i eq_refl) as (am' & Hu' & Hi & _). pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
pose proof (inv_groups HI g am Hu) as GG.
pose proof GG as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
assert (Hav32 : am_avail am < 2 ^ 32) by (apply (mask_u32 _ (am_last am)); [lia|lia|intros j Hj; apply (proj1 (Gabove j Hj))]).
assert (Hfr32 : am_freed am < 2 ^ 32) by (apply (mask_u32 _ (am_last am)); [lia|lia|intros j Hj; apply (proj2 (Gabove j Hj))]).
assert (Hsc : 0 <= am_sc am < 64) by (destruct Gcl as [(C & _)|(C & _)]; lia).
destruct (used_group_region X (Some (g, i)) U A g am HI Hu) as (rg & Hr & Hk & Hl & Ho & Hext & Hml0).
destruct (lg_placed _ _ _ _ LG _ _ Hr Hl) as (_ & R4096 & Rceil & _). pose proof (proj1 alloc_ceiling_val) as HCV.
assert (Hml : 0 <= am_maplen am < 2 ^ 40).
{ split; [exact Gml|]. destruct (Z_lt_dec 0 (am_maplen am)); [|lia].
destruct (Gmp ltac:(lia)) as (r2 & rg2 & Em & Hr2 & _ & _ & Hlen2 & _). rewrite Em in Hr. cbn [prid] in Hr.
rewrite Hr in Hr2. injection Hr2 as <-. rewrite Em in *. cbn [poff] in *. unfold PGSZ in *. unfold group_extent, UNIT, IB in Hext. lia. }
destruct (meta_factsA g am Hu) as (G1 & G2 & G8 & Gimg & Garea).
unfold G. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
- unfold meta_bits. pose proof (bits_nonneg (am_last am) (am_sc am) (am_maplen am)). unfold bits_enc in *. lia.
- unfold meta_bits. pose proof (bits_lt64 (am_last am) (am_sc am) (am_maplen am)). unfold bits_enc in *. lia.
- assert (E5 : meta_bits am / 32 = 1 + 2 * (am_sc am + 64 * am_maplen am)).
{ unfold meta_bits. replace (am_last am + 32 + 64 * am_sc am + 4096 * am_maplen am) with ((1 + 2 * (am_sc am + 64 * am_maplen am)) * 32 + am_last am) by lia.
rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec. change 32 with (2 ^ 5).
destruct (Z.eq_dec j 5) as [->|Hne].
+ rewrite Z.pow2_bits_true by lia. rewrite andb_true_r. apply Z.testbit_true; [lia|]. change (2 ^ 5) with 32. rewrite E5.
replace (1 + 2 * (am_sc am + 64 * am_maplen am)) with (1 + (am_sc am + 64 * am_maplen am) * 2) by lia. rewrite Z.mod_add by lia. reflexivity.
+ rewrite Z.pow2_bits_eqb by lia. replace (5 =? j) with false by (symmetry; apply Z.eqb_neq; lia). apply andb_false_r.
Qed.
Lemma sc_q : match q with Q1 => am_sc am = 63 | _ => 0 <= am_sc am < 48 end.
Proof. destruct q; cbn [toMq qfacts] in QF; destruct QF as [_ QF']; tauto. Qed.
Lemma Un : usedX X A n an.
Proof. destruct d; cbn [toMd dfacts] in DF; [destruct DF as (_ & _ & _ & -> & _ & ->); exact Hu | destruct DF as (_ & _ & _ & _ & _ & -> & _ & ->); exact Hu | | | |]; tauto. Qed.
Lemma Up : usedX X A p ap.
Proof.
pose proof Un as Un0. destruct d; cbn [toMd dfacts] in DF;
[destruct DF as (_ & _ & -> & _ & -> & _); exact Hu | destruct DF as (_ & _ & _ & _ & -> & _ & -> & _); exact Hu | tauto | tauto | |];
destruct DF as (_ & _ & _ & [-> ->] & _); exact Un0.
Qed.
Lemma n_facts :
4096 <= N /\ N + 40 <= alloc_ceiling /\ N mod 8 = 0 /\ (forall x, N <= x < N + 40 -> ~ in_img B1 x) /\
4096 <= NM /\ NM + 16 <= alloc_ceiling /\ NM mod 16 = 0 /\ (forall x, NM <= x < NM + 16 -> ~ in_img B1 x) /\
(exists rg, region_of A (prid (am_mem an)) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
In (LMem (SP (prid (am_mem an)) 0), rg_len rg) (footprint A) /\ ly_reg L (prid (am_mem an)) <= NM /\ NM + 16 <= ly_reg L (prid (am_mem an)) + rg_len rg) /\
0 <= am_freed an < 2 ^ 32 /\ 0 <= am_aidx an <= 31 /\
(exists b, mbyte src0segs mem (NM + 8) = Some b /\ bv_unsigned b mod 32 = am_aidx an) /\ aidxb mod 32 = am_aidx an.
Proof.
pose proof (proj1 alloc_ceiling_val) as HCV. pose proof Un as Un.
destruct (meta_factsA n an Un) as (N1 & N2 & N8 & Nimg & _).
pose proof (inv_groups HI n an Un) as ((Nlast & Naidx & Nlen & Nav & Nfrn & Ndisj & Nabove & _) & Nml & _).
assert (Nfr32 : am_freed an < 2 ^ 32) by (apply (mask_u32 _ (am_last an)); [lia|lia|intros j Hj; apply (proj2 (Nabove j Hj))]).
destruct (used_group_region X (Some (g, i)) U A n an HI Un) as (rg & Hr & Hk & Hl & Ho & Hext & _).
destruct (lg_placed _ _ _ _ LG _ _ Hr Hl) as (Ral & R4096 & Rceil & Rimg).
pose proof (used_group_aligned X (Some (g, i)) U A HI _ n an Un (Nat.le_refl _)) as AL16.
assert (ENM : NM = ly_reg L (prid (am_mem an)) + poff (am_mem an)) by (unfold NM, ptr_addr, loc_addr; destruct (am_mem an); reflexivity).
unfold group_extent, UNIT, IB in Hext. pose proof (stride_pos _ _ _ _ _ (inv_groups HI n an Un)) as SPn.
assert (B8 : exists b, mbyte src0segs mem (NM + 8) = Some b /\ bv_unsigned b mod 32 = am_aidx an).
{ assert (Hc : In (if am_maplen an =? 0 then MCell (LMem (padd (am_mem an) 8)) 1 (VLo5 (am_aidx an)) else MCell (LMem (padd (am_mem an) 8)) 4 (VZ (am_aidx an))) (imageX X A)).
{ unfold imageX. rewrite !in_app_iff. right; right. apply in_flat_map. exists (n, an). split; [| cbn [fst snd group_cells]; right; left; reflexivity].
unfold used_metasX. apply filter_In. split; [apply (used_metas_iff A n an (proj1 (inv_keys HI))); exact (proj1 (usedX_MT _ _ _ _ Un)) | cbn [fst]; rewrite (proj2 (usedX_MT _ _ _ _ Un)); reflexivity]. }
pose proof (CELLA _ Hc) as C. unfold cell_mem in C. destruct (am_maplen an =? 0); cbn [mc_val mc_loc mc_w sval_num] in C; rewrite loc_addr_padd in C; fold NM in C.
- exact (C ltac:(lia)).
- exists (Z_to_bv 8 (le_byte (am_aidx an) 4 0)). split; [rewrite <- (C 0%nat ltac:(lia)); f_equal; lia|].
replace (le_byte (am_aidx an) 4 0) with (am_aidx an).
2:{ unfold le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 4)) with 4294967296. rewrite Z.shiftr_0_r. rewrite (Z.mod_small (am_aidx an) 4294967296) by lia. rewrite Z.mod_small by lia. reflexivity. }
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite (Z.mod_small (am_aidx an) 256) by lia. rewrite Z.mod_small by lia. reflexivity. }
unfold N. repeat match goal with |- _ /\ _ => split end; auto; try lia.
- rewrite ENM. replace (ly_reg L (prid (am_mem an)) + poff (am_mem an)) with (poff (am_mem an) + (256 * (ly_reg L (prid (am_mem an)) / 4096)) * 16).
+ rewrite Z.mod_add; [exact AL16 | lia].
+ pose proof (Z.div_exact (ly_reg L (prid (am_mem an))) 4096 ltac:(lia)) as [_ E]. unfold PGSZ in Ral. specialize (E Ral). lia.
- intros x Hx. apply Rimg. lia.
- exists rg. repeat match goal with |- _ /\ _ => split end; auto; try lia. apply footprint_region_In; assumption.
- unfold aidxb. destruct B8 as (b & -> & Hb). exact Hb.
Qed.
Lemma n_apart : match d with D2a | D2b | D2a' | D2b' => n <> g /\ (G + 40 <= N \/ N + 40 <= G) | _ => True end.
Proof.
assert (K : n <> g -> n <> g /\ (G + 40 <= N \/ N + 40 <= G)).
{ intros Hng. pose proof (metas_apart X _ U A L g n _ _ HI HL Mg (proj1 (usedX_MT _ _ _ _ Un)) ltac:(intros E; exact (Hng (eq_sym E)))) as AP.
unfold META_SIZE in AP. fold G N in AP. auto. }
destruct d; try exact I; cbn [toMd dfacts] in DF; destruct DF as (_ & _ & Hng & _); exact (K Hng).
Qed.
Lemma p_facts : 4096 <= P /\ P + 40 <= alloc_ceiling /\ P mod 8 = 0 /\ (forall x, P <= x < P + 40 -> ~ in_img B1 x).
Proof. destruct (meta_factsA p ap Up) as (P1 & P2 & P8 & Pimg & _). unfold P. auto. Qed.
Lemma p_apart : match d with D2a | D2b => p <> g /\ p <> n /\ (G + 40 <= P \/ P + 40 <= G) /\ (N + 40 <= P \/ P + 40 <= N) | _ => True end.
Proof.
assert (K : p <> g -> p <> n -> p <> g /\ p <> n /\ (G + 40 <= P \/ P + 40 <= G) /\ (N + 40 <= P \/ P + 40 <= N)).
{ intros Hpg Hpn.
pose proof (metas_apart X _ U A L g p _ _ HI HL Mg (proj1 (usedX_MT _ _ _ _ Up)) ltac:(intros E; exact (Hpg (eq_sym E)))) as AP1.
pose proof (metas_apart X _ U A L n p _ _ HI HL (proj1 (usedX_MT _ _ _ _ Un)) (proj1 (usedX_MT _ _ _ _ Up)) ltac:(intros E; exact (Hpn (eq_sym E)))) as AP2.
unfold META_SIZE in *. fold G N P in AP1. fold N P in AP2. auto. }
destruct d; try exact I; cbn [toMd dfacts] in DF; destruct DF as (_ & _ & _ & Hpg & Hpn & _); exact (K Hpg Hpn).
Qed.
Lemma hd_factsA : match d with D2a | D2a' => 0 <= hdv < 2 ^ 64 /\ hdv <> G | _ => True end.
Proof.
pose proof (proj1 alloc_ceiling_val) as HCV. pose proof g_facts as (_&_&_&_&_&_&G1&G2&_).
assert (K : hd_ok X A g am -> 0 <= hdv < 2 ^ 64 /\ hdv <> G).
{ intros HD. unfold hdv. destruct (active_hd A (am_sc am)) as [h|] eqn:Eh; cbn [optrZ]; [| unfold G; lia].
destruct (HD h Eh) as [Hhg (ah & Uh)].
destruct (meta_factsA h ah Uh) as (H1 & H2 & _).
pose proof (metas_apart X _ U A L g h _ _ HI HL Mg (proj1 (usedX_MT _ _ _ _ Uh)) ltac:(intros E; exact (Hhg (eq_sym E)))) as AP.
unfold META_SIZE in AP. unfold G. lia. }
destruct d; try exact I; cbn [toMd dfacts] in DF.
- destruct DF as (_ & _ & _ & _ & _ & _ & _ & _ & HD). exact (K HD).
- destruct DF as (_ & _ & _ & _ & _ & _ & HD). exact (K HD).
Qed.
Lemma XR : forall k, 0 <= xvA k < 2 ^ 64.
Proof.
intros k. pose proof g_facts as (_ & Hlast & Hav & Hfr & Hbits & _ & G1 & G2 & _ & _ & _ & Hml & Hsc). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof n_facts as (N1&N2&_&_&M1&M2&_&_&_&Nfr&Nai&(b & Eb & _)&_). pose proof p_facts as (P1&P2&_).
unfold xvA. destruct (k <? 32)%nat; [apply u64_range|].
assert (M64 : forall z, 0 <= z mod 2 ^ 64 < 2 ^ 64) by (intros z; apply Z.mod_pos_bound; lia).
assert (M256 : forall z, 0 <= z mod 256 < 2 ^ 64) by (intros z; pose proof (Z.mod_pos_bound z 256 ltac:(lia)); lia).
assert (HSCL : 0 <= scl_of (am_sc am) < 2 ^ 64) by (unfold scl_of; destruct (am_sc am <? 48) eqn:E; [apply Z.ltb_lt in E; pose proof (scl_range (am_sc am) ltac:(lia)); lia | lia]).
assert (HTQ : 0 <= (if am_sc am <? 48 then TBL + 2 * am_sc am else TBL) < 2 ^ 64) by (unfold TBL, src0_D_size_classes; destruct (am_sc am <? 48); lia).
assert (HAI : 0 <= aidxb < 2 ^ 64) by (unfold aidxb; rewrite Eb; pose proof (u8_range b); lia).
unfold CTX, src0_D_malloc_context.
do 64 (destruct k as [|k]; [first [apply M64 | apply M256 | assumption | lia] |]). lia.
Qed.
Lemma sp_facts :
SP0 mod 16 = 0 /\ alloc_ceiling + 96 + 96 * Z.of_nat fuel <= SP0 /\ SP0 < 2 ^ 63 /\
(forall x, SP0 - 96 * Z.of_nat (S fuel) <= x < SP0 -> writable_at src0segs mem x).
Proof.
pose proof NPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & Hceil & Hsp63 & Hstk & _).
unfold NT_FRAME in *. unfold SP0. split; [exact Hal|]. split; [lia|]. split; [exact Hsp63|]. intros x Hx. apply Hstk. lia.
Qed.
Lemma EG : xvA 10 = G.
Proof.
pose proof NPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ha0 & _). pose proof g_facts as (_&_&_&_&_&_&G1&G2&_). pose proof (proj1 alloc_ceiling_val).
unfold xvA. cbn [Nat.ltb Nat.leb nat_to_reg]. rewrite Ha0. apply lit64_small. unfold G in *. lia.
Qed.
Lemma EI : xvA 11 = i.
Proof.
pose proof NPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ha1 & _). pose proof g_facts as (Hi & Hl & _).
unfold xvA. cbn [Nat.ltb Nat.leb nat_to_reg]. rewrite Ha1. apply lit64_small. lia.
Qed.
Lemma ESP : xvA 2 = SP0. Proof. reflexivity. Qed.
Lemma regsA_ok : regs_ok (EV xvA) regs_init regs.
Proof.
apply regs_ok_init. intros k Hk. unfold xvA. replace (k <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia). apply Z_to_bv_bv_unsigned.
Qed.
Ltac facts0 := pose proof XR as XR0; pose proof EG as EG0; pose proof EI as EI0.
Ltac denA0 xr eg ei := cbn [sv_denot]; rewrite ?alu64_and, ?alu64_or, ?alu64_srl, ?alu64_sll, ?alu64_add, ?alu64_sub;
rewrite ?(ew_EV xvA xr);
unfold aSP, aNG, aNI, aPREV, aNEXT, aGMEM, aGAV, aGFR, aGBITS, aGV, aSC, aACT, aTQ2, aSCL, aUSG, aBNC, aLAST, aMP, aP, aN, aNMEM, aNAIDX, aNFR, aHD;
rewrite ?eg, ?ei; unfold xvA; cbn [Nat.ltb Nat.leb nat_to_reg]; rewrite ?Z.add_0_r.
Ltac denA :=
let xr := match goal with H : forall k : nat, 0 <= xvA k < 2 ^ 64 |- _ => H end in
let eg := match goal with H : xvA 10 = _ |- _ => H end in
let ei := match goal with H : xvA 11 = _ |- _ => H end in
denA0 xr eg ei.
Ltac weq := apply (proj2 (word_eq _ _)).
Lemma atomsA_ok : atoms_ok (EV xvA) (a1_atoms q d).
Proof.
facts0. pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _ & Hml & Hsc).
pose proof sp_facts as (S16 & Sceil & S63 & _). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof sc_q as SQ.
pose proof n_facts as NF. pose proof p_facts as PF.
assert (M64 : forall z, 0 <= z mod 2 ^ 64 <= 2 ^ 64 - 1) by (intros z; pose proof (Z.mod_pos_bound z (2 ^ 64) ltac:(lia)); lia).
unfold a1_atoms. apply atoms_ok_app; [|apply atoms_ok_app].
- cbn [nt_atoms0 atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite !(ew_EV xvA XR0).
unfold aSP, aNG, aNI, aPREV, aNEXT, aGMEM, aGAV, aGFR, aGBITS, aGV, aSC, aLAST, aUSG, aBNC. rewrite EG0, EI0, ESP.
unfold xvA. cbn [Nat.ltb Nat.leb]. unfold CEIL.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite ?Z.mod_1_r.
pose proof (M64 (optrZ L (am_prev am))). pose proof (M64 (optrZ L (am_next am))). pose proof (M64 (ptr_addr L (am_mem am))). pose proof (M64 gv).
pose proof (M64 (usage_of A (am_sc am))). pose proof (Z.mod_pos_bound (znth (am_sc am - 7) (st_bounces A)) 256 ltac:(lia)).
unfold G, SP0 in *. repeat split; lia.
- destruct q; cbn [q_atoms atoms_ok]; [exact I| | | | | | | | | |]; cbn [toMq] in SQ;
unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite !(ew_EV xvA XR0); unfold aACT, aTQ2, aSCL, aMP; unfold xvA; cbn [Nat.ltb Nat.leb];
unfold TBL, src0_D_size_classes, CTX, src0_D_malloc_context; change (2 ^ 3) with 8; change (2 ^ 1) with 2; change (2 ^ 0) with 1; change (2 ^ 12) with 4096; rewrite ?Z.mod_1_r;
(replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia));
(assert (HSCL : 1 <= scl_of (am_sc am) <= 8191) by (unfold scl_of; replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia); apply scl_range; lia));
(rewrite (Z.mod_small (am_maplen am * 4096) (2 ^ 64)) by lia);
(repeat split; try lia; first
[ apply ctx_al8 | apply tbl_al2 | apply Z_mod_mult ]).
- cbn [d_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite !(ew_EV xvA XR0). unfold aP, aN, aNMEM, aNAIDX, aNFR, aHD. unfold xvA. cbn [Nat.ltb Nat.leb].
change (2 ^ 3) with 8. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite ?Z.mod_1_r. pose proof (M64 hdv).
destruct NF as (N1&N2&N8&_&M1&M2&M16&_&_&Nfr&Nai&(b & Eb & _)&_). destruct PF as (P1&P2&P8&_).
unfold aidxb. rewrite Eb. pose proof (u8_range b).
repeat split; try lia.
Qed.
Lemma Ebits : meta_bits am = bits_enc (am_last am) (am_sc am) (am_maplen am).
Proof. reflexivity. Qed.
Lemma U_NSELF : bv_unsigned (sv_denot (EV xvA) NSELF) = sx32 (2 ^ i).
Proof.
facts0. pose proof g_facts as (Hi & Hlast & _).
unfold NSELF. change (sv_denot (EV xvA) (SAluw ALU_SLL (SLit 1) (SOff aNI 0))) with (sext 64 (alu32 ALU_SLL (low32 (sv_denot (EV xvA) (SLit 1))) (low32 (sv_denot (EV xvA) (SOff aNI 0))))).
rewrite sllw_rr_unsigned, (den_off0 _ XR0), U_lit, (lit64_small (xvA aNI)) by apply XR0. change (1 mod 2 ^ 64) with 1.
unfold aNI. rewrite EI0. rewrite sllw_1 by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma U_NMASK : bv_unsigned (sv_denot (EV xvA) NMASK) = sx32 (nt_mask am).
Proof.
facts0. unfold NMASK. change (sv_denot (EV xvA) (SAlu ALU_OR (SExt true 32 (SOff aGAV 0)) (SExt true 32 (SOff aGFR 0)))) with
(alu64 ALU_OR (sv_denot (EV xvA) (SExt true 32 (SOff aGAV 0))) (sv_denot (EV xvA) (SExt true 32 (SOff aGFR 0)))).
rewrite alu64_or, !U_sext32, !(U_off0 _ XR0). unfold aGAV, aGFR, xvA. cbn [Nat.ltb Nat.leb]. unfold nt_mask. rewrite Z.lor_comm. apply lor_sx32.
Qed.
Lemma U_NMS : bv_unsigned (sv_denot (EV xvA) NMS) = sx32 (nt_mask am + 2 ^ i).
Proof.
unfold NMS. change (sv_denot (EV xvA) (SAluw ALU_ADD NMASK NSELF)) with (sext 64 (alu32 ALU_ADD (low32 (sv_denot (EV xvA) NMASK)) (low32 (sv_denot (EV xvA) NSELF)))).
rewrite addw_rr_unsigned, U_NMASK, U_NSELF. apply addw_masks.
Qed.
Lemma U_NALL : bv_unsigned (sv_denot (EV xvA) NALL) = sx32 (ones (am_last am)).
Proof.
facts0. pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & _).
unfold NALL. change (sv_denot (EV xvA) (SAluw ALU_ADD (SAluw ALU_SLL (SLit 2) (SOff aGBITS 0)) (SLit (-1)))) with
(sext 64 (alu32 ALU_ADD (low32 (sext 64 (alu32 ALU_SLL (low32 (sv_denot (EV xvA) (SLit 2))) (low32 (sv_denot (EV xvA) (SOff aGBITS 0)))))) (low32 (sv_denot (EV xvA) (SLit (-1)))))).
rewrite addw_rr_unsigned, sllw_rr_unsigned, (U_off0 _ XR0). cbn [sv_denot]. rewrite (lit64_unsigned (-1)), !lit64_small by lia.
unfold aGBITS, xvA. cbn [Nat.ltb Nat.leb]. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
rewrite (proj2 (addiw_sllw2_m1 (meta_bits am) ltac:(lia))). f_equal. f_equal.
unfold meta_bits. replace (am_last am + 32 + 64 * am_sc am + 4096 * am_maplen am) with (am_last am + (1 + 2 * am_sc am + 128 * am_maplen am) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma U_NINE : bv_unsigned (sv_denot (EV xvA) NINE) = 9 * (am_last am + 1).
Proof.
facts0. pose proof g_facts as (Hi & Hlast & _).
unfold NINE. change (sv_denot (EV xvA) (SAlu ALU_ADD (SMd M_MUL (SOff aLAST 0) (SLit 9)) (SLit 9))) with
(alu64 ALU_ADD (mul_div M_MUL (sv_denot (EV xvA) (SOff aLAST 0)) (sv_denot (EV xvA) (SLit 9))) (sv_denot (EV xvA) (SLit 9))).
rewrite alu64_add, mul64_unsigned, (U_off0 _ XR0), U_lit. unfold aLAST, xvA. cbn [Nat.ltb Nat.leb]. change (9 mod 2 ^ 64) with 9.
unfold mul64, add64. rewrite (Z.mod_small (am_last am * 9)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma mask_self_range : 0 <= nt_mask am + 2 ^ i < 2 ^ 32 /\ 0 <= ones (am_last am) < 2 ^ 32 /\ 0 <= nt_mask am < 2 ^ 32 /\ 0 < 2 ^ i < 2 ^ 32.
Proof.
pose proof g_facts as (Hi & Hlast & Hav & Hfr & _).
pose proof (mask_facts X U A g i am HI Hu) as (_ & _ & Hm0 & Hbit & _).
assert (Hb : 0 < 2 ^ i < 2 ^ 32) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
assert (Dd : Z.land (nt_mask am) (2 ^ i) = 0).
{ apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec i j) as [<-|]; [rewrite Hbit; reflexivity | apply andb_false_r]. }
pose proof (lor_range (am_freed am) (am_avail am) 32 ltac:(lia) ltac:(lia)) as LR. unfold nt_mask in *.
split; [rewrite (Z.add_nocarry_lxor _ _ Dd); apply lxor_range; lia|]. split; [|split; [lia | exact Hb]].
unfold ones. assert (0 < 2 ^ (am_last am + 1) <= 2 ^ 32) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]). lia.
Qed.
Lemma last0_q : match q with Q3 | Q4V1 | Q5V1 | Q6V1 | Q7V1 => am_last am = 0 | _ => True end.
Proof.
pose proof QF as QF0. unfold qfacts, strideV1 in QF0. destruct q; try exact I; cbn [toMq] in QF0.
- destruct QF0 as (_ & _ & _ & HL0 & _). exact HL0.
- destruct QF0 as (_ & _ & (_ & HL0 & _) & _). exact HL0.
- destruct QF0 as (_ & _ & (_ & HL0 & _) & _). exact HL0.
- destruct QF0 as (_ & _ & (_ & HL0 & _) & _). exact HL0.
- destruct QF0 as (_ & _ & (_ & HL0 & _) & _). exact HL0.
Qed.
Lemma aliasA_ok : alias_ok (EV xvA) (a1_alias q).
Proof.
facts0. pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _ & Hml & Hsc). pose proof sc_q as SQ. pose proof last0_q as L0.
pose proof (Z.mod_pos_bound (am_maplen am * 4096) (2 ^ 64) ltac:(lia)) as MPR.
unfold a1_alias. apply alias_ok_app.
- cbn [alias_ok]. split; [|split; [|exact I]].
+ weq. unfold SCX. denA. rewrite !lit64_small by lia.
change (52 mod 64) with 52. change (58 mod 64) with 58. rewrite Ebits. apply bits_sc; lia.
+ weq. change (sv_denot (EV xvA) (SAlu ALU_ADD (SExt true 32 (SOff aNFR 0)) (SLit 0))) with (alu64 ALU_ADD (sv_denot (EV xvA) (SExt true 32 (SOff aNFR 0))) (sv_denot (EV xvA) (SLit 0))).
rewrite alu64_add, U_lit. change (0 mod 2 ^ 64) with 0. pose proof (u64_range (sv_denot (EV xvA) (SExt true 32 (SOff aNFR 0)))). unfold add64. rewrite Z.add_0_r. apply Z.mod_small. lia.
- destruct q; cbn [toMq] in SQ, L0; [exact I| | | | | | | | | |]; cbn [alias_ok];
(split; [|split; [|split; [|split; [|split; [|exact I]]]]]); weq; denA;
unfold TBL, src0_D_size_classes, CTX, src0_D_malloc_context; rewrite ?(lit64_unsigned (-4096)); rewrite ?lit64_small by lia; rewrite ?Ebits;
(replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia)); rewrite ?lit64_small by lia.
all: try (change (3 mod 64) with 3; unfold sll64; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3) with 8; rewrite Z.mod_small by lia; lia).
all: try (change (5 mod 64) with 5; rewrite bits_2sc by lia; lia).
all: try (change (1 mod 64) with 1; unfold sll64; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 1) with 2; rewrite Z.mod_small by lia; lia).
all: try (change ((-4096) mod 2 ^ 64) with (2 ^ 64 - 4096); rewrite bits_maplen_bytes by lia; rewrite Z.mod_small by lia; reflexivity).
all: rewrite bits_land31 by lia; rewrite ?L0; reflexivity.
Qed.
Lemma bounces_range : 7 <= am_sc am <= 38 -> 0 <= znth (am_sc am - 7) (st_bounces A) <= 255.
Proof.
intros Hsc. pose proof (inv_ctx HI) as (_ & _ & _ & Lb & _ & _ & Bb & _). apply Bb. unfold znth. apply nth_In. rewrite Lb. lia.
Qed.
Lemma usage_range : 0 <= usage_of A (am_sc am) < 2 ^ 48.
Proof. exact (proj1 HB (am_sc am)). Qed.
Ltac cprep := unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite ?branch_geu, ?branch_ltu, ?branch_eq, ?branch_ne.
Lemma cond_C32_okA : acond_ok (EV xvA) cond_C32.
Proof.
facts0. pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & _). unfold cond_C32. cprep. denA. rewrite !lit64_small by lia.
change (32 mod 2 ^ 64) with 32. rewrite Hb32. reflexivity.
Qed.
Lemma U_sc7 : bv_unsigned (sv_denot (EV xvA) (SOff aSC (-7))) = if am_sc am <? 7 then am_sc am - 7 + 2 ^ 64 else am_sc am - 7.
Proof.
facts0. pose proof g_facts as (_&_&_&_&_&_&_&_&_&_&_&_&Hsc). cbn [sv_denot]. rewrite (ew_EV xvA XR0). unfold aSC, xvA. cbn [Nat.ltb Nat.leb].
rewrite Z_to_bv_unsigned. destruct (Z.ltb_spec (am_sc am) 7).
- rewrite <- (bv_wrap_add_modulus_1 64 (am_sc am + -7)). change (bv_modulus 64) with (2 ^ 64). rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2 ^ 64). lia.
- rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma qconds_ok : conds_ok (EV xvA) (q_conds q d).
Proof.
facts0. pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _ & Hml & Hsc). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof mask_self_range as (R1 & R2 & R3 & R4). pose proof usage_range as UR. pose proof n_apart as NA. pose proof n_facts as (N1 & N2 & _).
pose proof QF as QF0. unfold qfacts, okA, strideV1, strideV2, bouncing in QF0. unfold bit in QF0. destruct QF0 as [Eall QF1].
assert (Escl : am_sc am < 48 -> class_size (am_sc am) = 16 * scl_of (am_sc am)).
{ intros H48. unfold class_size, scl_of, UNIT. replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
assert (HSCL : am_sc am < 48 -> 1 <= scl_of (am_sc am) <= 8191) by (intros H48; unfold scl_of; replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia); apply scl_range; lia).
assert (C_all : acond_ok (EV xvA) (mkAC BC_EQ NMS NALL)) by (cprep; rewrite U_NMS, U_NALL, Eall; apply Z.eqb_refl).
assert (C_le47 : am_sc am < 48 -> acond_ok (EV xvA) (mkAC BC_GEU (SLit 47) (SOff aSC 0))).
{ intros H48. cprep. denA. rewrite !lit64_small by lia. destruct (Z.ltb_spec 47 (am_sc am)); [lia | reflexivity]. }
assert (C_ml0 : am_maplen am = 0 -> acond_ok (EV xvA) (mkAC BC_EQ (SAlu ALU_SRL (SOff aGBITS 0) (SLit 12)) (SLit 0))).
{ intros Hml0. cprep. denA. rewrite !lit64_small by lia. change (12 mod 64) with 12. rewrite Ebits, bits_shiftr12, Hml0 by lia. reflexivity. }
assert (C_ml : 0 < am_maplen am -> acond_ok (EV xvA) (mkAC BC_NE (SAlu ALU_SRL (SOff aGBITS 0) (SLit 12)) (SLit 0))).
{ intros Hml1. cprep. denA. rewrite !lit64_small by lia. change (12 mod 64) with 12. change (0 mod 2 ^ 64) with 0. rewrite Ebits, bits_shiftr12 by lia.
destruct (Z.eqb_spec (am_maplen am) 0); [lia | reflexivity]. }
assert (C_strlt : 0 < am_maplen am -> am_sc am < 48 -> am_maplen am * 4096 - UNIT < class_size (am_sc am) ->
acond_ok (EV xvA) (mkAC BC_LTU (SOff aMP (-16)) (SAlu ALU_SLL (SOff aSCL 0) (SLit 4)))).
{ intros Hml1 H48 Hlt. rewrite (Escl H48) in Hlt. unfold UNIT in Hlt. cprep. denA. rewrite (Z.mod_small (am_maplen am * 4096)) by lia. rewrite !lit64_small by lia. change (4 mod 64) with 4.
unfold sll64. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. rewrite Z.mod_small by lia. apply Z.ltb_lt. lia. }
assert (C_strge : 0 < am_maplen am -> am_sc am < 48 -> class_size (am_sc am) <= am_maplen am * 4096 - UNIT -> acond_ok (EV xvA) STRIDE_GE).
{ intros Hml1 H48 Hge. rewrite (Escl H48) in Hge. unfold UNIT in Hge. unfold STRIDE_GE. cprep. denA. rewrite (Z.mod_small (am_maplen am * 4096)) by lia. rewrite !lit64_small by lia. change (4 mod 64) with 4.
unfold sll64. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. rewrite Z.mod_small by lia.
destruct (Z.ltb_spec (am_maplen am * 4096 + -16) (scl_of (am_sc am) * 16)); [lia | reflexivity]. }
assert (C_nxg : match d with D1 => False | _ => True end -> acond_ok (EV xvA) (mkAC BC_NE (nextx d) (SOff aNG 0))).
{ intros Hd. cprep. destruct d; try (destruct Hd; fail); cbn [nextx]; denA; rewrite ?lit64_small by lia; unfold G in *.
- destruct (Z.eqb_spec 0 (ptr_addr L g)); [lia | reflexivity].
- destruct NA as [_ NA']. unfold N in *. destruct (Z.eqb_spec (ptr_addr L n) (ptr_addr L g)); [lia | reflexivity].
- destruct NA as [_ NA']. unfold N in *. destruct (Z.eqb_spec (ptr_addr L n) (ptr_addr L g)); [lia | reflexivity].
- destruct NA as [_ NA']. unfold N in *. destruct (Z.eqb_spec (ptr_addr L n) (ptr_addr L g)); [lia | reflexivity].
- destruct NA as [_ NA']. unfold N in *. destruct (Z.eqb_spec (ptr_addr L n) (ptr_addr L g)); [lia | reflexivity]. }
assert (C_last : am_last am <> 0 -> acond_ok (EV xvA) (mkAC BC_NE (SOff aLAST 0) (SLit 0))).
{ intros HL1. cprep. denA. rewrite !lit64_small by lia. change (0 mod 2 ^ 64) with 0. destruct (Z.eqb_spec (am_last am) 0); [lia | reflexivity]. }
assert (C_sc7lt : (am_sc am < 7 \/ 38 < am_sc am) -> acond_ok (EV xvA) (mkAC BC_LTU (SLit 31) (SOff aSC (-7)))).
{ intros Hb. cprep. rewrite U_sc7, U_lit. change (31 mod 2 ^ 64) with 31. apply Z.ltb_lt. destruct (Z.ltb_spec (am_sc am) 7); lia. }
assert (C_sc7ge : 7 <= am_sc am <= 38 -> acond_ok (EV xvA) (mkAC BC_GEU (SLit 31) (SOff aSC (-7)))).
{ intros Hb. cprep. rewrite U_sc7, U_lit. change (31 mod 2 ^ 64) with 31. destruct (Z.ltb_spec (am_sc am) 7); [lia|]. destruct (Z.ltb_spec 31 (am_sc am - 7)); [lia | reflexivity]. }
assert (C_bnclt : 7 <= am_sc am <= 38 -> znth (am_sc am - 7) (st_bounces A) < 100 -> acond_ok (EV xvA) (mkAC BC_LTU (SOff aBNC 0) (SLit 100))).
{ intros Hb Hlt. pose proof (bounces_range Hb). cprep. denA. rewrite (Z.mod_small _ 256) by lia. rewrite !lit64_small by lia. apply Z.ltb_lt. lia. }
assert (C_bncge : 7 <= am_sc am <= 38 -> 100 <= znth (am_sc am - 7) (st_bounces A) -> acond_ok (EV xvA) (mkAC BC_GEU (SOff aBNC 0) (SLit 100))).
{ intros Hb Hge. pose proof (bounces_range Hb). cprep. denA. rewrite (Z.mod_small _ 256) by lia. rewrite !lit64_small by lia. destruct (Z.ltb_spec (znth (am_sc am - 7) (st_bounces A)) 100); [lia | reflexivity]. }
assert (C_usg9 : am_last am = 0 -> 9 * (am_last am + 1) <= usage_of A (am_sc am) -> acond_ok (EV xvA) (mkAC BC_GEU (SOff aUSG 0) (SLit 9))).
{ intros HL0 Hu9. cprep. denA. rewrite (Z.mod_small (usage_of A (am_sc am))) by lia. rewrite !lit64_small by lia. change (9 mod 2 ^ 64) with 9.
destruct (Z.ltb_spec (usage_of A (am_sc am)) 9); [lia | reflexivity]. }
assert (C_usgN : 9 * (am_last am + 1) <= usage_of A (am_sc am) -> acond_ok (EV xvA) (mkAC BC_GEU (SOff aUSG 0) NINE)).
{ intros Hu9. cprep. rewrite U_NINE. denA. rewrite (Z.mod_small (usage_of A (am_sc am))) by lia. rewrite !lit64_small by lia.
destruct (Z.ltb_spec (usage_of A (am_sc am)) (9 * (am_last am + 1))); [lia | reflexivity]. }
assert (C_l18 : am_last am + 1 < 20 -> acond_ok (EV xvA) (mkAC BC_GEU (SLit 18) (SOff aLAST 0))).
{ intros H20. cprep. denA. rewrite !lit64_small by lia. change (18 mod 2 ^ 64) with 18. destruct (Z.ltb_spec 18 (am_last am)); [lia | reflexivity]. }
assert (C_sc47 : am_sc am = 63 -> acond_ok (EV xvA) (mkAC BC_LTU (SLit 47) (SOff aSC 0))).
{ intros H63. cprep. denA. rewrite !lit64_small by lia. change (47 mod 2 ^ 64) with 47. apply Z.ltb_lt. lia. }
pose proof VALID as VA.
destruct q; cbn [toMq] in QF1; cbn [q_conds conds_ok]; cbn [validA] in VA.
- split; [exact C_all|]. split; [apply C_sc47; exact QF1 | exact I].
- destruct QF1 as (H48 & Hml0). repeat split; auto; apply C_le47; lia.
- destruct QF1 as (H48 & Hml1 & HL0 & Hlt). repeat split; auto; [apply C_le47; lia | apply C_strlt; auto; lia].
- destruct QF1 as (H48 & (Hml1 & HL0 & Hge) & Hnx). repeat split; auto; [apply C_le47; lia | apply C_strge; auto; lia | apply C_nxg; destruct d; try exact I; discriminate VA].
- destruct QF1 as (H48 & (Hml1 & HL1) & Hnx). repeat split; auto; [apply C_le47; lia | apply C_nxg; destruct d; try exact I; discriminate VA].
- destruct QF1 as (H48 & (Hml1 & HL0 & Hge) & Hnx & Hb). repeat split; auto; [apply C_le47; lia | apply C_strge; auto; lia].
- destruct QF1 as (H48 & (Hml1 & HL1) & Hnx & Hb). repeat split; auto. apply C_le47; lia.
- destruct QF1 as (H48 & (Hml1 & HL0 & Hge) & Hnx & Hb & Hbn). repeat split; auto; [apply C_le47; lia | apply C_strge; auto; lia].
- destruct QF1 as (H48 & (Hml1 & HL1) & Hnx & Hb & Hbn). repeat split; auto. apply C_le47; lia.
- destruct QF1 as (H48 & (Hml1 & HL0 & Hge) & Hnx & (Hb & Hbn) & Hu9 & H20). repeat split; auto; [apply C_le47; lia | apply C_strge; auto; lia].
- destruct QF1 as (H48 & (Hml1 & HL1) & Hnx & (Hb & Hbn) & Hu9 & H20). repeat split; auto. apply C_le47; lia.
Qed.
Lemma dconds_ok : conds_ok (EV xvA) (d_conds d).
Proof.
facts0. pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _ & Hml & Hsc). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof n_apart as NA. pose proof n_facts as (N1 & N2 & _). pose proof hd_factsA as HDF.
pose proof DF as DF0. unfold dfacts in DF0.
assert (C48 : am_sc am < 48 -> acond_ok (EV xvA) (mkAC BC_LTU (SOff aSC 0) (SLit 48))).
{ intros H48. cprep. denA. rewrite !lit64_small by lia. apply Z.ltb_lt. lia. }
assert (CNG : n <> g /\ (G + 40 <= N \/ N + 40 <= G) -> acond_ok (EV xvA) (mkAC BC_NE (SOff aN 0) (SOff aNG 0))).
{ intros [_ AP]. cprep. denA. rewrite !lit64_small by lia. unfold N, G in *. destruct (Z.eqb_spec (ptr_addr L n) (ptr_addr L g)); [lia | reflexivity]. }
assert (CHD : 0 <= hdv < 2 ^ 64 /\ hdv <> G -> acond_ok (EV xvA) (mkAC BC_NE (SOff aHD 0) (SOff aNG 0))).
{ intros [R NE]. cprep. denA. rewrite (Z.mod_small hdv) by lia. rewrite !lit64_small by lia. unfold G in *. destruct (Z.eqb_spec hdv (ptr_addr L g)); [lia | reflexivity]. }
destruct d; cbn [toMd] in DF0; cbn [d_conds conds_ok].
- exact I.
- destruct DF0 as (_ & _ & H48 & _). split; [apply C48; lia | exact I].
- destruct DF0 as (_ & _ & _ & _ & _ & _ & _ & H48 & _). repeat split; [apply C48; lia | apply CNG; exact NA | apply CHD; exact HDF].
- destruct DF0 as (_ & _ & _ & _ & _ & _ & _ & H48 & _). repeat split; [apply C48; lia | apply CNG; exact NA].
- destruct DF0 as (_ & _ & _ & _ & _ & H48 & _). repeat split; [apply C48; lia | apply CNG; exact NA | apply CHD; exact HDF].
- destruct DF0 as (_ & _ & _ & _ & _ & H48 & _). repeat split; [apply C48; lia | apply CNG; exact NA].
Qed.
Lemma factsA_ok : facts_ok (EV xvA) (a1_facts q d).
Proof.
pose proof (proj1 alloc_ceiling_val) as ACV_p9.
unfold a1_facts, facts_ok. cbn [f_atoms f_conds f_alias]. split; [apply atomsA_ok|]. split; [|apply aliasA_ok].
split; [apply cond_C32_okA|]. apply conds_ok_app; [apply qconds_ok | apply dconds_ok].
Qed.
Lemma meta_vs_group qq aq : usedX X A qq aq -> ptr_addr L qq + 40 <= NM \/ NM + 16 <= ptr_addr L qq.
Proof.
intros Uq. destruct (meta_factsA qq aq Uq) as (_ & _ & _ & _ & (a & Ha & Ia & Q1 & Q2)).
destruct n_facts as (_&_&_&_&_&_&_&_&(rg & Hr & Hk & Hl & Irg & M1 & M2)&_).
pose proof HL as (_ & _ & PW & _).
assert (Hne : (LMem a, PGSZ) <> (LMem (SP (prid (am_mem an)) 0), rg_len rg)) by (apply (area_entry_not_region X (Some (g, i)) U A HI a _ rg Ha Hr Hk)).
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint A) _ _ PW Ia Irg Hne) as [Dj|Dj];
unfold ranges_disjoint, crange in Dj; cbn [fst snd loc_addr] in Dj; cbn [loc_addr] in Q1, Q2; unfold PGSZ in *; lia.
Qed.
Lemma rok_metagA : region_ok src0segs (EV xvA) mem (reg_metagA' d).
Proof.
facts0. pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _ & Hml & Hsc). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof n_facts as (N1 & N2 & _). pose proof p_facts as (P1 & P2 & _).
assert (BY : forall dd w val, match val with VLo5 _ => False | _ => True end -> In (MCell (LMem (padd g dd)) w val) (meta_slot_cells g (Some (MUsed am))) ->
bytes_are mem (G + dd) w (sval_num L val)).
{ intros dd w val Hv Hc kk Hkk. pose proof (meta_cellA g am _ Hu Hc) as C. unfold cell_mem in C. cbn [mc_val mc_loc mc_w] in C.
rewrite loc_addr_padd in C. destruct val; first [exact (C kk Hkk) | destruct Hv]. }
assert (W : forall o, 0 <= o < 40 -> writable_at src0segs mem (G + o)).
{ intros o Ho. apply present_writable. apply (meta_presentA g am _ Hu). unfold G. lia. }
assert (BP : bytes_are mem (G + 0) 8 (optrZ L (am_prev am))).
{ pose proof (BY 0 8%nat (optr (am_prev am)) ltac:(destruct (am_prev am); exact I) ltac:(cbn; tauto)) as B0. unfold optrZ. destruct (am_prev am); exact B0. }
assert (BN : bytes_are mem (G + 8) 8 (optrZ L (am_next am))).
{ pose proof (BY 8 8%nat (optr (am_next am)) ltac:(destruct (am_next am); exact I) ltac:(cbn; tauto)) as B0. unfold optrZ. destruct (am_next am); exact B0. }
assert (VP : bv_unsigned (sv_denot (EV xvA) (prevx d)) = optrZ L (am_prev am) mod 2 ^ 64 /\ bv_unsigned (sv_denot (EV xvA) (nextx d)) = optrZ L (am_next am) mod 2 ^ 64).
{ pose proof DF as DF0. unfold dfacts in DF0. destruct d; cbn [toMd] in DF0; cbn [prevx nextx].
- destruct DF0 as (Hn & Hp & _). rewrite Hn, Hp, !U_lit. cbn [optrZ]. split; reflexivity.
- destruct DF0 as (Hn & Hp & _). rewrite Hn, Hp, !(U_off0 _ XR0). unfold aNG. rewrite EG0. cbn [optrZ]. unfold G. rewrite Z.mod_small by lia. split; reflexivity.
- destruct DF0 as (Hn & Hp & _). rewrite Hn, Hp, !(U_off0 _ XR0). unfold aP, aN, xvA. cbn [Nat.ltb Nat.leb optrZ]. unfold P, N in *. rewrite !Z.mod_small by lia. split; reflexivity.
- destruct DF0 as (Hn & Hp & _). rewrite Hn, Hp, !(U_off0 _ XR0). unfold aP, aN, xvA. cbn [Nat.ltb Nat.leb optrZ]. unfold P, N in *. rewrite !Z.mod_small by lia. split; reflexivity.
- destruct DF0 as (Hn & Hp & _). rewrite Hn, Hp, !(U_off0 _ XR0). unfold aN, xvA. cbn [Nat.ltb Nat.leb optrZ]. unfold N in *. rewrite !Z.mod_small by lia. split; reflexivity.
- destruct DF0 as (Hn & Hp & _). rewrite Hn, Hp, !(U_off0 _ XR0). unfold aN, xvA. cbn [Nat.ltb Nat.leb optrZ]. unfold N in *. rewrite !Z.mod_small by lia. split; reflexivity. }
destruct VP as [VPp VPn].
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_metagA' metagA_chunks]; rewrite (base_val_EV _ XR0); unfold aNG; rewrite EG0; [lia | lia | intros o Ho; apply W; destruct d; lia |].
repeat apply Forall_cons; [| | | | | | apply Forall_nil].
- apply (chunk_ok_val _ _ _ _ 8%N _ (optrZ L (am_prev am) mod 2 ^ 64)); [exact VPp | apply M64w | intros kk Hkk; rewrite le_byte_mod64; exact (BP kk Hkk)].
- apply (chunk_ok_val _ _ _ _ 8%N _ (optrZ L (am_next am) mod 2 ^ 64)); [exact VPn | apply M64w | intros kk Hkk; rewrite le_byte_mod64; exact (BN kk Hkk)].
- apply (chunk_ok_val _ _ _ _ 8%N _ (ptr_addr L (am_mem am) mod 2 ^ 64)); [apply (U_off0 _ XR0) | apply M64w |].
intros kk Hkk. rewrite le_byte_mod64. apply (BY 16 8%nat (VP (am_mem am)) I ltac:(cbn; tauto) kk Hkk).
- apply (chunk_ok_val _ _ _ _ 4%N _ (am_avail am)); [apply (U_off0 _ XR0) | cbn; lia |]. apply (BY 24 4%nat (VZ (am_avail am)) I ltac:(cbn; tauto)).
- apply (chunk_ok_val _ _ _ _ 4%N _ (am_freed am)); [apply (U_off0 _ XR0) | cbn; lia |]. apply (BY 28 4%nat (VZ (am_freed am)) I ltac:(cbn; tauto)).
- apply (chunk_ok_val _ _ _ _ 8%N _ (meta_bits am)); [apply (U_off0 _ XR0) | cbn; lia |]. apply (BY 32 8%nat (VZ (meta_bits am)) I ltac:(cbn; tauto)).
Qed.
Lemma rok_gotA : region_ok src0segs (EV xvA) mem reg_got.
Proof.
pose proof ST as ST0.
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_got base_val]; unfold GOT, src0_D_got_stack_chk_guard; [lia | lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 8%N _ GUARD); [apply U_lit | cbn; unfold GUARD, src0_D_stack_chk_guard; lia |].
intros kk Hkk. exact (st_got _ _ ST0 kk Hkk).
Qed.
Lemma rok_guardA : region_ok src0segs (EV xvA) mem reg_guard.
Proof.
facts0. apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_guard base_val]; unfold GUARD, src0_D_stack_chk_guard; [lia | lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 8%N _ (gv mod 2 ^ 64)); [apply (U_off0 _ XR0) | apply M64w |].
intros kk Hkk. rewrite le_byte_mod64. exact (Hgv kk Hkk).
Qed.
Lemma rok_stkA : region_ok src0segs (EV xvA) mem reg_ntstk.
Proof.
facts0. pose proof sp_facts as (S16 & Sceil & S63 & WSTK). pose proof (proj1 alloc_ceiling_val).
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_ntstk]; rewrite (base_val_EV _ XR0); unfold aSP; rewrite ESP; [lia | lia | | apply Forall_nil].
intros o Ho. apply WSTK. lia.
Qed.
Lemma act_bytesA : am_sc am < 48 -> bytes_are mem (xvA aACT + 0) 8 hdv.
Proof.
pose proof g_facts as (_&_&_&_&_&_&_&_&_&_&_&_& Hsc). intros H48. unfold hdv. eapply bytes_are_at'; [apply (ctx_active_cellA (Z.to_nat (am_sc am))); lia|].
unfold xvA, aACT. cbn [Nat.ltb Nat.leb]. rewrite Z2Nat.id by lia. lia.
Qed.
Lemma rok_d : Forall (region_ok src0segs (EV xvA) mem) (d_mem d).
Proof.
facts0. pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _ & Hml & Hsc). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof n_facts as (N1 & N2 & N8 & Nimg & M1 & M2 & M16 & Mimg & (rg & Hr & Hk & Hl & Irg & R1 & R2) & Nfr & Nai & (b & Eb & Hb) & Haidx). pose proof p_facts as (P1 & P2 & P8 & Pimg).
pose proof hd_factsA as HDF. pose proof Un as Un0. pose proof Up as Up0.
pose proof DF as DF0. unfold dfacts in DF0.
assert (AW : am_sc am < 48 -> forall o, 0 <= o < 8 -> writable_at src0segs mem (xvA aACT + o)).
{ intros H48 o Ho. apply (ctx_writable mem SO). unfold xvA, aACT. cbn [Nat.ltb Nat.leb]. unfold CTX_SIZE. lia. }
assert (AR : am_sc am < 48 -> CTX + 80 <= xvA aACT /\ xvA aACT + 392 < 2 ^ 64) by (intros H48; unfold xvA, aACT; cbn [Nat.ltb Nat.leb]; unfold CTX, src0_D_malloc_context; lia).
assert (RACT : am_sc am < 48 -> forall val w, bv_unsigned (sv_denot (EV xvA) val) = hdv mod 2 ^ 64 -> region_ok src0segs (EV xvA) mem (reg_act val w)).
{ intros H48 val w Hval. specialize (AR H48). unfold CTX, src0_D_malloc_context in AR.
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_act]; rewrite (base_val_EV _ XR0); [lia | lia | intros o Ho; apply (AW H48); destruct w; lia |].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 8%N _ (hdv mod 2 ^ 64)); [exact Hval | apply M64w |].
intros kk Hkk. rewrite le_byte_mod64. exact (act_bytesA H48 kk Hkk). }
assert (RACTg : am_sc am < 48 -> active_hd A (am_sc am) = Some g -> forall w, region_ok src0segs (EV xvA) mem (reg_act (SOff aNG 0) w)).
{ intros H48 Hhd w. apply (RACT H48). rewrite (U_off0 _ XR0). unfold aNG. rewrite EG0. unfold hdv. rewrite Hhd. cbn [optrZ]. unfold G in *. rewrite Z.mod_small by lia. reflexivity. }
assert (RACTh : am_sc am < 48 -> forall w, region_ok src0segs (EV xvA) mem (reg_act (SOff aHD 0) w)).
{ intros H48 w. apply (RACT H48). rewrite (U_off0 _ XR0). reflexivity. }
assert (WN : forall lo hi, 0 <= lo -> hi <= 40 -> forall o, lo <= o < hi -> writable_at src0segs mem (N + o)).
{ intros lo hi Hlo Hhi o Ho. apply present_writable. apply (meta_presentA n an _ Un0). unfold N. lia. }
assert (WP : forall o, 8 <= o < 16 -> writable_at src0segs mem (P + o)).
{ intros o Ho. apply present_writable. apply (meta_presentA p ap _ Up0). unfold P. lia. }
assert (Rp8 : region_ok src0segs (EV xvA) mem reg_p8).
{ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_p8]; rewrite (base_val_EV _ XR0); unfold aP, xvA; cbn [Nat.ltb Nat.leb]; [lia | lia | exact WP | apply Forall_nil]. }
assert (Rn0 : region_ok src0segs (EV xvA) mem reg_n0).
{ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_n0]; rewrite (base_val_EV _ XR0); unfold aN, xvA; cbn [Nat.ltb Nat.leb]; [lia | lia | apply (WN 0 8); lia | apply Forall_nil]. }
assert (Rn016 : region_ok src0segs (EV xvA) mem reg_n016).
{ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_n016]; rewrite (base_val_EV _ XR0); unfold aN, xvA; cbn [Nat.ltb Nat.leb]; [lia | lia | apply (WN 0 16); lia | apply Forall_nil]. }
assert (BYn : forall dd w val, match val with VLo5 _ => False | _ => True end -> In (MCell (LMem (padd n dd)) w val) (meta_slot_cells n (Some (MUsed an))) ->
bytes_are mem (N + dd) w (sval_num L val)).
{ intros dd w val Hv Hc kk Hkk. pose proof (meta_cellA n an _ Un0 Hc) as C. unfold cell_mem in C. cbn [mc_val mc_loc mc_w] in C.
rewrite loc_addr_padd in C. destruct val; first [exact (C kk Hkk) | destruct Hv]. }
assert (Rn24 : am_avail an = 0 -> region_ok src0segs (EV xvA) mem reg_n24).
{ intros Hav0. apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_n24]; rewrite (base_val_EV _ XR0); unfold aN; change (xvA 59) with N; [lia | lia | apply (WN 24 32); lia |].
repeat apply Forall_cons; [| | | apply Forall_nil].
- apply (chunk_ok_val _ _ _ _ 8%N _ NM); [rewrite (U_off0 _ XR0); reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia |].
apply (BYn 16 8%nat (VP (am_mem an)) I ltac:(cbn; tauto)).
- apply chunk_ok_lit0. intros kk Hkk. pose proof (BYn 24 4%nat (VZ (am_avail an)) I ltac:(cbn; tauto) kk Hkk) as B0. rewrite Hav0 in B0. cbn [sval_num] in B0. rewrite le_byte_0 in B0. exact B0.
- apply (chunk_ok_val _ _ _ _ 4%N _ (am_freed an)); [rewrite (U_off0 _ XR0); reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia |].
apply (BYn 28 4%nat (VZ (am_freed an)) I ltac:(cbn; tauto)). }
assert (Raidx : region_ok src0segs (EV xvA) mem reg_naidx).
{ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_naidx]; rewrite (base_val_EV _ XR0); unfold aNMEM; change (xvA 60) with NM; [lia | lia | intros o Ho; lia |].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 1%N _ aidxb); [rewrite (U_off0 _ XR0); reflexivity | unfold aidxb; rewrite Eb; pose proof (u8_range b); cbn; lia |].
intros kk Hkk. destruct kk; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Eb. f_equal. unfold aidxb. rewrite Eb.
unfold le_byte. change (2 ^ (8 * Z.of_nat (N.to_nat 1))) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. pose proof (u8_range b).
rewrite (Z.mod_small (bv_unsigned b) 256) by lia. rewrite Z.mod_small by lia. symmetry. apply Z_to_bv_bv_unsigned. }
destruct d; cbn [toMd] in DF0; cbn [d_mem].
- apply Forall_nil.
- destruct DF0 as (_ & _ & H48 & Hhd & _). apply Forall_cons; [apply RACTg; [lia | exact Hhd] | apply Forall_nil].
- destruct DF0 as (_ & _ & _ & _ & _ & _ & _ & H48 & _). repeat apply Forall_cons; [apply RACTh; lia | exact Rp8 | exact Rn0 | apply Forall_nil].
- destruct DF0 as (_ & _ & _ & _ & _ & _ & _ & H48 & Hhd & Hav0). repeat apply Forall_cons; [apply RACTg; [lia | exact Hhd] | exact Rp8 | exact Rn0 | apply Rn24; exact Hav0 | exact Raidx | apply Forall_nil].
- destruct DF0 as (_ & _ & _ & _ & _ & H48 & _). repeat apply Forall_cons; [apply RACTh; lia | exact Rn016 | apply Forall_nil].
- destruct DF0 as (_ & _ & _ & _ & _ & H48 & Hhd & Hav0). repeat apply Forall_cons; [apply RACTg; [lia | exact Hhd] | exact Rn016 | apply Rn24; exact Hav0 | exact Raidx | apply Forall_nil].
Qed.
Lemma rok_q : Forall (region_ok src0segs (EV xvA) mem) (q_mem q).
Proof.
facts0. pose proof g_facts as (_&_&_&_&_&_&_&_&_&_&_&_& Hsc). pose proof usage_range as UR. pose proof sc_q as SQ.
pose proof QF as QF0. unfold qfacts, bouncing in QF0. destruct QF0 as [_ QF1].
assert (Rtq : am_sc am < 48 -> region_ok src0segs (EV xvA) mem reg_tq2).
{ intros H48. assert (HSCL : 1 <= scl_of (am_sc am) <= 8191) by (unfold scl_of; replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia); apply scl_range; lia).
assert (ETQ : xvA aTQ2 = TBL + 2 * am_sc am) by (unfold xvA, aTQ2; cbn [Nat.ltb Nat.leb]; replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_tq2]; rewrite (base_val_EV _ XR0), ETQ; unfold TBL, src0_D_size_classes; [lia | lia | intros o Ho; lia |].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 2%N _ (scl_of (am_sc am))); [rewrite (U_off0 _ XR0); reflexivity | cbn; lia |].
rewrite Z.add_0_r. apply tq_bytesA. lia. }
assert (Rbnc : 7 <= am_sc am <= 38 -> region_ok src0segs (EV xvA) mem reg_bnc).
{ intros Hb. pose proof (bounces_range Hb) as BR.
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_bnc]; rewrite (base_val_EV _ XR0); unfold xvA, aSC; cbn [Nat.ltb Nat.leb]; unfold CTX, src0_D_malloc_context; [lia | lia | intros o Ho; lia |].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 1%N _ (znth (am_sc am - 7) (st_bounces A))); [rewrite (U_off0 _ XR0); unfold xvA, aBNC; cbn [Nat.ltb Nat.leb]; apply Z.mod_small; lia | cbn; lia |].
eapply bytes_are_at'; [apply (ctx_bounces_cellA (Z.to_nat (am_sc am - 7))); lia|]. unfold CTX, src0_D_malloc_context. rewrite Z2Nat.id by lia. lia. }
assert (Rusg : am_sc am < 48 -> region_ok src0segs (EV xvA) mem reg_usg).
{ intros H48. apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_usg]; rewrite (base_val_EV _ XR0); unfold xvA, aACT; cbn [Nat.ltb Nat.leb]; unfold CTX, src0_D_malloc_context; [lia | lia | intros o Ho; lia |].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 8%N _ (usage_of A (am_sc am))); [rewrite (U_off0 _ XR0); unfold xvA, aUSG; cbn [Nat.ltb Nat.leb]; apply Z.mod_small; lia | cbn; lia |].
eapply bytes_are_at'; [apply (ctx_usage_cellA (Z.to_nat (am_sc am))); lia|]. unfold CTX, src0_D_malloc_context. rewrite Z2Nat.id by lia. lia. }
destruct q; cbn [toMq] in QF1, SQ; cbn [q_mem]; repeat apply Forall_cons; try apply Forall_nil;
first [apply Rtq; lia | apply Rbnc; tauto | apply Rusg; lia].
Qed.
Lemma regionsA_ok : Forall (region_ok src0segs (EV xvA) mem) (a1_mem q d).
Proof.
unfold a1_mem. apply Forall_cons; [apply rok_metagA|]. apply Forall_cons; [apply rok_gotA|]. apply Forall_cons; [apply rok_guardA|].
apply Forall_cons; [apply rok_stkA|]. apply Forall_app_intro; [apply rok_d | apply rok_q].
Qed.
Lemma pdA : pairwise_disjoint (EV xvA) (a1_mem q d).
Proof.
facts0. pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _ & Hml & Hsc). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof sp_facts as (S16 & Sceil & S63 & _). pose proof (off_img G Gimg) as GI. pose proof sc_q as SQ.
pose proof n_facts as (N1 & N2 & N8 & Nimg & M1 & M2 & M16 & Mimg & _). pose proof p_facts as (P1 & P2 & P8 & Pimg).
pose proof (off_img N Nimg) as NI. pose proof (off_img P Pimg) as PI.
assert (MI : NM + 16 <= 0x10000 \/ 0x51000 <= NM).
{ destruct (img_gap 0x10000 (0x51000 - 0x10000) NM 16 ltac:(intros x Hx; unfold in_img1; lia) ltac:(lia) Mimg ltac:(lia)); lia. }
pose proof (meta_vs_group g am Hu) as VG. pose proof (meta_vs_group n an Un) as VN. pose proof (meta_vs_group p ap Up) as VP. fold G in VG. fold N in VN. fold P in VP.
pose proof n_apart as NA. pose proof p_apart as PA. pose proof VALID as VA.
clear Hi Hav Hfr Hbits Hb32 Hml Gimg Nimg Pimg.
unfold a1_mem.
destruct q, d; try discriminate VA; cbn [toMq] in SQ;
try (destruct NA as [Hng NA']); try (destruct PA as (Hpg & Hpn & PA1 & PA2));
cbn [d_mem q_mem app pairwise_disjoint all_disjoint]; unfold extent_disjoint;
cbn [r_base r_lo r_hi reg_metagA' reg_got reg_guard reg_ntstk reg_act reg_p8 reg_n0 reg_n016 reg_n24 reg_naidx reg_tq2 reg_bnc reg_usg]; rewrite !(base_val_EV _ XR0); cbn [base_val];
unfold aNG, aSP; rewrite EG0, ESP;
unfold xvA, aACT, aTQ2, aSC, aP, aN, aNMEM; cbn [Nat.ltb Nat.leb];
try (replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia));
unfold GOT, GUARD, CTX, TBL, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_malloc_context, src0_D_size_classes; unfold G, N, P, NM, SP0 in *;
clear HI Hu HB NPRE Hgv HC1 QF DF XR0 EG0 EI0 VA; repeat split;
first [ (try clear GI; try clear NI; try clear PI; try clear MI; try clear VG; try clear VN; try clear VP; try clear NA'; try clear PA1; try clear PA2; lia)
| (try clear NI; try clear PI; try clear MI; try clear VG; try clear VN; try clear VP; try clear NA'; try clear PA1; try clear PA2; lia)
| (try clear GI; try clear PI; try clear MI; try clear VG; try clear VN; try clear VP; try clear NA'; try clear PA1; try clear PA2; lia)
| (try clear GI; try clear NI; try clear MI; try clear VG; try clear VN; try clear VP; try clear NA'; try clear PA1; try clear PA2; lia)
| (try clear GI; try clear NI; try clear PI; try clear VG; try clear VN; try clear VP; try clear NA'; try clear PA1; try clear PA2; lia)
| (try clear GI; try clear NI; try clear PI; try clear MI; try clear VN; try clear VP; try clear NA'; try clear PA1; try clear PA2; lia)
| (try clear GI; try clear NI; try clear PI; try clear MI; try clear VG; try clear VP; try clear NA'; try clear PA1; try clear PA2; lia)
| (try clear GI; try clear NI; try clear PI; try clear MI; try clear VG; try clear VN; try clear NA'; try clear PA1; try clear PA2; lia)
| (try clear GI; try clear NI; try clear PI; try clear MI; try clear VG; try clear VN; try clear VP; try clear PA1; try clear PA2; lia)
| (try clear GI; try clear NI; try clear PI; try clear MI; try clear VG; try clear VN; try clear VP; try clear NA'; try clear PA2; lia)
| (try clear GI; try clear NI; try clear PI; try clear MI; try clear VG; try clear VN; try clear VP; try clear NA'; try clear PA1; lia) ].
Qed.
Theorem memA_ok : mem_ok src0segs (EV xvA) mem (a1_mem q d).
Proof.
pose proof VALID as VA. split; [destruct q, d; try discriminate VA; vm_compute; reflexivity|]. split; [apply regionsA_ok | apply pdA].
Qed.
Theorem A1_entry_st_ok :
st_ok src0segs (EV xvA) (ss_A1 q d) (mkst regs (Z_to_bv 64 src0_A_nontrivial_free) mem (seg_rom src0segs)).
Proof.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts ss_A1 resv_denot].
repeat (split; [reflexivity|]). split; [apply regsA_ok|]. split; [apply memA_ok | apply factsA_ok].
Qed.
Definition A1s : astate :=
match d with
| D0 => A
| D1 => A_D1 A g am
| D2a => A_D2a A g am p n ap an
| D2b => A_D2b A g am p n ap an
| D2a' => A_D2a' A g am n an
| D2b' => A_D2b' A g am n an
end.
Definition amU : ameta := match d with D0 => am | _ => strip am end.
Lemma amU_strip : strip amU = strip am.
Proof. unfold amU. destruct d; destruct am; reflexivity. Qed.
Lemma len_active : length (st_active A) = 48%nat.
Proof. exact (proj1 (inv_ctx HI)). Qed.
Lemma footprint_set_active l s : footprint (set_active l s) = footprint s.
Proof. reflexivity. Qed.
Lemma A1s_facts :
footprint A1s = footprint A /\ st_regions A1s = st_regions A /\ st_areas A1s = st_areas A /\ MT A1s g = Some (MUsed amU) /\
st_usage A1s = st_usage A /\ st_seq A1s = st_seq A /\ st_unmap_seq A1s = st_unmap_seq A /\ st_bounces A1s = st_bounces A /\
st_free_meta_head A1s = st_free_meta_head A /\ length (st_active A1s) = 48%nat.
Proof.
pose proof len_active as LA. pose proof n_apart as NA. pose proof p_apart as PA.
assert (MG : MT A1s g = Some (MUsed amU)).
{ unfold A1s, amU, A_D1, A_D2a, A_D2b, A_D2a', A_D2b', A_unl, A_unl'. destruct d; rewrite ?MT_set_active, ?MT_upd_same; try reflexivity. exact Mg. }
assert (FP : footprint A1s = footprint A /\ st_regions A1s = st_regions A /\ st_areas A1s = st_areas A).
{ unfold A1s, A_D1, A_D2a, A_D2b, A_D2a', A_D2b', A_unl, A_unl'. destruct d; rewrite ?footprint_set_active, ?footprint_upd_meta; repeat split; reflexivity. }
destruct FP as (F1 & F2 & F3). split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact MG|].
unfold A1s, A_D1, A_D2a, A_D2b, A_D2a', A_D2b', A_unl, A_unl', act_n. destruct d;
cbn [st_usage st_seq st_unmap_seq st_bounces st_free_meta_head st_active set_active upd_meta set_metas]; rewrite ?length_lupd; repeat split; try reflexivity; exact LA.
Qed.
Section u.
Variable ms1 : machine_state.
Variable U1 : Z -> Z.
Hypothesis HS1 : st_ok src0segs (EV xvA) (SSA1 q d) ms1.
Hypothesis HF1 : frame_of (EV xvA) (a1_mem q d) mem (ms_mem ms1).
Hypothesis HI2 : Inv (g :: X) None U1 A1s.
Let mem1 := ms_mem ms1.
Let regs1 := ms_regs ms1.
Lemma post_shapeA : ms1 = mkst regs1 (Z_to_bv 64 XU) mem1 (seg_rom src0segs).
Proof.
pose proof (SSA1_shape q d VALID) as SH. pose proof HS1 as HS. remember (SSA1 q d) as ss eqn:Ess. clear Ess.
destruct SH as (Hpc & Hrv & _). rewrite <- Hpc. apply (st_ok_mkst src0segs _ _ _ HS Hrv).
Qed.
Lemma post_regsA :
getr regs1 (nat_to_reg 10) = Z_to_bv 64 G /\ getr regs1 (nat_to_reg 9) = Z_to_bv 64 GUARD /\ getr regs1 (nat_to_reg 18) = Z_to_bv 64 CTX /\
getr regs1 (nat_to_reg 2) = Z_to_bv 64 (SP0 - 96) /\
(forall r, In r [1; 3; 4; 8; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr regs1 (nat_to_reg r) = getr regs (nat_to_reg r)).
Proof.
facts0. pose proof g_facts as (_&_&_&_&_&_&G1&G2&_). pose proof sp_facts as (_ & Sceil & S63 & _). pose proof (proj1 alloc_ceiling_val).
pose proof (SSA1_shape q d VALID) as SH. pose proof HS1 as HS. remember (SSA1 q d) as ss eqn:Ess. clear Ess.
destruct SH as (Hpc & Hrv & Hview & _).
pose proof (fun r => st_ok_reg src0segs _ _ ms1 r HS) as RR.
unfold live_view, live_viewU in Hview. cbn [map] in Hview.
injection Hview as V1 V2 V3 V4 V8 V9 V10 V18 V19 V20 V21 V22 V23 V24 V25 V26 V27.
assert (NR : forall k, (1 <= k <= 31)%nat -> nat_to_reg k = Z_to_bv 5 (Z.of_nat k)).
{ intros k Hk. clear -Hk. apply bv_eq. rewrite nat_to_reg_unsigned by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity. }
assert (K : forall k e (V : sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat k)) = e), (1 <= k <= 31)%nat -> getr regs1 (nat_to_reg k) = sv_denot (EV xvA) e).
{ intros k e V Hk. unfold regs1. rewrite (NR k Hk), (RR (Z_to_bv 5 (Z.of_nat k))), V. reflexivity. }
assert (KE : forall k (V : sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat k)) = SOff k 0), (1 <= k <= 31)%nat -> getr regs1 (nat_to_reg k) = getr regs (nat_to_reg k)).
{ intros k V Hk. rewrite (K k _ V Hk). cbn [sv_denot EV ew]. rewrite Z.add_0_r. unfold xvA.
replace (k <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite !Z_to_bv_bv_unsigned. reflexivity. }
split; [rewrite (K 10%nat _ V10 ltac:(lia)); cbn [sv_denot EV ew]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EG0; reflexivity|].
split; [rewrite (K 9%nat _ V9 ltac:(lia)); reflexivity|].
split; [rewrite (K 18%nat _ V18 ltac:(lia)); reflexivity|].
split; [rewrite (K 2%nat _ V2 ltac:(lia)); cbn [sv_denot EV ew]; rewrite (lit64_small (xvA 2)) by apply XR0; rewrite ESP; reflexivity|].
intros r Hr. repeat (destruct Hr as [<-|Hr]; [apply KE; [assumption | lia] |]). destruct Hr.
Qed.
Lemma final_regionsA :
region_ok src0segs (EV xvA) mem1 (metagA_out d) /\ region_ok src0segs (EV xvA) mem1 reg_ntstk' /\
Forall (region_ok src0segs (EV xvA) mem1) (d_mem_out d).
Proof.
pose proof (SSA1_shape q d VALID) as SH. pose proof HS1 as HS. remember (SSA1 q d) as ss eqn:Ess. clear Ess.
destruct SH as (_ & _ & _ & Hm). pose proof (st_ok_mem_ok _ _ _ _ HS) as (_ & ROK & _). rewrite Hm in ROK. unfold memA1_out in ROK.
apply Forall_app in ROK as [R1 R2]. apply Forall_app in R2 as [R2 _].
apply Forall_cons_iff in R1 as [Ra R1]. apply Forall_cons_iff in R1 as [_ R1]. apply Forall_cons_iff in R1 as [_ R1]. apply Forall_cons_iff in R1 as [Rs _].
unfold mem1. auto.
Qed.
Lemma frameA :
bytes_are mem1 (SP0 - 48) 8 gv /\
bytes_are mem1 (SP0 - 40) 8 (bv_unsigned (getr regs (nat_to_reg 19))) /\
bytes_are mem1 (SP0 - 32) 8 (bv_unsigned (getr regs (nat_to_reg 18))) /\
bytes_are mem1 (SP0 - 24) 8 (bv_unsigned (getr regs (nat_to_reg 9))) /\
bytes_are mem1 (SP0 - 16) 8 (bv_unsigned (getr regs (nat_to_reg 8))) /\
bytes_are mem1 (SP0 - 8) 8 (bv_unsigned (getr regs (nat_to_reg 1))) /\
(forall a, SP0 - 96 <= a < SP0 -> writable_at src0segs mem1 a).
Proof.
facts0. destruct final_regionsA as (_ & Rs & _). destruct Rs as (_ & _ & W & C). cbn [r_base r_wlo r_whi r_chunks reg_ntstk' ntstk_chunks] in W, C.
rewrite (base_val_EV _ XR0) in W, C. unfold aSP in W, C. rewrite ESP in W, C. unfold ntstk_chunks in C.
apply Forall_cons_iff in C as [C48 C]. apply Forall_cons_iff in C as [C40 C]. apply Forall_cons_iff in C as [C32 C].
apply Forall_cons_iff in C as [C24 C]. apply Forall_cons_iff in C as [C16 C]. apply Forall_cons_iff in C as [C8 _].
assert (RB : forall off e z, chunk_ok src0segs (EV xvA) mem1 SP0 (mkChunk off (CVal 8 e)) -> bv_unsigned (sv_denot (EV xvA) e) = z mod 2 ^ 64 -> bytes_are mem1 (SP0 + off) 8 z).
{ intros off e z Hc Hv kk Hkk. pose proof (chunk8_cell xvA L mem1 SP0 off e z (LCtx (SP0 + off - ly_ctx L)) (VZ z) Hc Hv ltac:(cbn; lia) eq_refl I) as CM.
unfold cell_mem in CM. cbn [mc_val mc_loc mc_w sval_num loc_addr] in CM. replace (ly_ctx L + (SP0 + off - ly_ctx L)) with (SP0 + off) in CM by lia. exact (CM kk Hkk). }
assert (RG : forall k, (1 <= k <= 31)%nat -> bv_unsigned (sv_denot (EV xvA) (SOff k 0)) = bv_unsigned (getr regs (nat_to_reg k)) mod 2 ^ 64).
{ intros k Hk. rewrite (U_off0 _ XR0). unfold xvA. replace (k <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia). symmetry. apply Z.mod_small. apply u64_range. }
repeat match goal with |- _ /\ _ => split end.
- replace (SP0 - 48) with (SP0 + -48) by lia. eapply RB; [eassumption | rewrite (U_off0 _ XR0); reflexivity].
- replace (SP0 - 40) with (SP0 + -40) by lia. eapply RB; [eassumption | apply RG; lia].
- replace (SP0 - 32) with (SP0 + -32) by lia. eapply RB; [eassumption | apply RG; lia].
- replace (SP0 - 24) with (SP0 + -24) by lia. eapply RB; [eassumption | apply RG; lia].
- replace (SP0 - 16) with (SP0 + -16) by lia. eapply RB; [eassumption | apply RG; lia].
- replace (SP0 - 8) with (SP0 + -8) by lia. eapply RB; [eassumption | apply RG; lia].
- intros a Ha. replace a with (SP0 + (a - SP0)) by lia. apply W. lia.
Qed.
Definition kA : nat := Z.to_nat (am_sc am).
Definition NEWg : list mcell := match d with D0 => [] | _ => [MCell (LMem (padd g 0)) 8 (VZ 0); MCell (LMem (padd g 8)) 8 (VZ 0)] end.
Definition navail : Z := Z.land (am_freed an) (ones (am_aidx an)).
Definition nfreed : Z := Z.ldiff (am_freed an) (ones (am_aidx an)).
Definition NEWd : list mcell :=
match d with
| D0 => []
| D1 => [act_cell kA None]
| D2a => [MCell (LMem (padd n 0)) 8 (VP p); MCell (LMem (padd p 8)) 8 (VP n)]
| D2b => [act_cell kA (Some n); MCell (LMem (padd n 0)) 8 (VP p); MCell (LMem (padd p 8)) 8 (VP n);
MCell (LMem (padd n 24)) 4 (VZ navail); MCell (LMem (padd n 28)) 4 (VZ nfreed)]
| D2a' => [MCell (LMem (padd n 0)) 8 (VP n); MCell (LMem (padd n 8)) 8 (VP n)]
| D2b' => [act_cell kA (Some n); MCell (LMem (padd n 0)) 8 (VP n); MCell (LMem (padd n 8)) 8 (VP n);
MCell (LMem (padd n 24)) 4 (VZ navail); MCell (LMem (padd n 28)) 4 (VZ nfreed)]
end.
Definition NEW : list mcell := NEWg ++ NEWd.
Definition in_winA (a : Z) : Prop :=
(match d with D0 => False | _ => G <= a < G + 16 end) \/
(SP0 - 96 <= a < SP0) \/
match d with
| D0 => False
| D1 => xvA aACT <= a < xvA aACT + 8
| D2a => (P + 8 <= a < P + 16) \/ (N <= a < N + 8)
| D2b => (xvA aACT <= a < xvA aACT + 8) \/ (P + 8 <= a < P + 16) \/ (N <= a < N + 8) \/ (N + 24 <= a < N + 32)
| D2a' => N <= a < N + 16
| D2b' => (xvA aACT <= a < xvA aACT + 8) \/ (N <= a < N + 16) \/ (N + 24 <= a < N + 32)
end.
Lemma wrange_winA a : in_wrange (EV xvA) (a1_mem q d) a -> in_winA a.
Proof.
facts0. intros (r & Hr & Ha). unfold a1_mem in Hr. unfold in_winA.
rewrite !in_app_iff in Hr. cbn [In d_mem q_mem] in Hr.
destruct Hr as [[<-|[<-|[<-|[<-|[]]]]] | [Hr | Hr]].
- left. destruct d; cbn [reg_metagA' r_base r_wlo r_whi] in Ha; rewrite (base_val_EV _ XR0) in Ha; unfold aNG in Ha; rewrite EG0 in Ha; lia.
- cbn [reg_got r_base r_wlo r_whi base_val] in Ha. lia.
- cbn [reg_guard r_base r_wlo r_whi base_val] in Ha. lia.
- right; left. cbn [reg_ntstk r_base r_wlo r_whi] in Ha. rewrite (base_val_EV _ XR0) in Ha. unfold aSP in Ha. rewrite ESP in Ha. lia.
- right; right. destruct d; cbn [In] in Hr;
repeat (destruct Hr as [<-|Hr]); try (destruct Hr; fail); try destruct Hr;
cbn [reg_act reg_p8 reg_n0 reg_n016 reg_n24 reg_naidx r_base r_wlo r_whi] in Ha; rewrite (base_val_EV _ XR0) in Ha;
unfold aP, aN, aNMEM in Ha; try change (xvA 58) with P in Ha; try change (xvA 59) with N in Ha; lia.
- exfalso. destruct q; cbn [In] in Hr; try (destruct Hr; fail);
repeat (destruct Hr as [<-|Hr]); try destruct Hr; cbn [reg_tq2 reg_bnc reg_usg r_base r_wlo r_whi] in Ha; lia.
Qed.
Lemma frame1A a : 0 <= a < 2 ^ 64 -> ~ in_winA a -> mem1 (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros Ha Hw. unfold mem1. apply (HF1 (Z_to_bv 64 a)). intros Hin. apply Hw. apply wrange_winA. rewrite Z_to_bv_unsigned in Hin.
unfold bv_wrap in Hin. change (bv_modulus 64) with (2 ^ 64) in Hin. rewrite Z.mod_small in Hin by lia. exact Hin.
Qed.
Lemma used_metasX_cons s gm : In gm (used_metasX (g :: X) s) -> In gm (used_metasX X s).
Proof.
unfold used_metasX. intros Hm. apply filter_In in Hm as [Hm Hx]. apply filter_In. split; [exact Hm|].
cbn [fst] in Hx |- *. rewrite memb_cons in Hx. destruct (memb (fst gm) X); [|reflexivity]. rewrite orb_true_r in Hx. discriminate.
Qed.
Lemma imageX_cons s c : In c (imageX (g :: X) s ++ tail_cellsX (g :: X) s) -> In c (imageX X s ++ tail_cellsX X s).
Proof.
intros Hc. apply in_app_iff in Hc as [Hc|Hc]; apply in_app_iff; [left | right].
- unfold imageX in *. rewrite !in_app_iff in Hc |- *. destruct Hc as [Hc|[Hc|Hc]]; [tauto | tauto | right; right].
apply in_flat_map in Hc as (gm & Hgm & Hc). apply in_flat_map. exists gm. split; [apply used_metasX_cons; exact Hgm | exact Hc].
- unfold tail_cellsX in *. apply in_flat_map in Hc as (gm & Hgm & Hc). apply in_flat_map. exists gm. split; [apply used_metasX_cons; exact Hgm | exact Hc].
Qed.
Lemma meta_layer s qq a a' c (NW : list mcell) :
MT s qq = Some (MUsed a) -> grp_same a a' ->
(forall c', In c' (meta_slot_cells qq (Some (MUsed a'))) -> In c' NW \/ In c' (imageX X A ++ tail_cellsX X A)) ->
In c (imageX (g :: X) (upd_meta qq (MUsed a') s) ++ tail_cellsX (g :: X) (upd_meta qq (MUsed a') s)) ->
In c NW \/ In c (imageX X A ++ tail_cellsX X A) \/ In c (imageX (g :: X) s ++ tail_cellsX (g :: X) s).
Proof.
intros Mq GS Hcells Hc. apply in_app_iff in Hc as [Hc|Hc].
- destruct (imageX_upd_meta (g :: X) s qq a a' c Mq GS Hc) as [H1|H1].
+ destruct (Hcells c H1) as [H2|H2]; [left; exact H2 | right; left; exact H2].
+ right; right. apply in_app_iff. left. exact H1.
- right; right. apply in_app_iff. right. eapply tail_cellsX_upd_meta; eauto.
Qed.
Lemma meta_bits_links pr nx a : meta_bits (am_set_links pr nx a) = meta_bits a.
Proof. destruct a; reflexivity. Qed.
Lemma meta_bits_act a : meta_bits (am_act a) = meta_bits a.
Proof. destruct a; reflexivity. Qed.
Lemma meta_bits_strip a : meta_bits (strip a) = meta_bits a.
Proof. destruct a; reflexivity. Qed.
Lemma meta_bits_an2' : meta_bits (an2' n an) = meta_bits an. Proof. destruct an; reflexivity. Qed.
Lemma meta_bits_ap2 : meta_bits (ap2 n ap) = meta_bits ap. Proof. destruct ap; reflexivity. Qed.
Lemma old6 qq a d0 w val : usedX X A qq a -> In (MCell (LMem (padd qq d0)) w val) (meta_slot_cells qq (Some (MUsed a))) ->
In (MCell (LMem (padd qq d0)) w val) (imageX X A ++ tail_cellsX X A).
Proof. intros Uq Hc. exact (old_meta_cellA qq a _ Uq Hc). Qed.
Lemma cellsA1 c : In c (imageX (g :: X) A1s ++ tail_cellsX (g :: X) A1s) -> In c NEW \/ In c (imageX X A ++ tail_cellsX X A).
Proof.
pose proof g_facts as (_&_&_&_&_&_&_&_&_&_&_&_& Hsc). pose proof len_active as LA. pose proof Un as Un0. pose proof Up as Up0.
pose proof n_apart as NA. pose proof p_apart as PA. pose proof DF as DF0. unfold dfacts in DF0.
assert (Mn : MT A n = Some (MUsed an)) by exact (proj1 (usedX_MT _ _ _ _ Un0)).
assert (Mp : MT A p = Some (MUsed ap)) by exact (proj1 (usedX_MT _ _ _ _ Up0)).
assert (OLDg : forall c', In c' (meta_slot_cells g (Some (MUsed am))) -> In c' (imageX X A ++ tail_cellsX X A)) by (intros c' Hc'; exact (old_meta_cellA g am _ Hu Hc')).
assert (OLDn : forall c', In c' (meta_slot_cells n (Some (MUsed an))) -> In c' (imageX X A ++ tail_cellsX X A)) by (intros c' Hc'; exact (old_meta_cellA n an _ Un0 Hc')).
assert (OLDp : forall c', In c' (meta_slot_cells p (Some (MUsed ap))) -> In c' (imageX X A ++ tail_cellsX X A)) by (intros c' Hc'; exact (old_meta_cellA p ap _ Up0 Hc')).
assert (Cg : forall c', In c' (meta_slot_cells g (Some (MUsed (strip am)))) ->
In c' [MCell (LMem (padd g 0)) 8 (VZ 0); MCell (LMem (padd g 8)) 8 (VZ 0)] \/ In c' (imageX X A ++ tail_cellsX X A)).
{ intros c' Hc'. cbn [meta_slot_cells strip am_set_links am_prev am_next am_mem am_avail am_freed optr] in Hc'. rewrite ?meta_bits_strip, ?meta_bits_links in Hc'. unfold META_prev, META_next in Hc'.
destruct Hc' as [<-|[<-|Hc']]; [left; cbn; tauto | left; cbn; tauto | right]. apply OLDg. cbn [meta_slot_cells]. cbn in Hc' |- *. tauto. }
assert (Cn : forall pr c', In c' (meta_slot_cells n (Some (MUsed (am_set_links pr (am_next an) an)))) ->
In c' [MCell (LMem (padd n 0)) 8 (optr pr)] \/ In c' (imageX X A ++ tail_cellsX X A)).
{ intros pr c' Hc'. cbn [meta_slot_cells am_set_links am_prev am_next am_mem am_avail am_freed] in Hc'. rewrite meta_bits_links in Hc'. unfold META_prev in Hc'.
destruct Hc' as [<-|Hc']; [left; cbn; tauto | right]. apply OLDn. cbn [meta_slot_cells]. cbn in Hc' |- *. tauto. }
assert (Cn' : forall c', In c' (meta_slot_cells n (Some (MUsed (an2' n an)))) ->
In c' [MCell (LMem (padd n 0)) 8 (VP n); MCell (LMem (padd n 8)) 8 (VP n)] \/ In c' (imageX X A ++ tail_cellsX X A)).
{ intros c' Hc'. cbn [meta_slot_cells an2' am_set_links am_prev am_next am_mem am_avail am_freed optr] in Hc'. rewrite ?meta_bits_an2', ?meta_bits_links in Hc'. unfold META_prev, META_next in Hc'.
destruct Hc' as [<-|[<-|Hc']]; [left; cbn; tauto | left; cbn; tauto | right]. apply OLDn. cbn [meta_slot_cells]. cbn in Hc' |- *. tauto. }
assert (CactB : forall c', In c' (meta_slot_cells n (Some (MUsed (am_act (an2 p an))))) ->
In c' [MCell (LMem (padd n 0)) 8 (VP p); MCell (LMem (padd n 24)) 4 (VZ navail); MCell (LMem (padd n 28)) 4 (VZ nfreed)] \/
In c' (imageX X A ++ tail_cellsX X A)).
{ intros c' Hc'. unfold navail, nfreed. cbn [meta_slot_cells am_act an2 am_set_avail am_set_freed am_set_links am_prev am_next am_mem am_avail am_freed am_aidx optr] in Hc'.
replace (meta_bits (am_act (an2 p an))) with (meta_bits an) in Hc' by (destruct an; reflexivity). unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hc'.
destruct Hc' as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
- left; cbn; tauto.
- right. apply OLDn. cbn. tauto.
- right. apply OLDn. cbn. tauto.
- left; cbn; tauto.
- left; cbn; tauto.
- right. apply OLDn. cbn. tauto. }
assert (CactB' : forall c', In c' (meta_slot_cells n (Some (MUsed (am_act (an2' n an))))) ->
In c' [MCell (LMem (padd n 0)) 8 (VP n); MCell (LMem (padd n 8)) 8 (VP n); MCell (LMem (padd n 24)) 4 (VZ navail); MCell (LMem (padd n 28)) 4 (VZ nfreed)] \/
In c' (imageX X A ++ tail_cellsX X A)).
{ intros c' Hc'. unfold navail, nfreed. cbn [meta_slot_cells am_act an2' am_set_avail am_set_freed am_set_links am_prev am_next am_mem am_avail am_freed am_aidx optr] in Hc'.
replace (meta_bits (am_act (an2' n an))) with (meta_bits an) in Hc' by (destruct an; reflexivity). unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hc'.
destruct Hc' as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
- left; cbn; tauto.
- left; cbn; tauto.
- right. apply OLDn. cbn. tauto.
- left; cbn; tauto.
- left; cbn; tauto.
- right. apply OLDn. cbn. tauto. }
assert (Cp : forall c', In c' (meta_slot_cells p (Some (MUsed (ap2 n ap)))) ->
In c' [MCell (LMem (padd p 8)) 8 (VP n)] \/ In c' (imageX X A ++ tail_cellsX X A)).
{ intros c' Hc'. cbn [meta_slot_cells ap2 am_set_links am_prev am_next am_mem am_avail am_freed optr] in Hc'. rewrite ?meta_bits_ap2, ?meta_bits_links in Hc'. unfold META_next in Hc'.
destruct Hc' as [Hc'|[<-|Hc']]; [right; apply OLDp; cbn; tauto | left; cbn; tauto | right]. apply OLDp. cbn [meta_slot_cells]. cbn in Hc' |- *. tauto. }
intros Hc. unfold NEW, NEWg, NEWd. unfold A1s, A_D1, A_D2a, A_D2b, A_D2a', A_D2b', A_unl, A_unl' in Hc.
assert (FIN : forall c0, In c0 (imageX (g :: X) A ++ tail_cellsX (g :: X) A) -> In c0 (imageX X A ++ tail_cellsX X A)) by (intros c0; apply imageX_cons).
destruct d; cbn [toMd] in DF0.
- right. apply FIN. exact Hc.
-   change (st_active A) with (st_active (upd_meta g (MUsed (strip am)) A)) in Hc. apply in_app_iff in Hc as [Hc|Hc].
+ destruct (imageX_set_active (g :: X) (upd_meta g (MUsed (strip am)) A) (Z.to_nat (am_sc am)) None c ltac:(cbn [st_active upd_meta set_metas]; rewrite LA; lia) Hc) as [->|Hc1]; [left; apply in_app_iff; right; left; reflexivity|].
destruct (meta_layer A g am (strip am) c _ Mg (grp_same_links _ _ am) Cg ltac:(apply in_app_iff; left; exact Hc1)) as [K|[K|K]];
[left; apply in_app_iff; left; exact K | right; exact K | right; apply FIN; exact K].
+ rewrite tail_cellsX_set_active in Hc.
destruct (meta_layer A g am (strip am) c _ Mg (grp_same_links _ _ am) Cg ltac:(apply in_app_iff; right; exact Hc)) as [K|[K|K]];
[left; apply in_app_iff; left; exact K | right; exact K | right; apply FIN; exact K].
-   destruct NA as [Hng _]. destruct PA as (Hpg & Hpn & _).
destruct (meta_layer _ g am (strip am) c _ ltac:(rewrite (MT_upd_other n) by (intros E; exact (Hng (eq_sym E))); rewrite (MT_upd_other p) by (intros E; exact (Hpg (eq_sym E))); exact Mg) (grp_same_links _ _ am) Cg Hc) as [K|[K|K]];
[left; apply in_app_iff; left; exact K | right; exact K |].
destruct (meta_layer _ n an (an2 p an) c _ ltac:(rewrite (MT_upd_other p) by (intros E; exact (Hpn (eq_sym E))); exact Mn) (grp_same_links _ _ an) (Cn (Some p)) K) as [K2|[K2|K2]];
[left; apply in_app_iff; right; cbn in K2 |- *; tauto | right; exact K2 |].
destruct (meta_layer A p ap (ap2 n ap) c _ Mp (grp_same_links _ _ ap) Cp K2) as [K3|[K3|K3]];
[left; apply in_app_iff; right; cbn in K3 |- *; tauto | right; exact K3 | right; apply FIN; exact K3].
-   destruct NA as [Hng _]. destruct PA as (Hpg & Hpn & _). unfold act_n in Hc.
change (st_active A) with (st_active (upd_meta g (MUsed (strip am)) (upd_meta n (MUsed (am_act (an2 p an))) (upd_meta p (MUsed (ap2 n ap)) A)))) in Hc.
assert (Hc' : In c (imageX (g :: X) (upd_meta g (MUsed (strip am)) (upd_meta n (MUsed (am_act (an2 p an))) (upd_meta p (MUsed (ap2 n ap)) A))) ++
tail_cellsX (g :: X) (upd_meta g (MUsed (strip am)) (upd_meta n (MUsed (am_act (an2 p an))) (upd_meta p (MUsed (ap2 n ap)) A)))) \/ c = act_cell kA (Some n)).
{ apply in_app_iff in Hc as [Hc|Hc].
- destruct (imageX_set_active (g :: X) (upd_meta g (MUsed (strip am)) (upd_meta n (MUsed (am_act (an2 p an))) (upd_meta p (MUsed (ap2 n ap)) A))) (Z.to_nat (am_sc am)) (Some n) c ltac:(cbn [st_active upd_meta set_metas]; rewrite LA; lia) Hc) as [->|Hc1]; [right; reflexivity | left; apply in_app_iff; left; exact Hc1].
- left. apply in_app_iff. right. rewrite tail_cellsX_set_active in Hc. exact Hc. }
destruct Hc' as [Hc'| ->]; [| left; apply in_app_iff; right; left; reflexivity].
destruct (meta_layer _ g am (strip am) c _ ltac:(rewrite (MT_upd_other n) by (intros E; exact (Hng (eq_sym E))); rewrite (MT_upd_other p) by (intros E; exact (Hpg (eq_sym E))); exact Mg) (grp_same_links _ _ am) Cg Hc') as [K|[K|K]];
[left; apply in_app_iff; left; exact K | right; exact K |].
destruct (meta_layer _ n an (am_act (an2 p an)) c _ ltac:(rewrite (MT_upd_other p) by (intros E; exact (Hpn (eq_sym E))); exact Mn)
ltac:(unfold am_act, an2; eapply grp_same_trans; [apply grp_same_links | eapply grp_same_trans; [apply grp_same_freed | apply grp_same_avail]])
CactB K) as [K2|[K2|K2]];
[left; apply in_app_iff; right; cbn in K2 |- *; tauto | right; exact K2 |].
destruct (meta_layer A p ap (ap2 n ap) c _ Mp (grp_same_links _ _ ap) Cp K2) as [K3|[K3|K3]];
[left; apply in_app_iff; right; cbn in K3 |- *; tauto | right; exact K3 | right; apply FIN; exact K3].
-   destruct NA as [Hng _].
destruct (meta_layer _ g am (strip am) c _ ltac:(rewrite (MT_upd_other n) by (intros E; exact (Hng (eq_sym E))); exact Mg) (grp_same_links _ _ am) Cg Hc) as [K|[K|K]];
[left; apply in_app_iff; left; exact K | right; exact K |].
destruct (meta_layer A n an (an2' n an) c _ Mn (grp_same_links _ _ an) Cn' K) as [K2|[K2|K2]];
[left; apply in_app_iff; right; exact K2 | right; exact K2 | right; apply FIN; exact K2].
-   destruct NA as [Hng _]. unfold act_n in Hc.
change (st_active A) with (st_active (upd_meta g (MUsed (strip am)) (upd_meta n (MUsed (am_act (an2' n an))) A))) in Hc.
assert (Hc' : In c (imageX (g :: X) (upd_meta g (MUsed (strip am)) (upd_meta n (MUsed (am_act (an2' n an))) A)) ++
tail_cellsX (g :: X) (upd_meta g (MUsed (strip am)) (upd_meta n (MUsed (am_act (an2' n an))) A))) \/ c = act_cell kA (Some n)).
{ apply in_app_iff in Hc as [Hc|Hc].
- destruct (imageX_set_active (g :: X) (upd_meta g (MUsed (strip am)) (upd_meta n (MUsed (am_act (an2' n an))) A)) (Z.to_nat (am_sc am)) (Some n) c ltac:(cbn [st_active upd_meta set_metas]; rewrite LA; lia) Hc) as [->|Hc1]; [right; reflexivity | left; apply in_app_iff; left; exact Hc1].
- left. apply in_app_iff. right. rewrite tail_cellsX_set_active in Hc. exact Hc. }
destruct Hc' as [Hc'| ->]; [| left; apply in_app_iff; right; left; reflexivity].
destruct (meta_layer _ g am (strip am) c _ ltac:(rewrite (MT_upd_other n) by (intros E; exact (Hng (eq_sym E))); exact Mg) (grp_same_links _ _ am) Cg Hc') as [K|[K|K]];
[left; apply in_app_iff; left; exact K | right; exact K |].
destruct (meta_layer A n an (am_act (an2' n an)) c _ Mn
ltac:(unfold am_act, an2'; eapply grp_same_trans; [apply grp_same_links | eapply grp_same_trans; [apply grp_same_freed | apply grp_same_avail]])
CactB' K) as [K2|[K2|K2]];
[left; apply in_app_iff; right; cbn in K2 |- *; tauto | right; exact K2 | right; apply FIN; exact K2].
Qed.
Lemma sc_d : match d with D0 => True | _ => 0 <= am_sc am < 48 end.
Proof.
pose proof DF as DF0. unfold dfacts in DF0. destruct d; cbn [toMd] in DF0; [exact I | | | | |]; tauto.
Qed.
Lemma new_homeA c : In c NEW -> In c (areas_cells A1s (st_areas A1s)) \/ In c (ctx_cells A1s).
Proof.
pose proof g_facts as (_&_&_&_&_&_&_&_&_&_&_&_& Hsc). pose proof len_active as LA. pose proof A1s_facts as (_ & _ & _ & MG & _).
pose proof n_apart as NA. pose proof p_apart as PA. pose proof sc_d as SD.
intros Hn. unfold NEW in Hn. apply in_app_iff in Hn as [Hn|Hn].
- left. apply (slot_cells_in_areas (g :: X) None U1 A1s HI2 g (MUsed amU) c MG). unfold NEWg, amU in Hn |- *. destruct d; try (destruct Hn; fail);
cbn [meta_slot_cells strip am_set_links am_prev am_next am_mem am_avail am_freed optr]; unfold META_prev, META_next; cbn in Hn |- *; tauto.
- unfold NEWd in Hn. unfold A1s, A_D1, A_D2a, A_D2b, A_D2a', A_D2b', A_unl, A_unl', act_n in *. destruct d; try (destruct Hn; fail).
+ destruct Hn as [<-|[]]. right. change (st_active A) with (st_active (upd_meta g (MUsed (strip am)) A)). apply act_cell_In; [unfold kA; lia | exact LA].
+ destruct NA as [Hng _]. destruct PA as (Hpg & Hpn & _). left. destruct Hn as [<-|[<-|[]]].
* apply (slot_cells_in_areas (g :: X) None U1 _ HI2 n (MUsed (an2 p an))); [rewrite (MT_upd_other g) by exact Hng; apply MT_upd_same | cbn; tauto].
* apply (slot_cells_in_areas (g :: X) None U1 _ HI2 p (MUsed (ap2 n ap))); [rewrite (MT_upd_other g) by exact Hpg; rewrite (MT_upd_other n) by exact Hpn; apply MT_upd_same | cbn; tauto].
+ destruct NA as [Hng _]. destruct PA as (Hpg & Hpn & _). destruct Hn as [<-|[<-|[<-|[<-|[<-|[]]]]]].
* right. change (st_active A) with (st_active (upd_meta g (MUsed (strip am)) (upd_meta n (MUsed (am_act (an2 p an))) (upd_meta p (MUsed (ap2 n ap)) A)))). apply act_cell_In; [unfold kA; lia | exact LA].
* left. apply (slot_cells_in_areas (g :: X) None U1 _ HI2 n (MUsed (am_act (an2 p an)))); [rewrite MT_set_active, (MT_upd_other g) by exact Hng; apply MT_upd_same | unfold navail, nfreed; destruct an; cbn; tauto].
* left. apply (slot_cells_in_areas (g :: X) None U1 _ HI2 p (MUsed (ap2 n ap))); [rewrite MT_set_active, (MT_upd_other g) by exact Hpg; rewrite (MT_upd_other n) by exact Hpn; apply MT_upd_same | cbn; tauto].
* left. apply (slot_cells_in_areas (g :: X) None U1 _ HI2 n (MUsed (am_act (an2 p an)))); [rewrite MT_set_active, (MT_upd_other g) by exact Hng; apply MT_upd_same | unfold navail, nfreed; destruct an; cbn; tauto].
* left. apply (slot_cells_in_areas (g :: X) None U1 _ HI2 n (MUsed (am_act (an2 p an)))); [rewrite MT_set_active, (MT_upd_other g) by exact Hng; apply MT_upd_same | unfold navail, nfreed; destruct an; cbn; tauto].
+ destruct NA as [Hng _]. left. destruct Hn as [<-|[<-|[]]];
(apply (slot_cells_in_areas (g :: X) None U1 _ HI2 n (MUsed (an2' n an))); [rewrite (MT_upd_other g) by exact Hng; apply MT_upd_same | cbn; tauto]).
+ destruct NA as [Hng _]. destruct Hn as [<-|[<-|[<-|[<-|[<-|[]]]]]].
* right. change (st_active A) with (st_active (upd_meta g (MUsed (strip am)) (upd_meta n (MUsed (am_act (an2' n an))) A))). apply act_cell_In; [unfold kA; lia | exact LA].
* left. apply (slot_cells_in_areas (g :: X) None U1 _ HI2 n (MUsed (am_act (an2' n an)))); [rewrite MT_set_active, (MT_upd_other g) by exact Hng; apply MT_upd_same | unfold navail, nfreed; destruct an; cbn; tauto].
* left. apply (slot_cells_in_areas (g :: X) None U1 _ HI2 n (MUsed (am_act (an2' n an)))); [rewrite MT_set_active, (MT_upd_other g) by exact Hng; apply MT_upd_same | unfold navail, nfreed; destruct an; cbn; tauto].
* left. apply (slot_cells_in_areas (g :: X) None U1 _ HI2 n (MUsed (am_act (an2' n an)))); [rewrite MT_set_active, (MT_upd_other g) by exact Hng; apply MT_upd_same | unfold navail, nfreed; destruct an; cbn; tauto].
* left. apply (slot_cells_in_areas (g :: X) None U1 _ HI2 n (MUsed (am_act (an2' n an)))); [rewrite MT_set_active, (MT_upd_other g) by exact Hng; apply MT_upd_same | unfold navail, nfreed; destruct an; cbn; tauto].
Qed.
Lemma U_NACT : bv_unsigned (sv_denot (EV xvA) NACT) = sllw 2 aidxb.
Proof.
facts0. unfold NACT.
change (sv_denot (EV xvA) (SAluw ALU_SLL (SLit 2) (SOff aNAIDX 0))) with
(sext 64 (alu32 ALU_SLL (low32 (sv_denot (EV xvA) (SLit 2))) (low32 (sv_denot (EV xvA) (SOff aNAIDX 0))))).
rewrite sllw_rr_unsigned, (U_off0 _ XR0), U_lit. change (2 mod 2 ^ 64) with 2. unfold aNAIDX, xvA. cbn [Nat.ltb Nat.leb]. reflexivity.
Qed.
Lemma U_NAVAIL : lo32 (bv_unsigned (sv_denot (EV xvA) NAVAIL)) = navail.
Proof.
facts0. pose proof n_facts as (_&_&_&_&_&_&_&_&_&Nfr&Nai&_&Haidx). pose proof (XR0 aNAIDX) as AR.
unfold NAVAIL.
change (sv_denot (EV xvA) (SAlu ALU_AND (SExt true 32 (SOff aNFR 0)) (SAlu ALU_ADD NACT (SLit (-1))))) with
(alu64 ALU_AND (sv_denot (EV xvA) (SExt true 32 (SOff aNFR 0))) (alu64 ALU_ADD (sv_denot (EV xvA) NACT) (sv_denot (EV xvA) (SLit (-1))))).
rewrite alu64_and, alu64_add, U_sext32, (U_off0 _ XR0), U_NACT, U_lit. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
change (xvA aNFR) with (am_freed an).
rewrite (land_mask_ones_lo32 (am_freed an) aidxb Nfr (proj1 (XR0 aNAIDX))). unfold navail. rewrite Haidx. reflexivity.
Qed.
Lemma U_NFREED2 : lo32 (bv_unsigned (sv_denot (EV xvA) NFREED2)) = nfreed.
Proof.
facts0. pose proof n_facts as (_&_&_&_&_&_&_&_&_&Nfr&Nai&_&Haidx). pose proof (XR0 aNAIDX) as AR.
unfold NFREED2.
change (sv_denot (EV xvA) (SAlu ALU_AND (SExt true 32 (SOff aNFR 0)) (SAluw ALU_SUB (SLit 0) NACT))) with
(alu64 ALU_AND (sv_denot (EV xvA) (SExt true 32 (SOff aNFR 0))) (sext 64 (alu32 ALU_SUB (low32 (Z_to_bv 64 0)) (low32 (sv_denot (EV xvA) NACT))))).
rewrite alu64_and, negw_unsigned, U_sext32, (U_off0 _ XR0), U_NACT.
change (xvA aNFR) with (am_freed an).
rewrite (land_negw_sllw2_lo32 (am_freed an) aidxb Nfr (proj1 (XR0 aNAIDX))). unfold nfreed. rewrite Haidx.
rewrite ldiff_as_sub; [reflexivity | lia | unfold ones; pose proof (Z.pow_pos_nonneg 2 (am_aidx an + 1)); lia].
Qed.
Lemma new_memA c : In c NEW -> cell_mem B1 L mem1 c.
Proof.
facts0. pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _ & Hml & Hsc). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof n_facts as (N1 & N2 & _). pose proof p_facts as (P1 & P2 & _).
destruct final_regionsA as (Rg & _ & Rd). pose proof sc_d as SD. pose proof U_NAVAIL as UNA. pose proof U_NFREED2 as UNF.
assert (ACT : forall (e : sv) (v : option sptr), am_sc am < 48 ->
chunk_ok src0segs (EV xvA) mem1 (xvA aACT) (mkChunk 0 (CVal 8 e)) ->
bv_unsigned (sv_denot (EV xvA) e) = optrZ L v mod 2 ^ 64 -> cell_mem B1 L mem1 (act_cell kA v)).
{ intros e v H48 C Hv. destruct (optr_facts L v) as [E1 E2]. unfold act_cell.
eapply (chunk8_cell xvA L mem1 _ 0 e _ _ _ C Hv); [| exact E1 | exact E2].
cbn [loc_addr]. rewrite Hctx. unfold xvA, aACT, kA, CTX_active. cbn [Nat.ltb Nat.leb]. rewrite Z2Nat.id by lia. lia. }
assert (C8 : forall (base : Z) (off : Z) (k : nat) (qq rr : sptr),
chunk_ok src0segs (EV xvA) mem1 base (mkChunk off (CVal 8 (SOff k 0))) -> xvA k = ptr_addr L rr ->
ptr_addr L qq + off = base + off -> cell_mem B1 L mem1 (MCell (LMem (padd qq off)) 8 (VP rr))).
{ intros base off k qq rr C Hk Hb. eapply (chunk8_cell xvA L mem1 base off _ (ptr_addr L rr) _ _ C); [| rewrite loc_addr_padd; exact Hb | reflexivity | exact I].
rewrite (U_off0 _ XR0), Hk. symmetry. apply Z.mod_small. pose proof (XR0 k). lia. }
assert (Z8 : forall off, chunk_ok src0segs (EV xvA) mem1 (xvA aNG) (mkChunk off (CVal 8 (SLit 0))) -> cell_mem B1 L mem1 (MCell (LMem (padd g off)) 8 (VZ 0))).
{ intros off C. eapply (chunk8_cell xvA L mem1 _ off _ 0 _ _ C); [apply U_lit | rewrite loc_addr_padd; unfold aNG; rewrite EG0; reflexivity | reflexivity | exact I]. }
intros Hn. unfold NEW in Hn. apply in_app_iff in Hn as [Hn|Hn].
- unfold NEWg in Hn. destruct Rg as (_ & _ & _ & C). cbn [r_base r_chunks metagA_out] in C. rewrite (base_val_EV _ XR0) in C.
destruct d; try (destruct Hn; fail); apply Forall_cons_iff in C as [Ca C]; apply Forall_cons_iff in C as [Cb _];
(destruct Hn as [<-|[<-|[]]]; [exact (Z8 0 Cb) | exact (Z8 8 Ca)]).
- unfold NEWd in Hn. destruct d; cbn [d_mem_out] in Rd; try (destruct Hn; fail).
+   apply Forall_cons_iff in Rd as [Ra _]. destruct Ra as (_ & _ & _ & C). cbn [r_base r_chunks reg_act] in C. rewrite (base_val_EV _ XR0) in C. apply Forall_cons_iff in C as [C _].
destruct Hn as [<-|[]]. cbn in SD. apply (ACT (SLit 0) None); [exact (proj2 SD) | exact C | rewrite U_lit; reflexivity].
+   apply Forall_cons_iff in Rd as [_ Rd]. apply Forall_cons_iff in Rd as [Rp Rd]. apply Forall_cons_iff in Rd as [Rn _].
destruct Rp as (_ & _ & _ & Cp). cbn [r_base r_chunks] in Cp. rewrite (base_val_EV _ XR0) in Cp. apply Forall_cons_iff in Cp as [Cp _].
destruct Rn as (_ & _ & _ & Cn). cbn [r_base r_chunks] in Cn. rewrite (base_val_EV _ XR0) in Cn. apply Forall_cons_iff in Cn as [Cn _].
destruct Hn as [<-|[<-|[]]]; [exact (C8 _ 0 aP n p Cn eq_refl eq_refl) | exact (C8 _ 8 aN p n Cp eq_refl eq_refl)].
+   apply Forall_cons_iff in Rd as [Ra Rd]. apply Forall_cons_iff in Rd as [Rp Rd]. apply Forall_cons_iff in Rd as [Rn Rd]. apply Forall_cons_iff in Rd as [R24 _].
destruct Ra as (_ & _ & _ & Ca). cbn [r_base r_chunks reg_act] in Ca. rewrite (base_val_EV _ XR0) in Ca. apply Forall_cons_iff in Ca as [Ca _].
destruct Rp as (_ & _ & _ & Cp). cbn [r_base r_chunks] in Cp. rewrite (base_val_EV _ XR0) in Cp. apply Forall_cons_iff in Cp as [Cp _].
destruct Rn as (_ & _ & _ & Cn). cbn [r_base r_chunks] in Cn. rewrite (base_val_EV _ XR0) in Cn. apply Forall_cons_iff in Cn as [Cn _].
destruct R24 as (_ & _ & _ & C24). cbn [r_base r_chunks reg_n24_out] in C24. rewrite (base_val_EV _ XR0) in C24. apply Forall_cons_iff in C24 as [Cav C24]. apply Forall_cons_iff in C24 as [Cfr _].
pose proof SD as Hsc48. cbn in Hsc48.
destruct Hn as [<-|[<-|[<-|[<-|[<-|[]]]]]].
* apply (ACT (SOff aN 0) (Some n)); [lia | exact Ca | rewrite (U_off0 _ XR0); cbn [optrZ]; symmetry; apply Z.mod_small; change (xvA aN) with N; lia].
* exact (C8 _ 0 aP n p Cn eq_refl eq_refl).
* exact (C8 _ 8 aN p n Cp eq_refl eq_refl).
* eapply (chunk4_cell_lo32 xvA L mem1 _ 24 _ _ _ Cav UNA). rewrite loc_addr_padd. reflexivity.
* eapply (chunk4_cell_lo32 xvA L mem1 _ 28 _ _ _ Cfr UNF). rewrite loc_addr_padd. reflexivity.
+   apply Forall_cons_iff in Rd as [_ Rd]. apply Forall_cons_iff in Rd as [Rn _].
destruct Rn as (_ & _ & _ & Cn). cbn [r_base r_chunks] in Cn. rewrite (base_val_EV _ XR0) in Cn. apply Forall_cons_iff in Cn as [Cn0 Cn]. apply Forall_cons_iff in Cn as [Cn8 _].
destruct Hn as [<-|[<-|[]]]; [exact (C8 _ 0 aN n n Cn0 eq_refl eq_refl) | exact (C8 _ 8 aN n n Cn8 eq_refl eq_refl)].
+   apply Forall_cons_iff in Rd as [Ra Rd]. apply Forall_cons_iff in Rd as [Rn Rd]. apply Forall_cons_iff in Rd as [R24 _].
destruct Ra as (_ & _ & _ & Ca). cbn [r_base r_chunks reg_act] in Ca. rewrite (base_val_EV _ XR0) in Ca. apply Forall_cons_iff in Ca as [Ca _].
destruct Rn as (_ & _ & _ & Cn). cbn [r_base r_chunks] in Cn. rewrite (base_val_EV _ XR0) in Cn. apply Forall_cons_iff in Cn as [Cn0 Cn]. apply Forall_cons_iff in Cn as [Cn8 _].
destruct R24 as (_ & _ & _ & C24). cbn [r_base r_chunks reg_n24_out] in C24. rewrite (base_val_EV _ XR0) in C24. apply Forall_cons_iff in C24 as [Cav C24]. apply Forall_cons_iff in C24 as [Cfr _].
pose proof SD as Hsc48. cbn in Hsc48.
destruct Hn as [<-|[<-|[<-|[<-|[<-|[]]]]]].
* apply (ACT (SOff aN 0) (Some n)); [lia | exact Ca | rewrite (U_off0 _ XR0); cbn [optrZ]; symmetry; apply Z.mod_small; change (xvA aN) with N; lia].
* exact (C8 _ 0 aN n n Cn0 eq_refl eq_refl).
* exact (C8 _ 8 aN n n Cn8 eq_refl eq_refl).
* eapply (chunk4_cell_lo32 xvA L mem1 _ 24 _ _ _ Cav UNA). rewrite loc_addr_padd. reflexivity.
* eapply (chunk4_cell_lo32 xvA L mem1 _ 28 _ _ _ Cfr UNF). rewrite loc_addr_padd. reflexivity.
Qed.
Lemma off_img_presentA x o (m : word -> option byte) :
(forall y, x <= y < x + 40 -> ~ in_img B1 y) -> 4096 <= x -> x + 40 <= alloc_ceiling -> 0 <= o < 40 ->
writable_at src0segs m (x + o) -> present m (x + o).
Proof.
pose proof (proj1 alloc_ceiling_val). intros Himg Hx1 Hx2 Ho W. apply writable_off_img_present; [lia | | exact W].
intros I1. apply (Himg (x + o)); [lia|]. apply in_img1_in_img. exact I1.
Qed.
Lemma new_presentA c k : In c NEW -> (k < mc_w c)%nat -> (exists qq, mc_loc c = LMem qq) -> present mem1 (loc_addr L (mc_loc c) + Z.of_nat k).
Proof.
facts0. pose proof g_facts as (Hi & Hlast & Hav & Hfr & Hbits & Hb32 & G1 & G2 & G8 & Gimg & _). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof n_facts as (N1 & N2 & N8 & Nimg & _). pose proof p_facts as (P1 & P2 & P8 & Pimg).
destruct final_regionsA as (Rg & _ & Rd).
assert (PG : forall off, 0 <= off + Z.of_nat k < 16 -> match d with D0 => False | _ => True end -> present mem1 (loc_addr L (LMem (padd g off)) + Z.of_nat k)).
{ intros off Ho Hd. rewrite loc_addr_padd. fold G. replace (G + off + Z.of_nat k) with (G + (off + Z.of_nat k)) by lia.
apply (off_img_presentA G _ mem1 Gimg G1 G2); [lia|].
destruct Rg as (_ & _ & W & _). cbn [r_base r_wlo r_whi metagA_out] in W. rewrite (base_val_EV _ XR0) in W. unfold aNG in W. rewrite EG0 in W. apply W. destruct d; [destruct Hd | | | | |]; lia. }
assert (PN : forall (r : YP09.region) (off lo hi : Z), region_ok src0segs (EV xvA) mem1 r -> r_base r = Some aN -> r_wlo r = lo -> r_whi r = hi -> 0 <= lo -> hi <= 40 ->
lo <= off + Z.of_nat k < hi -> present mem1 (loc_addr L (LMem (padd n off)) + Z.of_nat k)).
{ intros r off lo hi (_ & _ & W & _) Hb Hlo Hhi Hlo0 Hhi40 Ho. rewrite Hb, Hlo, Hhi, (base_val_EV _ XR0) in W. change (xvA aN) with N in W.
rewrite loc_addr_padd. fold N. replace (N + off + Z.of_nat k) with (N + (off + Z.of_nat k)) by lia. apply (off_img_presentA N _ mem1 Nimg N1 N2); [lia|]. apply W. lia. }
assert (PP : forall (r : YP09.region) (off lo hi : Z), region_ok src0segs (EV xvA) mem1 r -> r_base r = Some aP -> r_wlo r = lo -> r_whi r = hi -> 0 <= lo -> hi <= 40 ->
lo <= off + Z.of_nat k < hi -> present mem1 (loc_addr L (LMem (padd p off)) + Z.of_nat k)).
{ intros r off lo hi (_ & _ & W & _) Hb Hlo Hhi Hlo0 Hhi40 Ho. rewrite Hb, Hlo, Hhi, (base_val_EV _ XR0) in W. change (xvA aP) with P in W.
rewrite loc_addr_padd. fold P. replace (P + off + Z.of_nat k) with (P + (off + Z.of_nat k)) by lia. apply (off_img_presentA P _ mem1 Pimg P1 P2); [lia|]. apply W. lia. }
intros Hn Hk [qq Hq]. unfold NEW in Hn. apply in_app_iff in Hn as [Hn|Hn].
- unfold NEWg in Hn. destruct d; try (destruct Hn; fail); (destruct Hn as [<-|[<-|[]]]; cbn [mc_loc mc_w] in Hk |- *; apply PG; [lia | exact I | lia | exact I]).
- unfold NEWd in Hn. destruct d; cbn [d_mem_out] in Rd; try (destruct Hn; fail).
+ destruct Hn as [<-|[]]. cbn in Hq. discriminate.
+ apply Forall_cons_iff in Rd as [_ Rd]. apply Forall_cons_iff in Rd as [Rp Rd]. apply Forall_cons_iff in Rd as [Rn _].
destruct Hn as [<-|[<-|[]]]; cbn [mc_loc mc_w] in Hk |- *; [eapply (PN _ 0 0 8 Rn); try reflexivity; lia | eapply (PP _ 8 8 16 Rp); try reflexivity; lia].
+ apply Forall_cons_iff in Rd as [_ Rd]. apply Forall_cons_iff in Rd as [Rp Rd]. apply Forall_cons_iff in Rd as [Rn Rd]. apply Forall_cons_iff in Rd as [R24 _].
destruct Hn as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [mc_loc mc_w] in Hk |- *;
[cbn in Hq; discriminate | eapply (PN _ 0 0 8 Rn); try reflexivity; lia | eapply (PP _ 8 8 16 Rp); try reflexivity; lia
| eapply (PN _ 24 24 32 R24); try reflexivity; lia | eapply (PN _ 28 24 32 R24); try reflexivity; lia].
+ apply Forall_cons_iff in Rd as [_ Rd]. apply Forall_cons_iff in Rd as [Rn _].
destruct Hn as [<-|[<-|[]]]; cbn [mc_loc mc_w] in Hk |- *; [eapply (PN _ 0 0 16 Rn); try reflexivity; lia | eapply (PN _ 8 0 16 Rn); try reflexivity; lia].
+ apply Forall_cons_iff in Rd as [_ Rd]. apply Forall_cons_iff in Rd as [Rn Rd]. apply Forall_cons_iff in Rd as [R24 _].
destruct Hn as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [mc_loc mc_w] in Hk |- *;
[cbn in Hq; discriminate | eapply (PN _ 0 0 16 Rn); try reflexivity; lia | eapply (PN _ 8 0 16 Rn); try reflexivity; lia
| eapply (PN _ 24 24 32 R24); try reflexivity; lia | eapply (PN _ 28 24 32 R24); try reflexivity; lia].
Qed.
Lemma win_coveredA a :
in_winA a -> (SP0 - 96 <= a < SP0) \/ exists c, In c NEW /\ in_range a (cell_range L c).
Proof.
pose proof sc_d as SD.
assert (NG : forall c, In c NEWg -> In c NEW) by (intros c Hc; unfold NEW; apply in_app_iff; left; exact Hc).
assert (ND : forall c, In c NEWd -> In c NEW) by (intros c Hc; unfold NEW; apply in_app_iff; right; exact Hc).
assert (CM : forall qq off w val, In (MCell (LMem (padd qq off)) w val) NEW -> ptr_addr L qq + off <= a < ptr_addr L qq + off + Z.of_nat w ->
exists c, In c NEW /\ in_range a (cell_range L c)).
{ intros qq off w val Hc Ha. exists (MCell (LMem (padd qq off)) w val). split; [exact Hc|]. unfold in_range, cell_range. cbn [mc_loc mc_w fst snd]. rewrite loc_addr_padd. lia. }
assert (CA : forall v, In (act_cell kA v) NEW -> 0 <= am_sc am < 48 -> xvA aACT <= a < xvA aACT + 8 -> exists c, In c NEW /\ in_range a (cell_range L c)).
{ intros v Hc Hsc Ha. exists (act_cell kA v). split; [exact Hc|]. unfold act_cell, in_range, cell_range. cbn [mc_loc mc_w fst snd loc_addr]. rewrite Hctx.
unfold xvA, aACT in Ha. cbn [Nat.ltb Nat.leb] in Ha. unfold CTX_active, kA. rewrite Z2Nat.id by lia. lia. }
unfold NEWg in NG. unfold NEWd in ND.
intros [W | [W | W]]; [right | left; exact W | right].
- destruct d; [destruct W | | | | |];
(destruct (Z_lt_dec a (G + 8)); [apply (CM g 0 8%nat (VZ 0)); [apply NG; cbn; tauto | unfold G in *; lia] | apply (CM g 8 8%nat (VZ 0)); [apply NG; cbn; tauto | unfold G in *; lia]]).
- cbn in SD. destruct d; try (destruct W; fail).
+ apply (CA None); [apply ND; left; reflexivity | exact SD | exact W].
+ destruct W as [W|W]; [apply (CM p 8 8%nat (VP n)); [apply ND; cbn; tauto | unfold P in *; lia] | apply (CM n 0 8%nat (VP p)); [apply ND; cbn; tauto | unfold N in *; lia]].
+ destruct W as [W|[W|[W|W]]].
* apply (CA (Some n)); [apply ND; left; reflexivity | exact SD | exact W].
* apply (CM p 8 8%nat (VP n)); [apply ND; cbn; tauto | unfold P in *; lia].
* apply (CM n 0 8%nat (VP p)); [apply ND; cbn; tauto | unfold N in *; lia].
* destruct (Z_lt_dec a (N + 28)); [apply (CM n 24 4%nat (VZ navail)); [apply ND; cbn; tauto | unfold N in *; lia] | apply (CM n 28 4%nat (VZ nfreed)); [apply ND; cbn; tauto | unfold N in *; lia]].
+ destruct (Z_lt_dec a (N + 8)); [apply (CM n 0 8%nat (VP n)); [apply ND; cbn; tauto | unfold N in *; lia] | apply (CM n 8 8%nat (VP n)); [apply ND; cbn; tauto | unfold N in *; lia]].
+ destruct W as [W|[W|W]].
* apply (CA (Some n)); [apply ND; left; reflexivity | exact SD | exact W].
* destruct (Z_lt_dec a (N + 8)); [apply (CM n 0 8%nat (VP n)); [apply ND; cbn; tauto | unfold N in *; lia] | apply (CM n 8 8%nat (VP n)); [apply ND; cbn; tauto | unfold N in *; lia]].
* destruct (Z_lt_dec a (N + 28)); [apply (CM n 24 4%nat (VZ navail)); [apply ND; cbn; tauto | unfold N in *; lia] | apply (CM n 28 4%nat (VZ nfreed)); [apply ND; cbn; tauto | unfold N in *; lia]].
Qed.
Lemma win_ownedA a : in_winA a -> (SP0 - 96 <= a < SP0) \/ alloc_owned L A a.
Proof.
pose proof sc_d as SD. pose proof HL as HL0. pose proof Mg as Mg0.
pose proof (proj1 (usedX_MT _ _ _ _ Un)) as Mn. pose proof (proj1 (usedX_MT _ _ _ _ Up)) as Mp.
assert (OG : G <= a < G + 16 -> alloc_owned L A a) by (intros W; apply (meta_bytes_owned X (Some (g, i)) U A L HI HL0 g _ (MUsed am) Mg0); unfold META_SIZE; unfold G in W; lia).
assert (ON : N <= a < N + 32 -> alloc_owned L A a) by (intros W; apply (meta_bytes_owned X (Some (g, i)) U A L HI HL0 n _ (MUsed an) Mn); unfold META_SIZE; unfold N in W; lia).
assert (OP : P + 8 <= a < P + 16 -> alloc_owned L A a) by (intros W; apply (meta_bytes_owned X (Some (g, i)) U A L HI HL0 p _ (MUsed ap) Mp); unfold META_SIZE; unfold P in W; lia).
assert (OA : 0 <= am_sc am < 48 -> xvA aACT <= a < xvA aACT + 8 -> alloc_owned L A a).
{ intros Hsc W. apply (ctx_bytes_owned X (Some (g, i)) U A L HI HL0). rewrite Hctx. unfold xvA, aACT in W. cbn [Nat.ltb Nat.leb] in W. unfold CTX_SIZE. lia. }
cbn in SD. intros [W | [W | W]]; [right | left; exact W | right].
- destruct d; [destruct W | | | | |]; exact (OG W).
- destruct d; [destruct W | apply (OA SD W) | | | |].
+ destruct W as [W|W]; [exact (OP W) | apply ON; lia].
+ destruct W as [W|[W|[W|W]]]; [exact (OA SD W) | exact (OP W) | apply ON; lia | apply ON; lia].
+ apply ON; lia.
+ destruct W as [W|[W|W]]; [exact (OA SD W) | apply ON; lia | apply ON; lia].
Qed.
Lemma in_winA_dec a : in_winA a \/ ~ in_winA a.
Proof.
unfold in_winA. destruct d;
repeat match goal with |- context [?x <= a < ?y] =>
lazymatch goal with
| H : (x <= a < y) \/ ~ (x <= a < y) |- _ => fail
| _ => assert ((x <= a < y) \/ ~ (x <= a < y)) by lia
end end; tauto.
Qed.
Theorem memrep1A : memrepX B1 (g :: X) L A1s mem1.
Proof.
pose proof sp_facts as (S16 & Sceil & S63 & _). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof A1s_facts as (Efp & Erg & _).
refine (memrepX_after B1 X (g :: X) (Some (g, i)) None U U1 A A1s L mem mem1 NEW [] (SP0 - 96, 96) HI HI2 HL Efp Erg MR cellsA1 new_homeA new_memA new_presentA _ _ _ _).
- intros dd c [].
- intros dd a [].
- intros e He. cbn [fst]. pose proof (footprint_hiA e He). lia.
- intros a Ha Hno _ Hns.
assert (NW : ~ in_winA a).
{ intros W. destruct (win_coveredA a W) as [S | (c & Hc & Hin)]; [apply Hns; unfold in_range; cbn [fst snd]; lia | exact (Hno c Hc Hin)]. }
pose proof (frame1A a Ha NW) as E. split; [exact (proj1 (same_byte_views mem mem1 a E))|].
intros [b Hb]. exists b. rewrite E. exact Hb.
Qed.
Lemma outside_winA x : 0x10000 <= x < 0x51000 -> ~ (CTX + 80 <= x < CTX + 80 + 8 * 48) -> ~ in_winA x.
Proof.
pose proof g_facts as (_&_&_&_&_&_& G1 & G2 & G8 & Gimg & _ & _ & Hsc). pose proof (proj1 alloc_ceiling_val) as HCV. pose proof sp_facts as (S16 & Sceil & S63 & _).
pose proof n_facts as (N1 & N2 & N8 & Nimg & _). pose proof p_facts as (P1 & P2 & P8 & Pimg).
pose proof (off_img G Gimg) as GI. pose proof (off_img N Nimg) as NI. pose proof (off_img P Pimg) as PI.
pose proof sc_d as SD. intros Hx Hact [W|[W|W]]; [destruct d; lia | lia |].
unfold xvA, aACT in W. cbn [Nat.ltb Nat.leb] in W. destruct d; cbn in SD; lia.
Qed.
Lemma statics1A : statics_ok B1 mem1.
Proof.
pose proof ST as ST0.
apply (statics_ok_ext B1 mem mem1 ST0). intros x Hs.
enough (NW : ~ in_winA x) by exact (proj1 (same_byte_views mem mem1 x (frame1A x ltac:(unfold static_owned in Hs; cbn -[Z.le Z.lt Z.add] in Hs; unfold src0_D_malloc_lock, src0_D_libc, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_debruijn32, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab in Hs; lia) NW))).
apply outside_winA; unfold static_owned in Hs; cbn [ms_lock ms_libc ms_got_guard ms_guard ms_debruijn ms_size_classes ms_small_cnt ms_med_cnt B1 src0_msyms] in Hs;
unfold src0_D_malloc_lock, src0_D_libc, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_debruijn32, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab in Hs;
unfold CTX, src0_D_malloc_context; lia.
Qed.
Lemma guard1A : word_mem src0segs mem1 GUARD gv.
Proof.
intros k Hk. rewrite <- (Hgv k Hk). apply (proj1 (same_byte_views mem mem1 (GUARD + Z.of_nat k) (frame1A (GUARD + Z.of_nat k) ltac:(unfold GUARD, src0_D_stack_chk_guard; lia) ltac:(apply outside_winA; unfold GUARD, src0_D_stack_chk_guard, CTX, src0_D_malloc_context; lia)))).
Qed.
Lemma ledger1A : ledger_ok B1 L A1s md.
Proof.
pose proof LG as LG0. unfold A1s, A_D1, A_D2a, A_D2b, A_D2a', A_D2b', A_unl, A_unl'. destruct d; split; apply LG0.
Qed.
Theorem A1_post : ntmid (g :: X) fuel L A A1s g regs regs1 mem mem1 md gv.
Proof.
pose proof NPRE as (_ & _ & _ & Hsec & _ & _ & _ & Hh & Hlz & Hmat & _ & _ & Hret & Hal & Hceil & H63 & Hstk & Htp).
pose proof sp_facts as (S16 & Sceil & S63 & WSTK). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof g_facts as (_&_&_&_&_&_& G1 & G2 & _ & _ & _ & _ & Hsc). pose proof n_facts as (N1 & N2 & _). pose proof p_facts as (P1 & P2 & _).
destruct post_regsA as (R10 & R9 & R18 & R2 & RK). pose proof frameA as (F48 & F40 & F32 & F24 & F16 & F8 & FW).
pose proof A1s_facts as (Efp & Erg & _).
split.
- exact SO.
- exact (layout_ok_s' A A1s L HL Efp Erg).
- exact Hctx.
- exact Hsec.
- exact memrep1A.
- exact statics1A.
- exact ledger1A.
- exact (conj Hh (conj Hlz Hmat)).
- exact R10.
- exact R9.
- exact R18.
- exact R2.
- intros r Hr. apply RK. cbn in Hr |- *. tauto.
- exact (conj F48 (conj F40 (conj F32 (conj F24 (conj F16 F8))))).
- exact guard1A.
- exact Hret.
- exact Htp.
- unfold NT_FRAME. fold SP0. split; [exact S16 | split; [lia | exact S63]].
- unfold NT_FRAME. fold SP0. intros a Ha. destruct (Z_le_dec (SP0 - 96) a) as [L1|L1]; [apply FW; lia|].
assert (NW : ~ in_winA a).
{ pose proof sc_d as SD. intros [W|[W|W]]; [destruct d; lia | lia |]. unfold xvA, aACT in W. cbn [Nat.ltb Nat.leb] in W. unfold CTX, src0_D_malloc_context in W. destruct d; cbn in SD; lia. }
apply (writable_same mem mem1 a (frame1A a ltac:(lia) NW)). apply WSTK. lia.
- unfold NT_FRAME. fold SP0. intros a Ha NO NS. apply (frame1A a Ha). intros W. destruct (win_ownedA a W) as [W'|W']; [apply NS; lia | exact (NO W')].
Qed.
End u.
End t.
End f.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
