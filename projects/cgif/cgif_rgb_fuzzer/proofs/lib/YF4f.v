(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0h YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF3v YF3w YF3x YF41 YF47 YF4b YF4c YF4d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Definition runtoD {imgk : img} (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN_sh tfxsegs tfxtbl_rtD FUEL pc ss).
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma word_of_bytes {imgk : img} : forall (m : word -> option byte) a,
(forall k, (k < 8)%nat -> exists b, mbyte tfxsegs m (a + Z.of_nat k) = Some b) -> exists w, val_mem tfxsegs m a 8 w.
Proof.
intros m a BY.
destruct (BY 0%nat ltac:(img_lia)) as [b0 B0]. destruct (BY 1%nat ltac:(img_lia)) as [b1 B1]. destruct (BY 2%nat ltac:(img_lia)) as [b2 B2]. destruct (BY 3%nat ltac:(img_lia)) as [b3 B3].
destruct (BY 4%nat ltac:(img_lia)) as [b4 B4]. destruct (BY 5%nat ltac:(img_lia)) as [b5 B5]. destruct (BY 6%nat ltac:(img_lia)) as [b6 B6]. destruct (BY 7%nat ltac:(img_lia)) as [b7 B7].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
pose proof (bv_unsigned_in_range 8 b4) as R4. pose proof (bv_unsigned_in_range 8 b5) as R5. pose proof (bv_unsigned_in_range 8 b6) as R6. pose proof (bv_unsigned_in_range 8 b7) as R7.
change (bv_modulus 8) with 256 in R0, R1, R2, R3, R4, R5, R6, R7.
exists (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))).
assert (LB : forall (z q b : Z) (k : nat) r, (k < 8)%nat -> 0 <= b < 256 -> 0 <= q -> 0 <= r < 2 ^ (8 * Z.of_nat k) ->
z = 2 ^ (8 * Z.of_nat k) * (b + 256 * q) + r -> z < 2 ^ 64 -> YP0g.le_byte z 8 k = b).
{ clear. intros z q b k r Hk Hb Hq Hr Hz Hz64. unfold YP0g.le_byte. rewrite Z.shiftr_div_pow2 by img_lia.
rewrite (Z.mod_small z) by (img_try (img_change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); img_lia)).
rewrite <- (Z.div_unique z (2 ^ (8 * Z.of_nat k)) (b + 256 * q) r ltac:(img_try (left; img_exact Hr)) Hz).
symmetry. img_apply (Z.mod_unique _ 256 q b); img_lia. }
match goal with |- val_mem _ _ _ _ ?w => set (WW := w) end.
assert (GOAL : forall (bk : byte) kk, mbyte tfxsegs m (a + Z.of_nat kk) = Some bk -> YP0g.le_byte WW 8 kk = bv_unsigned bk ->
mbyte tfxsegs m (a + Z.of_nat kk) = Some (Z_to_bv 8 (YP0g.le_byte WW 8 kk))).
{ intros bk kk Hm Hl. rewrite Hm, Hl, Z_to_bv_bv_unsigned. img_refl. }
intros k Hk.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [..|img_lia];
[ img_try (img_apply (GOAL b0 0%nat B0)) | img_try (img_apply (GOAL b1 1%nat B1)) | img_try (img_apply (GOAL b2 2%nat B2)) | img_try (img_apply (GOAL b3 3%nat B3))
| img_try (img_apply (GOAL b4 4%nat B4)) | img_try (img_apply (GOAL b5 5%nat B5)) | img_try (img_apply (GOAL b6 6%nat B6)) | img_try (img_apply (GOAL b7 7%nat B7)) ]; (subst WW; cbv beta).
- apply (LB _ ((bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))) _ 0%nat (0)); [img_lia | img_lia | img_lia | img_try (img_change (2 ^ (8 * Z.of_nat 0)) with 1; img_lia) | img_try (img_change (2 ^ (8 * Z.of_nat 0)) with 1; img_lia) | img_lia].
- apply (LB _ ((bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))))) _ 1%nat (bv_unsigned b0)); [img_lia | img_lia | img_lia | img_try (img_change (2 ^ (8 * Z.of_nat 1)) with 256; img_lia) | img_try (img_change (2 ^ (8 * Z.of_nat 1)) with 256; img_lia) | img_lia].
- apply (LB _ ((bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))) _ 2%nat ((bv_unsigned b0 + 256 * bv_unsigned b1))); [img_lia | img_lia | img_lia | img_try (img_change (2 ^ (8 * Z.of_nat 2)) with 65536; img_lia) | img_try (img_change (2 ^ (8 * Z.of_nat 2)) with 65536; img_lia) | img_lia].
- apply (LB _ ((bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))) _ 3%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * bv_unsigned b2)))); [img_lia | img_lia | img_lia | img_try (img_change (2 ^ (8 * Z.of_nat 3)) with 16777216; img_lia) | img_try (img_change (2 ^ (8 * Z.of_nat 3)) with 16777216; img_lia) | img_lia].
- apply (LB _ ((bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))) _ 4%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))))); [img_lia | img_lia | img_lia | img_try (img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296; img_lia) | img_try (img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296; img_lia) | img_lia].
- apply (LB _ ((bv_unsigned b6 + 256 * bv_unsigned b7)) _ 5%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * bv_unsigned b4)))))); [img_lia | img_lia | img_lia | img_try (img_change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; img_lia) | img_try (img_change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; img_lia) | img_lia].
- apply (LB _ (bv_unsigned b7) _ 6%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * bv_unsigned b5))))))); [img_lia | img_lia | img_lia | img_try (img_change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; img_lia) | img_try (img_change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; img_lia) | img_lia].
- apply (LB _ (0) _ 7%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * bv_unsigned b6)))))))); [img_lia | img_lia | img_lia | img_try (img_change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; img_lia) | img_try (img_change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; img_lia) | img_lia].
Qed.
Lemma img_word {imgk : img} : forall (Hh : word -> bool) (m : word -> option byte) a bs,
img_bytes tfxsegs a 8 = Some bs -> exists w, val_mem tfxsegs (mrestrict Hh m) a 8 w.
Proof.
intros Hh m a bs Hb. img_apply word_of_bytes. intros k Hk. destruct (img_bytes_spec tfxsegs a 8 bs Hb) as [Hlen Hi].
unfold mbyte. destruct (mrestrict Hh m (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; [img_try (exists b; img_refl)|].
img_change (seg_rom tfxsegs (Z_to_bv 64 (a + Z.of_nat k))) with (img_byte tfxsegs (a + Z.of_nat k)). rewrite (Hi k Hk).
destruct (nth_error bs k) as [b|] eqn:E; [img_try (exists b; img_refl)|]. exfalso. apply nth_error_None in E. img_lia.
Qed.
End e.
Lemma pat_bytes {imgk : img} : exists bs, YQ0b.img_bytes tfxsegs (0x103e0 + D_20) 8 = Some bs.
Proof. img_eexists_vm. Qed.
Definition aPAT : nat := 130.
Definition aDIG : nat := 131.
Definition R_fmt {imgk : img} : YQ0b.region :=
YQ0b.mkRegion None (0x1cdaf + D_m9) ((0x1cdaf + D_m9) + 21) 0 0
[YQ0b.mkChunk (0x1cdaf + D_m9) (CVal 8 (SLit 0x612079726f6d656d)); YQ0b.mkChunk (0x1cdb7 + D_m9) (CVal 8 (SLit 0x7365726464612074));
YQ0b.mkChunk (0x1cdbf + D_m9) (CVal 4 (SLit 0x70252073)); YQ0b.mkChunk (0x1cdc3 + D_m9) (CVal 1 (SLit 0))].
Definition R_jt {imgk : img} : YQ0b.region := lit4 (0x20c3c + D_m8) (0x469b0 + D_2cc).
Definition R_pat {imgk : img} : YQ0b.region := atom8 (0x103e0 + D_20) aPAT.
Definition R_gate1 {imgk : img} : YQ0b.region := lit8 (0xa21a0 + D_10f0) 1.
Definition R_gate2 {imgk : img} : YQ0b.region := lit4 (0x13bcdc + D_10c0) 0.
Definition D_0 {imgk : img} : sstate := resume S_V (SLit ENOMEM_RETv) (ss_mem S_V) (ss_facts S_V).
Definition D_1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (addreg R_gate2 (addreg R_gate1 (addreg R_pat (addreg R_jt (addreg R_fmt D_0))))) 18%bv (SOff aQS 0)))).
Definition dia_lhs (ss : sstate) : sv := sr_get (ss_regs ss) 17%bv.
Definition djoin {imgk : img} (tk : bool) (k : nat) (ss : sstate) : sstate :=
noconds (forget (fst (sym_run_toN_sh tfxsegs tfxtbl_rtD FUEL (0x67d88 + D_2c4) (arm BC_GEU tk (dia_lhs ss) (SLit 10) ss))) k [16%bv]).
Definition tighten (n : nat) (f : afact) (ss : sstate) : sstate :=
mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss) (ss_resv ss) (mkFacts ((n, f) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss))).
Definition hexfact (d : Z) : afact := mkAF (16 ^ (d - 1)) (16 ^ d - 8) 3.
Definition zmatch (b : option nat) (lo n : Z) (r : YQ0b.region) : bool :=
YQ0b.obase_eqb (YQ0b.r_base r) b && (YQ0b.r_lo r <=? lo) && (lo + n <=? YQ0b.r_hi r) && (0 <=? n).
Definition addzero_r (b : option nat) (lo n : Z) (r : YQ0b.region) : YQ0b.region :=
if zmatch b lo n r then YQ0b.mkRegion (YQ0b.r_base r) (YQ0b.r_lo r) (YQ0b.r_hi r) (YQ0b.r_wlo r) (YQ0b.r_whi r) (YQ0b.mkChunk lo (CZero n) :: YQ0b.r_chunks r)
else r.
Definition addzero (b : option nat) (lo n : Z) (ss : sstate) : sstate :=
mkSS (ss_pc ss) (ss_regs ss) (map (addzero_r b lo n) (ss_mem ss)) (ss_resv ss) (ss_facts ss).
Definition zbyte_chunk (off : Z) (c : YQ0b.chunk) : bool :=
(YQ0b.c_off c =? off) && match YQ0b.c_val c with CVal w v => ((w =? 1)%N && sv_eqb v (SLit 0))%bool | _ => false end.
Definition zbytes_ok (lo n : Z) (cs : list YQ0b.chunk) : bool :=
forallb (fun i => existsb (zbyte_chunk (lo + Z.of_nat i)) cs) (seq 0 (Z.to_nat n)).
Definition addzero_ok (b : option nat) (lo n : Z) (ss : sstate) : bool :=
forallb (fun r => negb (zmatch b lo n r) || zbytes_ok lo n (YQ0b.r_chunks r)) (ss_mem ss).
Definition D_1_6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (tighten aQS (hexfact 6) D_1))).
Definition D_M6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x6448c + D_2c4) D_1_6))).
Definition MS_AL6 {imgk : img} : sv := ltac:(img_eval_last (fun imgk : img => (sr_get (ss_regs D_M6) 13%bv))).
Definition D_X6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x64490 + D_2c4) (arm BC_EQ false MS_AL6 (SLit 0) D_M6)))).
Definition D_P6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x6448c + D_2c4) D_X6))).
Definition MS_PAD6 {imgk : img} : sv := ltac:(img_eval_last (fun imgk : img => (sr_get (ss_regs D_P6) 13%bv))).
Definition D_R6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67ca4 + D_2c4) (arm BC_EQ false MS_PAD6 (SLit 0) D_P6)))).
Definition D_Z6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (addzero (Some 2%nat) (-2984) 48 D_R6))).
Definition DG6r {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) D_Z6))).
Definition DG6_0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds DG6r))).
Definition DJ6_0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 0) DG6_0))).
Definition DG6_1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ6_0))).
Definition DJ6_1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 1) DG6_1))).
Definition DG6_2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ6_1))).
Definition DJ6_2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 2) DG6_2))).
Definition DG6_3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ6_2))).
Definition DJ6_3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 3) DG6_3))).
Definition DG6_4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ6_3))).
Definition DJ6_4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 4) DG6_4))).
Definition DG6_5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ6_4))).
Definition DJ6_5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 5) DG6_5))).
Definition D_END6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x60500 + D_2c4) DJ6_5))).
Definition D_1_7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (tighten aQS (hexfact 7) D_1))).
Definition D_M7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x6448c + D_2c4) D_1_7))).
Definition MS_AL7 {imgk : img} : sv := ltac:(img_eval_last (fun imgk : img => (sr_get (ss_regs D_M7) 13%bv))).
Definition D_X7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x64490 + D_2c4) (arm BC_EQ false MS_AL7 (SLit 0) D_M7)))).
Definition D_P7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x6448c + D_2c4) D_X7))).
Definition MS_PAD7 {imgk : img} : sv := ltac:(img_eval_last (fun imgk : img => (sr_get (ss_regs D_P7) 13%bv))).
Definition D_R7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67ca4 + D_2c4) (arm BC_EQ false MS_PAD7 (SLit 0) D_P7)))).
Definition D_Z7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (addzero (Some 2%nat) (-2976) 40 D_R7))).
Definition DG7r {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) D_Z7))).
Definition DG7_0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds DG7r))).
Definition DJ7_0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 0) DG7_0))).
Definition DG7_1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ7_0))).
Definition DJ7_1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 1) DG7_1))).
Definition DG7_2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ7_1))).
Definition DJ7_2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 2) DG7_2))).
Definition DG7_3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ7_2))).
Definition DJ7_3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 3) DG7_3))).
Definition DG7_4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ7_3))).
Definition DJ7_4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 4) DG7_4))).
Definition DG7_5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ7_4))).
Definition DJ7_5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 5) DG7_5))).
Definition DG7_6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ7_5))).
Definition DJ7_6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 6) DG7_6))).
Definition D_END7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x60500 + D_2c4) DJ7_6))).
Definition D_1_8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (tighten aQS (hexfact 8) D_1))).
Definition D_M8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x6448c + D_2c4) D_1_8))).
Definition MS_AL8 {imgk : img} : sv := ltac:(img_eval_last (fun imgk : img => (sr_get (ss_regs D_M8) 13%bv))).
Definition D_X8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x64490 + D_2c4) (arm BC_EQ false MS_AL8 (SLit 0) D_M8)))).
Definition D_P8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x6448c + D_2c4) D_X8))).
Definition MS_PAD8 {imgk : img} : sv := ltac:(img_eval_last (fun imgk : img => (sr_get (ss_regs D_P8) 13%bv))).
Definition D_R8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67ca4 + D_2c4) (arm BC_EQ false MS_PAD8 (SLit 0) D_P8)))).
Definition D_Z8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (addzero (Some 2%nat) (-2968) 32 D_R8))).
Definition DG8r {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) D_Z8))).
Definition DG8_0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds DG8r))).
Definition DJ8_0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 0) DG8_0))).
Definition DG8_1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ8_0))).
Definition DJ8_1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 1) DG8_1))).
Definition DG8_2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ8_1))).
Definition DJ8_2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 2) DG8_2))).
Definition DG8_3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ8_2))).
Definition DJ8_3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 3) DG8_3))).
Definition DG8_4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ8_3))).
Definition DJ8_4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 4) DG8_4))).
Definition DG8_5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ8_4))).
Definition DJ8_5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 5) DG8_5))).
Definition DG8_6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ8_5))).
Definition DJ8_6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 6) DG8_6))).
Definition DG8_7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ8_6))).
Definition DJ8_7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 7) DG8_7))).
Definition D_END8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x60500 + D_2c4) DJ8_7))).
Definition D_1_12 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (tighten aQS (hexfact 12) D_1))).
Definition D_M12 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x6448c + D_2c4) D_1_12))).
Definition MS_AL12 {imgk : img} : sv := ltac:(img_eval_last (fun imgk : img => (sr_get (ss_regs D_M12) 13%bv))).
Definition DG12r {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) (arm BC_EQ false MS_AL12 (SLit 0) D_M12)))).
Definition DG12_0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds DG12r))).
Definition DJ12_0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 0) DG12_0))).
Definition DG12_1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ12_0))).
Definition DJ12_1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 1) DG12_1))).
Definition DG12_2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ12_1))).
Definition DJ12_2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 2) DG12_2))).
Definition DG12_3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ12_2))).
Definition DJ12_3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 3) DG12_3))).
Definition DG12_4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ12_3))).
Definition DJ12_4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 4) DG12_4))).
Definition DG12_5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ12_4))).
Definition DJ12_5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 5) DG12_5))).
Definition DG12_6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ12_5))).
Definition DJ12_6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 6) DG12_6))).
Definition DG12_7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ12_6))).
Definition DJ12_7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 7) DG12_7))).
Definition DG12_8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ12_7))).
Definition DJ12_8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 8) DG12_8))).
Definition DG12_9 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ12_8))).
Definition DJ12_9 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 9) DG12_9))).
Definition DG12_10 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ12_9))).
Definition DJ12_10 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 10) DG12_10))).
Definition DG12_11 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x67db0 + D_2c4) DJ12_10))).
Definition DJ12_11 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (djoin true (aDIG + 11) DG12_11))).
Definition D_END12 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x60500 + D_2c4) DJ12_11))).






