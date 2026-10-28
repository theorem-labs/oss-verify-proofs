(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0f YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0m AF0x AFl0 AFhy AFhz AFi0 AFi4 AFi9 AFid AFie AFif.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Definition runtoD (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN_sh tfibsegs tfibtbl_rtD FUEL pc ss).
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma word_of_bytes : forall (m : word -> option byte) a,
(forall k, (k < 8)%nat -> exists b, mbyte tfibsegs m (a + Z.of_nat k) = Some b) -> exists w, val_mem tfibsegs m a 8 w.
Proof.
intros m a BY.
destruct (BY 0%nat ltac:(lia)) as [b0 B0]. destruct (BY 1%nat ltac:(lia)) as [b1 B1]. destruct (BY 2%nat ltac:(lia)) as [b2 B2]. destruct (BY 3%nat ltac:(lia)) as [b3 B3].
destruct (BY 4%nat ltac:(lia)) as [b4 B4]. destruct (BY 5%nat ltac:(lia)) as [b5 B5]. destruct (BY 6%nat ltac:(lia)) as [b6 B6]. destruct (BY 7%nat ltac:(lia)) as [b7 B7].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
pose proof (bv_unsigned_in_range 8 b4) as R4. pose proof (bv_unsigned_in_range 8 b5) as R5. pose proof (bv_unsigned_in_range 8 b6) as R6. pose proof (bv_unsigned_in_range 8 b7) as R7.
change (bv_modulus 8) with 256 in R0, R1, R2, R3, R4, R5, R6, R7.
exists (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))).
assert (LB : forall (z q b : Z) (k : nat) r, (k < 8)%nat -> 0 <= b < 256 -> 0 <= q -> 0 <= r < 2 ^ (8 * Z.of_nat k) ->
z = 2 ^ (8 * Z.of_nat k) * (b + 256 * q) + r -> z < 2 ^ 64 -> YO0f.le_byte z 8 k = b).
{ clear. intros z q b k r Hk Hb Hq Hr Hz Hz64. unfold YO0f.le_byte. rewrite Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small z) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia).
rewrite <- (Z.div_unique z (2 ^ (8 * Z.of_nat k)) (b + 256 * q) r ltac:(left; exact Hr) Hz).
symmetry. apply (Z.mod_unique _ 256 q b); lia. }
match goal with |- val_mem _ _ _ _ ?w => set (WW := w) end.
assert (GOAL : forall (bk : byte) kk, mbyte tfibsegs m (a + Z.of_nat kk) = Some bk -> YO0f.le_byte WW 8 kk = bv_unsigned bk ->
mbyte tfibsegs m (a + Z.of_nat kk) = Some (Z_to_bv 8 (YO0f.le_byte WW 8 kk))).
{ intros bk kk Hm Hl. rewrite Hm, Hl, Z_to_bv_bv_unsigned. reflexivity. }
intros k Hk.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [..|lia];
[ apply (GOAL b0 0%nat B0) | apply (GOAL b1 1%nat B1) | apply (GOAL b2 2%nat B2) | apply (GOAL b3 3%nat B3)
| apply (GOAL b4 4%nat B4) | apply (GOAL b5 5%nat B5) | apply (GOAL b6 6%nat B6) | apply (GOAL b7 7%nat B7) ]; subst WW.
- apply (LB _ ((bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))) _ 0%nat (0)); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 0)) with 1; lia | change (2 ^ (8 * Z.of_nat 0)) with 1; lia | lia].
- apply (LB _ ((bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))))) _ 1%nat (bv_unsigned b0)); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 1)) with 256; lia | change (2 ^ (8 * Z.of_nat 1)) with 256; lia | lia].
- apply (LB _ ((bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))) _ 2%nat ((bv_unsigned b0 + 256 * bv_unsigned b1))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 2)) with 65536; lia | change (2 ^ (8 * Z.of_nat 2)) with 65536; lia | lia].
- apply (LB _ ((bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))) _ 3%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * bv_unsigned b2)))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 3)) with 16777216; lia | change (2 ^ (8 * Z.of_nat 3)) with 16777216; lia | lia].
- apply (LB _ ((bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))) _ 4%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia | lia].
- apply (LB _ ((bv_unsigned b6 + 256 * bv_unsigned b7)) _ 5%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * bv_unsigned b4)))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; lia | change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; lia | lia].
- apply (LB _ (bv_unsigned b7) _ 6%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * bv_unsigned b5))))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; lia | change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; lia | lia].
- apply (LB _ (0) _ 7%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * bv_unsigned b6)))))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; lia | change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; lia | lia].
Qed.
Lemma img_word : forall (Hh : word -> bool) (m : word -> option byte) a bs,
img_bytes tfibsegs a 8 = Some bs -> exists w, val_mem tfibsegs (mrestrict Hh m) a 8 w.
Proof.
intros Hh m a bs Hb. apply word_of_bytes. intros k Hk. destruct (img_bytes_spec tfibsegs a 8 bs Hb) as [Hlen Hi].
unfold mbyte. destruct (mrestrict Hh m (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; [exists b; reflexivity|].
change (seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k))) with (img_byte tfibsegs (a + Z.of_nat k)). rewrite (Hi k Hk).
destruct (nth_error bs k) as [b|] eqn:E; [exists b; reflexivity|]. exfalso. apply nth_error_None in E. lia.
Qed.
End e.
Lemma pat_bytes : exists bs, YP09.img_bytes tfibsegs 0x103d8 8 = Some bs.
Proof. eexists. vm_compute. reflexivity. Qed.
Definition aPAT : nat := 130.
Definition aDIG : nat := 131.
Definition R_fmt : YP09.region :=
YP09.mkRegion None 0x1cd09 (0x1cd09 + 21) 0 0
[YP09.mkChunk 0x1cd09 (CVal 8 (SLit 0x612079726f6d656d)); YP09.mkChunk 0x1cd11 (CVal 8 (SLit 0x7365726464612074));
YP09.mkChunk 0x1cd19 (CVal 4 (SLit 0x70252073)); YP09.mkChunk 0x1cd1d (CVal 1 (SLit 0))].
Definition R_jt : YP09.region := lit4 0x20b7c 0x45f54.
Definition R_pat : YP09.region := atom8 0x103d8 aPAT.
Definition R_gate1 : YP09.region := lit8 0x9dfd8 1.
Definition R_gate2 : YP09.region := lit4 0x137b1c 0.
Definition D_0 : sstate := resume S_V (SLit ENOMEM_RETv) (ss_mem S_V) (ss_facts S_V).
Definition D_1 : sstate := Eval vm_compute in pin (addreg R_gate2 (addreg R_gate1 (addreg R_pat (addreg R_jt (addreg R_fmt D_0))))) 18%bv (SOff aQS 0).
Definition dia_lhs (ss : sstate) : sv := sr_get (ss_regs ss) 17%bv.
Definition djoin (tk : bool) (k : nat) (ss : sstate) : sstate :=
noconds (forget (fst (sym_run_toN_sh tfibsegs tfibtbl_rtD FUEL 0x6726c (arm BC_GEU tk (dia_lhs ss) (SLit 10) ss))) k [16%bv]).
Definition tighten (n : nat) (f : afact) (ss : sstate) : sstate :=
mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss) (ss_resv ss) (mkFacts ((n, f) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss))).
Definition hexfact (d : Z) : afact := mkAF (16 ^ (d - 1)) (16 ^ d - 8) 3.
Definition zmatch (b : option nat) (lo n : Z) (r : YP09.region) : bool :=
YP09.obase_eqb (YP09.r_base r) b && (YP09.r_lo r <=? lo) && (lo + n <=? YP09.r_hi r) && (0 <=? n).
Definition addzero_r (b : option nat) (lo n : Z) (r : YP09.region) : YP09.region :=
if zmatch b lo n r then YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r) (YP09.mkChunk lo (CZero n) :: YP09.r_chunks r)
else r.
Definition addzero (b : option nat) (lo n : Z) (ss : sstate) : sstate :=
mkSS (ss_pc ss) (ss_regs ss) (map (addzero_r b lo n) (ss_mem ss)) (ss_resv ss) (ss_facts ss).
Definition zbyte_chunk (off : Z) (c : YP09.chunk) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal w v => ((w =? 1)%N && sv_eqb v (SLit 0))%bool | _ => false end.
Definition zbytes_ok (lo n : Z) (cs : list YP09.chunk) : bool :=
forallb (fun i => existsb (zbyte_chunk (lo + Z.of_nat i)) cs) (seq 0 (Z.to_nat n)).
Definition addzero_ok (b : option nat) (lo n : Z) (ss : sstate) : bool :=
forallb (fun r => negb (zmatch b lo n r) || zbytes_ok lo n (YP09.r_chunks r)) (ss_mem ss).
Definition D_1_6 : sstate := Eval vm_compute in tighten aQS (hexfact 6) D_1.
Definition D_M6 : sstate := Eval vm_compute in runtoD 0x63970 D_1_6.
Definition MS_AL6 : sv := Eval vm_compute in sr_get (ss_regs D_M6) 13%bv.
Definition D_X6 : sstate := Eval vm_compute in runtoD 0x63974 (arm BC_EQ false MS_AL6 (SLit 0) D_M6).
Definition D_P6 : sstate := Eval vm_compute in runtoD 0x63970 D_X6.
Definition MS_PAD6 : sv := Eval vm_compute in sr_get (ss_regs D_P6) 13%bv.
Definition D_R6 : sstate := Eval vm_compute in runtoD 0x67188 (arm BC_EQ false MS_PAD6 (SLit 0) D_P6).
Definition D_Z6 : sstate := Eval vm_compute in addzero (Some 2%nat) (-2984) 48 D_R6.
Definition DG6r : sstate := Eval vm_compute in runtoD 0x67294 D_Z6.
Definition DG6_0 : sstate := Eval vm_compute in noconds DG6r.
Definition DJ6_0 : sstate := Eval vm_compute in djoin true (aDIG + 0) DG6_0.
Definition DG6_1 : sstate := Eval vm_compute in runtoD 0x67294 DJ6_0.
Definition DJ6_1 : sstate := Eval vm_compute in djoin true (aDIG + 1) DG6_1.
Definition DG6_2 : sstate := Eval vm_compute in runtoD 0x67294 DJ6_1.
Definition DJ6_2 : sstate := Eval vm_compute in djoin true (aDIG + 2) DG6_2.
Definition DG6_3 : sstate := Eval vm_compute in runtoD 0x67294 DJ6_2.
Definition DJ6_3 : sstate := Eval vm_compute in djoin true (aDIG + 3) DG6_3.
Definition DG6_4 : sstate := Eval vm_compute in runtoD 0x67294 DJ6_3.
Definition DJ6_4 : sstate := Eval vm_compute in djoin true (aDIG + 4) DG6_4.
Definition DG6_5 : sstate := Eval vm_compute in runtoD 0x67294 DJ6_4.
Definition DJ6_5 : sstate := Eval vm_compute in djoin true (aDIG + 5) DG6_5.
Definition D_END6 : sstate := Eval vm_compute in runtoD 0x5f9e4 DJ6_5.
Definition D_1_7 : sstate := Eval vm_compute in tighten aQS (hexfact 7) D_1.
Definition D_M7 : sstate := Eval vm_compute in runtoD 0x63970 D_1_7.
Definition MS_AL7 : sv := Eval vm_compute in sr_get (ss_regs D_M7) 13%bv.
Definition D_X7 : sstate := Eval vm_compute in runtoD 0x63974 (arm BC_EQ false MS_AL7 (SLit 0) D_M7).
Definition D_P7 : sstate := Eval vm_compute in runtoD 0x63970 D_X7.
Definition MS_PAD7 : sv := Eval vm_compute in sr_get (ss_regs D_P7) 13%bv.
Definition D_R7 : sstate := Eval vm_compute in runtoD 0x67188 (arm BC_EQ false MS_PAD7 (SLit 0) D_P7).
Definition D_Z7 : sstate := Eval vm_compute in addzero (Some 2%nat) (-2976) 40 D_R7.
Definition DG7r : sstate := Eval vm_compute in runtoD 0x67294 D_Z7.
Definition DG7_0 : sstate := Eval vm_compute in noconds DG7r.
Definition DJ7_0 : sstate := Eval vm_compute in djoin true (aDIG + 0) DG7_0.
Definition DG7_1 : sstate := Eval vm_compute in runtoD 0x67294 DJ7_0.
Definition DJ7_1 : sstate := Eval vm_compute in djoin true (aDIG + 1) DG7_1.
Definition DG7_2 : sstate := Eval vm_compute in runtoD 0x67294 DJ7_1.
Definition DJ7_2 : sstate := Eval vm_compute in djoin true (aDIG + 2) DG7_2.
Definition DG7_3 : sstate := Eval vm_compute in runtoD 0x67294 DJ7_2.
Definition DJ7_3 : sstate := Eval vm_compute in djoin true (aDIG + 3) DG7_3.
Definition DG7_4 : sstate := Eval vm_compute in runtoD 0x67294 DJ7_3.
Definition DJ7_4 : sstate := Eval vm_compute in djoin true (aDIG + 4) DG7_4.
Definition DG7_5 : sstate := Eval vm_compute in runtoD 0x67294 DJ7_4.
Definition DJ7_5 : sstate := Eval vm_compute in djoin true (aDIG + 5) DG7_5.
Definition DG7_6 : sstate := Eval vm_compute in runtoD 0x67294 DJ7_5.
Definition DJ7_6 : sstate := Eval vm_compute in djoin true (aDIG + 6) DG7_6.
Definition D_END7 : sstate := Eval vm_compute in runtoD 0x5f9e4 DJ7_6.
Definition D_1_8 : sstate := Eval vm_compute in tighten aQS (hexfact 8) D_1.
Definition D_M8 : sstate := Eval vm_compute in runtoD 0x63970 D_1_8.
Definition MS_AL8 : sv := Eval vm_compute in sr_get (ss_regs D_M8) 13%bv.
Definition D_X8 : sstate := Eval vm_compute in runtoD 0x63974 (arm BC_EQ false MS_AL8 (SLit 0) D_M8).
Definition D_P8 : sstate := Eval vm_compute in runtoD 0x63970 D_X8.
Definition MS_PAD8 : sv := Eval vm_compute in sr_get (ss_regs D_P8) 13%bv.
Definition D_R8 : sstate := Eval vm_compute in runtoD 0x67188 (arm BC_EQ false MS_PAD8 (SLit 0) D_P8).
Definition D_Z8 : sstate := Eval vm_compute in addzero (Some 2%nat) (-2968) 32 D_R8.
Definition DG8r : sstate := Eval vm_compute in runtoD 0x67294 D_Z8.
Definition DG8_0 : sstate := Eval vm_compute in noconds DG8r.
Definition DJ8_0 : sstate := Eval vm_compute in djoin true (aDIG + 0) DG8_0.
Definition DG8_1 : sstate := Eval vm_compute in runtoD 0x67294 DJ8_0.
Definition DJ8_1 : sstate := Eval vm_compute in djoin true (aDIG + 1) DG8_1.
Definition DG8_2 : sstate := Eval vm_compute in runtoD 0x67294 DJ8_1.
Definition DJ8_2 : sstate := Eval vm_compute in djoin true (aDIG + 2) DG8_2.
Definition DG8_3 : sstate := Eval vm_compute in runtoD 0x67294 DJ8_2.
Definition DJ8_3 : sstate := Eval vm_compute in djoin true (aDIG + 3) DG8_3.
Definition DG8_4 : sstate := Eval vm_compute in runtoD 0x67294 DJ8_3.
Definition DJ8_4 : sstate := Eval vm_compute in djoin true (aDIG + 4) DG8_4.
Definition DG8_5 : sstate := Eval vm_compute in runtoD 0x67294 DJ8_4.
Definition DJ8_5 : sstate := Eval vm_compute in djoin true (aDIG + 5) DG8_5.
Definition DG8_6 : sstate := Eval vm_compute in runtoD 0x67294 DJ8_5.
Definition DJ8_6 : sstate := Eval vm_compute in djoin true (aDIG + 6) DG8_6.
Definition DG8_7 : sstate := Eval vm_compute in runtoD 0x67294 DJ8_6.
Definition DJ8_7 : sstate := Eval vm_compute in djoin true (aDIG + 7) DG8_7.
Definition D_END8 : sstate := Eval vm_compute in runtoD 0x5f9e4 DJ8_7.
Definition D_1_12 : sstate := Eval vm_compute in tighten aQS (hexfact 12) D_1.
Definition D_M12 : sstate := Eval vm_compute in runtoD 0x63970 D_1_12.
Definition MS_AL12 : sv := Eval vm_compute in sr_get (ss_regs D_M12) 13%bv.
Definition DG12r : sstate := Eval vm_compute in runtoD 0x67294 (arm BC_EQ false MS_AL12 (SLit 0) D_M12).
Definition DG12_0 : sstate := Eval vm_compute in noconds DG12r.
Definition DJ12_0 : sstate := Eval vm_compute in djoin true (aDIG + 0) DG12_0.
Definition DG12_1 : sstate := Eval vm_compute in runtoD 0x67294 DJ12_0.
Definition DJ12_1 : sstate := Eval vm_compute in djoin true (aDIG + 1) DG12_1.
Definition DG12_2 : sstate := Eval vm_compute in runtoD 0x67294 DJ12_1.
Definition DJ12_2 : sstate := Eval vm_compute in djoin true (aDIG + 2) DG12_2.
Definition DG12_3 : sstate := Eval vm_compute in runtoD 0x67294 DJ12_2.
Definition DJ12_3 : sstate := Eval vm_compute in djoin true (aDIG + 3) DG12_3.
Definition DG12_4 : sstate := Eval vm_compute in runtoD 0x67294 DJ12_3.
Definition DJ12_4 : sstate := Eval vm_compute in djoin true (aDIG + 4) DG12_4.
Definition DG12_5 : sstate := Eval vm_compute in runtoD 0x67294 DJ12_4.
Definition DJ12_5 : sstate := Eval vm_compute in djoin true (aDIG + 5) DG12_5.
Definition DG12_6 : sstate := Eval vm_compute in runtoD 0x67294 DJ12_5.
Definition DJ12_6 : sstate := Eval vm_compute in djoin true (aDIG + 6) DG12_6.
Definition DG12_7 : sstate := Eval vm_compute in runtoD 0x67294 DJ12_6.
Definition DJ12_7 : sstate := Eval vm_compute in djoin true (aDIG + 7) DG12_7.
Definition DG12_8 : sstate := Eval vm_compute in runtoD 0x67294 DJ12_7.
Definition DJ12_8 : sstate := Eval vm_compute in djoin true (aDIG + 8) DG12_8.
Definition DG12_9 : sstate := Eval vm_compute in runtoD 0x67294 DJ12_8.
Definition DJ12_9 : sstate := Eval vm_compute in djoin true (aDIG + 9) DG12_9.
Definition DG12_10 : sstate := Eval vm_compute in runtoD 0x67294 DJ12_9.
Definition DJ12_10 : sstate := Eval vm_compute in djoin true (aDIG + 10) DG12_10.
Definition DG12_11 : sstate := Eval vm_compute in runtoD 0x67294 DJ12_10.
Definition DJ12_11 : sstate := Eval vm_compute in djoin true (aDIG + 11) DG12_11.
Definition D_END12 : sstate := Eval vm_compute in runtoD 0x5f9e4 DJ12_11.
Lemma D_pcs6 : map ss_pc [D_M6; D_P6; D_R6; DG6_0; DJ6_0; DG6_5; DJ6_5; D_END6] = [0x63970; 0x63970; 0x67188; 0x67294; 0x6726c; 0x67294; 0x6726c; 0x5f9e4]. Proof. vm_compute. reflexivity. Qed.
Lemma D_pcs7 : map ss_pc [D_M7; D_P7; D_R7; DG7_0; DJ7_0; DG7_6; DJ7_6; D_END7] = [0x63970; 0x63970; 0x67188; 0x67294; 0x6726c; 0x67294; 0x6726c; 0x5f9e4]. Proof. vm_compute. reflexivity. Qed.
Lemma D_pcs8 : map ss_pc [D_M8; D_P8; D_R8; DG8_0; DJ8_0; DG8_7; DJ8_7; D_END8] = [0x63970; 0x63970; 0x67188; 0x67294; 0x6726c; 0x67294; 0x6726c; 0x5f9e4]. Proof. vm_compute. reflexivity. Qed.
Lemma D_pcs12 : map ss_pc [D_M12; DG12_0; DJ12_0; DG12_11; DJ12_11; D_END12] = [0x63970; 0x67294; 0x6726c; 0x67294; 0x6726c; 0x5f9e4]. Proof. vm_compute. reflexivity. Qed.
Lemma D_zok : addzero_ok (Some 2%nat) (-2984) 48 D_R6 = true /\ addzero_ok (Some 2%nat) (-2976) 40 D_R7 = true /\ addzero_ok (Some 2%nat) (-2968) 32 D_R8 = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma D_joins : djoin false (aDIG + 0) DG6_0 = DJ6_0 /\ djoin false (aDIG + 5) DG6_5 = DJ6_5 /\ djoin false (aDIG + 0) DG12_0 = DJ12_0 /\ djoin false (aDIG + 11) DG12_11 = DJ12_11.
Proof. vm_compute. repeat split; reflexivity. Qed.
