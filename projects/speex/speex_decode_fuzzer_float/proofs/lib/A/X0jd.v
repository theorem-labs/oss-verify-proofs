(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1d7 X1cx X1cy X1cp X1cj X1dd X1cg X1cm X1cs X1da X1d1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rw X1rn X1s9 X1rz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1nu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X00a X001 X00b X00c X000 X00i X06k
X0hi X0j3 X0hr X0hn X0j0 X0j4 X0h2
X03z X04v X01z X047 X04w X044 X057 X055 X041 X0jw X0jo X0jj X0jl
X080 X0fy X0fg X0d8 X0ea X0hg X0jc X0eh X0c3 X0je.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require X023.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0e7 X002 X0jp X0jk X04x X056.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r9 X0r0 X0ra X0rb X0qz X0rh X0xc X183 X19m X18c X188 X19k X19n X17n X0ux X0vt X0sy X0v5 X0vu X0v2 X0w5 X0w3 X0uz X1ab X1a3 X19y X1a0 X16j X161 X13t X14v X181 X19t X152 X12o X19v.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0t2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X14s X0r1 X1a4 X19z X0vv X0w4.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rh OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xc OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ux OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0sy OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w3 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0uz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1ab OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1a3 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1a0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X181 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X152 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19v.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1a4 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19z OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vv OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w4.
Import ListNotations.
Open Scope Z_scope.

Lemma ro_cells_app' : forall (m : mem) A cs1 cs2,
ro_cells bsegs m A (cs1 ++ cs2) <-> ro_cells bsegs m A cs1 /\ ro_cells bsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros m A cs1 cs2. unfold ro_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, bytes_at_app.
split.
- intros ((W1 & W2) & (B1 & B2)). rewrite (cells_bytes_length cs1 W1) in B2. tauto.
- intros ((W1 & B1) & (W2 & B2)). rewrite (cells_bytes_length cs1 W1). tauto.
Qed.

Lemma ro_split1 : forall (m : mem) A c cs, ro_cells bsegs m A (c :: cs) ->
ro_cells bsegs m A [c] /\ ro_cells bsegs m (A + Z.of_nat (csize c)) cs.
Proof.
intros m A c cs H. change (c :: cs) with ([c] ++ cs) in H. apply ro_cells_app' in H as [H1 H2].
split; [exact H1|]. cbn [cells_size] in H2. rewrite Nat.add_0_r in H2. exact H2.
Qed.

Lemma ro_join1 : forall (m : mem) A c cs, ro_cells bsegs m A [c] -> ro_cells bsegs m (A + Z.of_nat (csize c)) cs ->
ro_cells bsegs m A (c :: cs).
Proof.
intros m A c cs H1 H2. change (c :: cs) with ([c] ++ cs). apply ro_cells_app'. split; [exact H1|].
cbn [cells_size]. rewrite Nat.add_0_r. exact H2.
Qed.

Lemma stk_sub' : forall (m : mem) lo hi a b, stk bsegs m lo hi -> lo <= a -> a <= b -> b <= hi -> stk bsegs m a b.
Proof.
intros m lo hi a b H H1 H2 H3. destruct (stk_split bsegs m lo a hi H ltac:(lia)) as [_ H4].
destruct (stk_split bsegs m a b hi H4 ltac:(lia)) as [H5 _]. exact H5.
Qed.

Section Consts.
Hypothesis AF : art_facts RTA.
Hypothesis IOC : forall Σ m, ART RTA Σ m -> io_consts m.

Lemma rta_drv : forall Σ m, ART RTA Σ m -> drv_consts m.
Proof using AF IOC.
intros Σ m HA. pose proof (IOC Σ m HA) as IO.
pose proof (af_got_lib RTA AF Σ m HA) as (_ & GSSP).
pose proof (io_ro_at m IO 0xfcd78 _ ltac:(io_in)) as G1. apply ro_split1 in G1 as [G1 G2].
pose proof (io_ro_at m IO 0xfc010 _ ltac:(io_in)) as G3.
pose proof (io_acc_at m IO 0x219c0 128 ltac:(io_in)) as B1. pose proof (io_acc_at m IO 0x165c0 128 ltac:(io_in)) as B2.
unfold drv_consts, stderr_cells. split; [split; [exact G1 | exact G3]|]. split; [exact GSSP|]. split; [exact G2|].
split; [apply (acc_sub bsegs m 0x219c0 128 S_SHORT 31 B1); unfold S_SHORT; lia|].
apply (acc_sub bsegs m 0x165c0 128 S_OVER 31 B2); unfold S_OVER; lia.
Qed.

Lemma rta_icpt : forall Σ m, ART RTA Σ m -> icpt_consts m.
Proof using IOC.
intros Σ m HA. pose proof (IOC Σ m HA) as IO.
pose proof (ART_consts Σ m HA) as (_ & _ & _ & M2S & _).
pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
pose proof (io_rw_at m IO 0xfdf08 _ ltac:(io_in)) as R1. change [C8 (Z_to_bv 64 0xf6df8); C8 (Z_to_bv 64 0xedcfc)]
with ([C8 (Z_to_bv 64 0xf6df8)] ++ [C8 (Z_to_bv 64 0xedcfc)]) in R1. apply X1dr.rw_cells_app in R1 as [R1 R2].
unfold icpt_consts. split; [exact T1|]. split; [exact R1|]. split; [exact M2S|].
split; [exact (io_acc_at m IO 0x628100 16 ltac:(io_in))|]. split; [exact R2|].
split; [exact (io_acc_at m IO 0x219c0 128 ltac:(io_in)) | exact (io_acc_at m IO 0x165c0 128 ltac:(io_in))].
Qed.

Lemma rta_xit : forall Σ m, ART RTA Σ m -> xit_rt m.
Proof using IOC.
intros Σ m HA. pose proof (IOC Σ m HA) as IO.
pose proof (ART_consts Σ m HA) as (_ & (G1 & G2 & _) & _ & (M1 & M2 & _) & (P1 & _ & (S1 & S2) & P3 & P4) & _ & _ & (_ & _ & _ & X4 & _)).
pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
pose proof (ART_shadow Σ m HA) as (_ & _ & SHW & _).
unfold xit_rt.
split; [exact (io_ro_at m IO 0xf7f78 _ ltac:(io_in))|].
split; [exact (io_ro_at m IO 0xfce88 _ ltac:(io_in))|].
split; [exact (io_ro_at m IO 0xfc0e8 _ ltac:(io_in))|].
split; [exists (Z_to_bv 64 0xfdec8); exact (io_ro_at m IO 0xfdec8 _ ltac:(io_in))|].
split; [exact (io_ro_at m IO 0xfce00 _ ltac:(io_in))|].
split; [exact (ro_of_rw _ _ _ G1)|].
split.
{ apply ro_join1; [exact (ro_of_rw _ _ _ P1)|]. apply ro_join1; [exact X4|].
change [C8 (Z_to_bv 64 0x105ab8); C8 (Z_to_bv 64 0x1067a8); C8 (Z_to_bv 64 0x1067b0); C8 (Z_to_bv 64 0x1067a0); C8 (Z_to_bv 64 0xfe040)]
with ([C8 (Z_to_bv 64 0x105ab8); C8 (Z_to_bv 64 0x1067a8); C8 (Z_to_bv 64 0x1067b0); C8 (Z_to_bv 64 0x1067a0)] ++ [C8 (Z_to_bv 64 0xfe040)]).
apply ro_cells_app'. split; [exact (ro_of_rw _ _ _ M1)|]. exact (ro_of_rw _ _ _ S1). }
split; [exact (io_ro_at m IO 0x1032d0 _ ltac:(io_in))|].
split; [exact (io_rw_at m IO 0x103370 _ ltac:(io_in))|].
split; [exact (ro_of_rw _ _ _ M2)|].
split; [exact T1|].
split; [exact (ro_of_rw _ _ _ P3)|].
split; [exact (ro_of_rw _ _ _ P4)|].
split; [exact (ro_of_rw _ _ _ S2)|].
split; [exact (io_ro_at m IO 0x197960 _ ltac:(io_in))|].
assert (E1 : pg_dn (shad 0x10000) = 0x7fffa000) by reflexivity. assert (E2 : shad SEGTOP_A = 0x800c3600) by reflexivity.
rewrite E1, E2 in SHW.
split; [apply (stk_sub' m _ _ _ _ SHW); lia|].
split; [apply (stk_sub' m _ _ _ _ SHW); lia|].
apply (stk_sub' m _ _ _ _ SHW); lia.
Qed.

Lemma rta_pf : forall Σ m, ART RTA Σ m -> pf_consts m.
Proof using IOC.
intros Σ m HA. pose proof (IOC Σ m HA) as IO.
pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & (P1 & _) & _).
pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
pose proof (rta_ic Σ m HA) as (IC1 & IC2 & _ & IC4 & IC5).
pose proof (io_ro_at m IO 0xfdf28 _ ltac:(io_in)) as V1. apply ro_split1 in V1 as [V1 V2]. apply ro_split1 in V2 as [V2 _].
pose proof (io_acc_at m IO 0x165c0 128 ltac:(io_in)) as B2.
unfold pf_consts, pfcells. split.
{ split; [exact T1|]. split; [exact (ro_of_rw _ _ _ P1)|]. split; [exact (io_ro_at m IO 0x19763c _ ltac:(io_in))|].
split; [exact V1 | exact V2]. }
split; [unfold ictx; split; [exact IC1|]; split; [exact IC2|]; split; [exact IC4 | exact IC5]|].
split; [exact (io_acc_at m IO 0x1529e 4 ltac:(io_in))|].
split; [exact (io_acc_at m IO 0x10f54 10 ltac:(io_in))|].
split; [exact (io_acc_at m IO 0x23708 16 ltac:(io_in))|].
split; [exact (io_acc_at m IO 0x22ad2 7 ltac:(io_in))|].
split; [apply (acc_sub bsegs m 0x165c0 128 0x165d7 17 B2); lia|].
split; [exact (io_acc_at m IO 0x1f32d 21 ltac:(io_in))|].
split; [exact (io_acc_at m IO 0x1f342 23 ltac:(io_in))|].
exact (io_acc_at m IO 0x1ac77 33 ltac:(io_in)).
Qed.

End Consts.

Lemma LIB_locA : fp_local LIB_FP LIB_A.
Proof. intros m m' _ _. exact I. Qed.

Theorem main_stmt_of_fuzz : rt_contracts RTA -> fuzz_one_cpsE RTA OUT_repA ERR_repA IO_FPA LIB_A -> MAIN_stmt.
Proof.
intros RC FUZZ argvb fs VARGV DS.
pose proof (rc_facts RTA RC) as AF.
pose proof (rip_proof) as RIP.
pose proof (rta_drv AF rta_io) as AF_DRV.
pose proof (rta_icpt rta_io) as AF_ICPT.
pose proof (rta_xit rta_io) as AF_XIT.
pose proof (rta_pf rta_io) as AF_PF.
exact (main_realizesAS RTA OUT_repA ERR_repA IO_FPA XENVA XENV_FPA XENVA1 XENVA1x LIB_A argvb fs AF AF_DRV
(malloc_contract_okF_of RTA (rc_malloc RTA RC)) (free_contract_okF_of RTA (rc_free RTA RC)) (free_null_contract_ok_of RTA (rc_free_null RTA RC))
(rc_memcpy RTA RC)
(read_file_okF RTA AF AF_ICPT RIP) (read_dir_ok RTA AF AF_ICPT)
(fprintf_ok RTA AF RIP rta_shw AF_PF) (fwrite_ok RTA AF AF_ICPT) (vprintf_okR RTA AF RIP rta_shw AF_PF)
(open_okF RTA AF) (open_refused_ok RTA AF) (close_okF RTA AF) (exit_ok RTA AF AF_XIT) (exit_ok1 RTA AF AF_XIT) XENVA1x_of
FUZZ VARGV OUT_locA ERR_locA XENV_locA XENV_locA1 LIB_locA IO_imgA XENV_imgA XENVA_reg_out XENVA_reg_in REG_fpA (DS true)).
Qed.

Corollary main_stmt_closed : fuzz_one_cpsE RTA OUT_repA ERR_repA IO_FPA LIB_A -> MAIN_stmt.
Proof. exact (main_stmt_of_fuzz rta_contracts_closed). Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Lemma ro_cells_app' : forall (m : mem) A cs1 cs2,
ro_cells asegs m A (cs1 ++ cs2) <-> ro_cells asegs m A cs1 /\ ro_cells asegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros m A cs1 cs2. unfold ro_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, bytes_at_app.
split.
- intros ((W1 & W2) & (B1 & B2)). rewrite (cells_bytes_length cs1 W1) in B2. tauto.
- intros ((W1 & B1) & (W2 & B2)). rewrite (cells_bytes_length cs1 W1). tauto.
Qed.

Lemma ro_split1 : forall (m : mem) A c cs, ro_cells asegs m A (c :: cs) ->
ro_cells asegs m A [c] /\ ro_cells asegs m (A + Z.of_nat (csize c)) cs.
Proof.
intros m A c cs H. change (c :: cs) with ([c] ++ cs) in H. apply ro_cells_app' in H as [H1 H2].
split; [exact H1|]. cbn [cells_size] in H2. rewrite Nat.add_0_r in H2. exact H2.
Qed.

Lemma ro_join1 : forall (m : mem) A c cs, ro_cells asegs m A [c] -> ro_cells asegs m (A + Z.of_nat (csize c)) cs ->
ro_cells asegs m A (c :: cs).
Proof.
intros m A c cs H1 H2. change (c :: cs) with ([c] ++ cs). apply ro_cells_app'. split; [exact H1|].
cbn [cells_size]. rewrite Nat.add_0_r. exact H2.
Qed.

Lemma stk_sub' : forall (m : mem) lo hi a b, stk asegs m lo hi -> lo <= a -> a <= b -> b <= hi -> stk asegs m a b.
Proof.
intros m lo hi a b H H1 H2 H3. destruct (stk_split asegs m lo a hi H ltac:(lia)) as [_ H4].
destruct (stk_split asegs m a b hi H4 ltac:(lia)) as [H5 _]. exact H5.
Qed.

Section Consts.
Hypothesis AF : art_facts RTA.
Hypothesis IOC : forall Σ m, ART RTA Σ m -> io_consts m.

Lemma rta_drv : forall Σ m, ART RTA Σ m -> drv_consts m.
Proof using AF IOC.
intros Σ m HA. pose proof (IOC Σ m HA) as IO.
pose proof (af_got_lib RTA AF Σ m HA) as (_ & GSSP).
pose proof (io_ro_at m IO 0xf44f8 _ ltac:(io_in)) as G1. apply ro_split1 in G1 as [G1 G2].
pose proof (io_ro_at m IO 0xf3790 _ ltac:(io_in)) as G3.
pose proof (io_acc_at m IO 0x21980 128 ltac:(io_in)) as B1. pose proof (io_acc_at m IO 0x164c0 128 ltac:(io_in)) as B2.
unfold drv_consts, stderr_cells. split; [split; [exact G1 | exact G3]|]. split; [exact GSSP|]. split; [exact G2|].
split; [apply (acc_sub asegs m 0x21980 128 S_SHORT 31 B1); unfold S_SHORT; lia|].
apply (acc_sub asegs m 0x164c0 128 S_OVER 31 B2); unfold S_OVER; lia.
Qed.

Lemma rta_icpt : forall Σ m, ART RTA Σ m -> icpt_consts m.
Proof using IOC.
intros Σ m HA. pose proof (IOC Σ m HA) as IO.
pose proof (ART_consts Σ m HA) as (_ & _ & _ & M2S & _).
pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
pose proof (io_rw_at m IO 0xf5688 _ ltac:(io_in)) as R1. change [C8 (Z_to_bv 64 0xee584); C8 (Z_to_bv 64 0xe5488)]
with ([C8 (Z_to_bv 64 0xee584)] ++ [C8 (Z_to_bv 64 0xe5488)]) in R1. apply X1dr.rw_cells_app in R1 as [R1 R2].
unfold icpt_consts. split; [exact T1|]. split; [exact R1|]. split; [exact M2S|].
split; [exact (io_acc_at m IO 0x61f8c0 16 ltac:(io_in))|]. split; [exact R2|].
split; [exact (io_acc_at m IO 0x21980 128 ltac:(io_in)) | exact (io_acc_at m IO 0x164c0 128 ltac:(io_in))].
Qed.

Lemma rta_xit : forall Σ m, ART RTA Σ m -> xit_rt m.
Proof using IOC.
intros Σ m HA. pose proof (IOC Σ m HA) as IO.
pose proof (ART_consts Σ m HA) as (_ & (G1 & G2 & _) & _ & (M1 & M2 & _) & (P1 & _ & (S1 & S2) & P3 & P4) & _ & _ & (_ & _ & _ & X4 & _)).
pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
pose proof (ART_shadow Σ m HA) as (_ & _ & SHW & _).
unfold xit_rt.
split; [exact (io_ro_at m IO 0xef708 _ ltac:(io_in))|].
split; [exact (io_ro_at m IO 0xf4608 _ ltac:(io_in))|].
split; [exact (io_ro_at m IO 0xf3868 _ ltac:(io_in))|].
split; [exists (Z_to_bv 64 0xf5648); exact (io_ro_at m IO 0xf5648 _ ltac:(io_in))|].
split; [exact (io_ro_at m IO 0xf4580 _ ltac:(io_in))|].
split; [exact (ro_of_rw _ _ _ G1)|].
split.
{ apply ro_join1; [exact (ro_of_rw _ _ _ P1)|]. apply ro_join1; [exact X4|].
change [C8 (Z_to_bv 64 0xfd278); C8 (Z_to_bv 64 0xfdf68); C8 (Z_to_bv 64 0xfdf70); C8 (Z_to_bv 64 0xfdf60); C8 (Z_to_bv 64 0xf57c0)]
with ([C8 (Z_to_bv 64 0xfd278); C8 (Z_to_bv 64 0xfdf68); C8 (Z_to_bv 64 0xfdf70); C8 (Z_to_bv 64 0xfdf60)] ++ [C8 (Z_to_bv 64 0xf57c0)]).
apply ro_cells_app'. split; [exact (ro_of_rw _ _ _ M1)|]. exact (ro_of_rw _ _ _ S1). }
split; [exact (io_ro_at m IO 0xfaa90 _ ltac:(io_in))|].
split; [exact (io_rw_at m IO 0xfab30 _ ltac:(io_in))|].
split; [exact (ro_of_rw _ _ _ M2)|].
split; [exact T1|].
split; [exact (ro_of_rw _ _ _ P3)|].
split; [exact (ro_of_rw _ _ _ P4)|].
split; [exact (ro_of_rw _ _ _ S2)|].
split; [exact (io_ro_at m IO 0x18f120 _ ltac:(io_in))|].
assert (E1 : pg_dn (shad 0x10000) = 0x7fffa000) by reflexivity. assert (E2 : shad SEGTOP_A = 0x800c2400) by reflexivity.
rewrite E1, E2 in SHW.
split; [apply (stk_sub' m _ _ _ _ SHW); lia|].
split; [apply (stk_sub' m _ _ _ _ SHW); lia|].
apply (stk_sub' m _ _ _ _ SHW); lia.
Qed.

Lemma rta_pf : forall Σ m, ART RTA Σ m -> pf_consts m.
Proof using IOC.
intros Σ m HA. pose proof (IOC Σ m HA) as IO.
pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & (P1 & _) & _).
pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
pose proof (rta_ic Σ m HA) as (IC1 & IC2 & _ & IC4 & IC5).
pose proof (io_ro_at m IO 0xf56a8 _ ltac:(io_in)) as V1. apply ro_split1 in V1 as [V1 V2]. apply ro_split1 in V2 as [V2 _].
pose proof (io_acc_at m IO 0x164c0 128 ltac:(io_in)) as B2.
unfold pf_consts, pfcells. split.
{ split; [exact T1|]. split; [exact (ro_of_rw _ _ _ P1)|]. split; [exact (io_ro_at m IO 0x18edfc _ ltac:(io_in))|].
split; [exact V1 | exact V2]. }
split; [unfold ictx; split; [exact IC1|]; split; [exact IC2|]; split; [exact IC4 | exact IC5]|].
split; [exact (io_acc_at m IO 0x151ae 4 ltac:(io_in))|].
split; [exact (io_acc_at m IO 0x10f3c 10 ltac:(io_in))|].
split; [exact (io_acc_at m IO 0x236c8 16 ltac:(io_in))|].
split; [exact (io_acc_at m IO 0x22a98 7 ltac:(io_in))|].
split; [apply (acc_sub asegs m 0x164c0 128 0x164e7 17 B2); lia|].
split; [exact (io_acc_at m IO 0x1f2f3 21 ltac:(io_in))|].
split; [exact (io_acc_at m IO 0x1f308 23 ltac:(io_in))|].
exact (io_acc_at m IO 0x1ab8e 33 ltac:(io_in)).
Qed.

End Consts.

Lemma LIB_locA : fp_local LIB_FP LIB_A.
Proof. intros m m' _ _. exact I. Qed.

Theorem main_stmt_of_fuzz : rt_contracts RTA -> fuzz_one_cpsE RTA OUT_repA ERR_repA IO_FPA LIB_A -> MAIN_stmt.
Proof.
intros RC FUZZ argvb fs VARGV DS.
pose proof (rc_facts RTA RC) as AF.
pose proof (rip_proof) as RIP.
pose proof (rta_drv AF rta_io) as AF_DRV.
pose proof (rta_icpt rta_io) as AF_ICPT.
pose proof (rta_xit rta_io) as AF_XIT.
pose proof (rta_pf rta_io) as AF_PF.
exact (main_realizesAS RTA OUT_repA ERR_repA IO_FPA XENVA XENV_FPA XENVA1 XENVA1x LIB_A argvb fs AF AF_DRV
(malloc_contract_okF_of RTA (rc_malloc RTA RC)) (free_contract_okF_of RTA (rc_free RTA RC)) (free_null_contract_ok_of RTA (rc_free_null RTA RC))
(rc_memcpy RTA RC)
(read_file_okF RTA AF AF_ICPT RIP) (read_dir_ok RTA AF AF_ICPT)
(fprintf_ok RTA AF RIP rta_shw AF_PF) (fwrite_ok RTA AF AF_ICPT) (vprintf_okR RTA AF RIP rta_shw AF_PF)
(open_okF RTA AF) (open_refused_ok RTA AF) (close_okF RTA AF) (exit_ok RTA AF AF_XIT) (exit_ok1 RTA AF AF_XIT) XENVA1x_of
FUZZ VARGV OUT_locA ERR_locA XENV_locA XENV_locA1 LIB_locA IO_imgA XENV_imgA XENVA_reg_out XENVA_reg_in REG_fpA (DS true)).
Qed.

Corollary main_stmt_closed : fuzz_one_cpsE RTA OUT_repA ERR_repA IO_FPA LIB_A -> MAIN_stmt.
Proof. exact (main_stmt_of_fuzz rta_contracts_closed). Qed.
