(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge Image Mem.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg RF_fi_iface.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition isframe_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists (r : Z) (a1' a2' a3' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom usegs).

Definition isframe_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (S : Z) (bl : list Z),
    buf_at m S bl -> (0 < S \/ zlen bl = 0) -> mem_inv usegs m ->
    a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (zlen bl) ->
    evt usegs (isframe_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PFI_ISFRAME) fc None m (seg_rom usegs)).

Lemma isframe_proof : isframe_stmt.
Proof.
  intros until bl. intros BUF SN MI -> ->. unfold PFI_ISFRAME.
  pose proof (buf_at_bound _ _ _ BUF) as BB.
  zstep. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00B0>10640767904.3810644848408.4214202106942.4414204194750.4014937404944.6014937404944.6114937404946.5816077671799.3821920002621.3921922089021.4328465183085.3945054632370.5959576979761.4759588178608.6059588178608.6159588178610.5961448213823.4561450317375.4100000300600900<00=00>00?00@00C00F00G00H00I00J00K00L00O00RS1KS1KS1KS1KFFFFS1KS1KSSSSSSS1KS1K".
if_cases K; zify_cond K.
  - pose proof (buf_read m S bl 0 BUF ltac:(lia)) as RD0. replace (wa (S + 0)) with (wa S) in RD0 by (unfold wa; f_equal; lia).
    pose proof (buf_read m S bl 1 BUF ltac:(lia)) as RD1.
    pose proof (buf_read m S bl 2 BUF ltac:(lia)) as RD2.
    pose proof (buf_read m S bl 3 BUF ltac:(lia)) as RD3.
    destruct (buf_nth m S bl 0 BUF ltac:(lia)) as [_ R0]. destruct (buf_nth m S bl 1 BUF ltac:(lia)) as [_ R1].
    destruct (buf_nth m S bl 2 BUF ltac:(lia)) as [_ R2]. destruct (buf_nth m S bl 3 BUF ltac:(lia)) as [_ R3].
    zstep. if_cases KN; zify_cond KN; [exfalso; lia|].
    do 12 zstep.   (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1.
    + (* [comment removed for export] *) do 6 zstep. finish.
    + (* [comment removed for export] *) zstep. zstep. finish.
  - zstep. zstep. finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition FHTAB : list Z := [0;0;0;0;0;0;0;0; 1;0;0;0;0;0;0;0; 2;0;0;0;0;0;0;0; 4;0;0;0;0;0;0;0;
                              0;0;0;0;0;0;0;0; 2;0;0;0;0;0;0;0; 4;0;0;0;0;0;0;0; 8;0;0;0;0;0;0;0]%Z.
Lemma fhtab_bytes : forall m, mem_inv usegs m -> bytes_at usegs m PFI_DIDTAB (map (Z_to_bv 8) FHTAB).
Proof.
  intros m MI. apply ro_bytes_at. { exact MI. } { unfold PFI_DIDTAB. Local Ltac2 Set LiaHints.tbl := fun () => "0020=31563816725.240634911374.2000001002SS".
lia. } { cbn. unfold PFI_DIDTAB. lia. }
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Lemma fhtab_read : forall m k, mem_inv usegs m -> 0 <= k < 8 ->
  ov_read_bytes usegs m (wa (PFI_DIDTAB + 8 * k)) 8 = Some (map (Z_to_bv 8) (firstn 8 (skipn (Z.to_nat (8 * k)) FHTAB))).
Proof.
  intros m k MI Hk.
  rewrite (bytes_at_read usegs m PFI_DIDTAB (map (Z_to_bv 8) FHTAB) (8 * k) 8 (fhtab_bytes m MI)); [| lia| cbn; lia].
  f_equal. rewrite <- List.firstn_map, <- List.skipn_map. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zrange_all : forall (P : Z -> bool) n, forallb P (map Z.of_nat (seq 0 n)) = true -> forall c, 0 <= c < Z.of_nat n -> P c = true.
Proof.
  intros P n H c Hc. apply (proj1 (forallb_forall _ _) H). apply in_map_iff. exists (Z.to_nat c). Local Ltac2 Set LiaHints.tbl := fun () => "0020=25492742081.529765743970.5000004008S2HcS2Hc".
split; [lia|]. apply in_seq. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Definition fhsize_post (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists (r : Z) (a1' a2' a3' a4' a5' a6' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom usegs).

Definition fhsize_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (S : Z) (bl : list Z),
    buf_at m S bl -> (0 < S \/ zlen bl = 0) -> mem_inv usegs m ->
    a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (zlen bl) ->
    evt usegs (fhsize_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PFI_FHSIZE) fc None m (seg_rom usegs)).

Lemma fhsize_proof : fhsize_stmt.
Proof.
  intros until bl. intros BUF SN MI -> ->. unfold PFI_FHSIZE.
  pose proof (buf_at_bound _ _ _ BUF) as BB.
  zstep. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00F0>11447729958.811442433912.43 16077671799.3824350674608.5924350674609.5829324322045.5829786629082.4329792256217.4733495333975.4436303483014.5341415827530.4141565867382.5041565867384.4841565867385.4745065529984.3845069577785.3954979766591.4355707291956.4859709842686.536632272804.44 67538440320.438573091283.43 00000100200300400500600700800=00>00?00C00G00K00N00Q00U00V00W00\00`00dFSFSSSSSS3L24FSS2R4S2R4S2R4S1KS1KS2L3SFS3L24S2HcS2R4".
if_cases K; zify_cond K.
  - pose proof (buf_read m S bl 4 BUF ltac:(lia)) as RD4. destruct (buf_nth m S bl 4 BUF ltac:(lia)) as [_ R4].
    zstep. zstep. zstep. if_cases KO; zify_cond KO; [exfalso; lia|].
    zstep. (* [comment removed for export] *) cbv beta. rewrite (byte_lit _ R4).
    set (c := Znth 4 bl) in *.
    assert (L3 : 0 <= Z.land c 3 <= 3).
    { assert (E : Z.land c 3 = c mod 4) by exact (Z.land_ones c 2 ltac:(lia)). rewrite E. pose proof (Z.mod_pos_bound c 4). lia. }
    assert (L6 : 0 <= Z.shiftr c 6 <= 3) by (rewrite Z.shiftr_div_pow2 by lia; change (2^6) with 64; lia).
    assert (S3 : Z.shiftl (Z.land c 3) 3 = 8 * Z.land c 3) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (S6 : Z.shiftl (Z.shiftr c 6) 3 = 8 * Z.shiftr c 6) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    do 5 zstep.
    zstep. if_cases KT; zify_cond KT; [exfalso; lia|].
    do 5 zstep.
    zstep. if_cases KU; zify_cond KU; [exfalso; lia|].
    do 6 zstep.
    assert (RDA : ov_read_bytes usegs m (wa (66448 + Z.shiftl (Z.land c 3) 3)) 8
                  = Some (map (Z_to_bv 8) (firstn 8 (skipn (Z.to_nat (8 * Z.land c 3)) FHTAB)))).
    { replace (66448 + Z.shiftl (Z.land c 3) 3) with (PFI_DIDTAB + 8 * Z.land c 3)
        by (unfold PFI_DIDTAB; rewrite Z.shiftl_mul_pow2 by lia; lia).
      apply fhtab_read; [exact MI| lia]. }
    assert (RDB : ov_read_bytes usegs m (wa (66480 + Z.shiftl (Z.shiftr c 6) 3)) 8
                  = Some (map (Z_to_bv 8) (firstn 8 (skipn (Z.to_nat (8 * (4 + Z.shiftr c 6))) FHTAB)))).
    { replace (66480 + Z.shiftl (Z.shiftr c 6) 3) with (PFI_DIDTAB + 8 * (4 + Z.shiftr c 6))
        by (unfold PFI_DIDTAB; lia).
      apply fhtab_read; [exact MI| lia]. }
    zstep. zstep. (* [comment removed for export] *)
    do 7 zstep. finish.
  - zstep. zstep. finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
