(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AllocWalkKit F_memset.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_Leaves AW_PoisonShadow AW_MmapFixed AW_SecMmap CidBits SecMsb AW_Combined AW_AllocBase AW_LargeAlloc1 AllocTacX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition large_alloc_seg3_post (sp gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo size msz a pa PS BSL nresv nch : Z) (chunks : list Z) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ra : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (a + 4096)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(a + 24, a + 32); (PS, PS + 8); (6976272, 6976281); (6976288, 6976320); (BSL, BSL + 8); (6976832, 6976833); (6976856, 6976872)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 6976264 [C8 (wz nresv); C8 (wz (nch + 1)); C8 (wz 0)]
    /\ u64arr asegs m' pa (wlist (chunks ++ [a]))
    /\ rw_cells asegs m' a [C8 (wz a); C8 (wz msz); C8 (wz size); C8 (wz nch)]
    /\ stk asegs m' 6976288 6976832
    /\ rw_cells asegs m' 6976832 [C8 (wz 0)]
    /\ stk asegs m' 6976840 6976880.

Lemma rw_cells_C4_1_bytes : forall m A cs,
  rw_cells asegs m A (C4 (Z_to_bv 64 1) :: cs) -> rw_cells asegs m A (C1 (b8 1) :: CB 3 [b8 0; b8 0; b8 0] :: cs).
Proof. intros m A cs [[[_ W] B] R]. exact (conj (conj (conj I (conj (eq_refl _) W)) B) R). Qed.
Lemma rw_cells_bytes_C4_0 : forall m A cs,
  rw_cells asegs m A (C1 (b8 0) :: CB 3 [b8 0; b8 0; b8 0] :: cs) -> rw_cells asegs m A (C4 (Z_to_bv 64 0) :: cs).
Proof. intros m A cs [[[_ [_ W]] B] R]. exact (conj (conj (conj I W) B) R). Qed.

Lemma rw_cells_C4_0_bytes : forall m A cs,
  rw_cells asegs m A (C4 (Z_to_bv 64 0) :: cs) -> rw_cells asegs m A (C1 (b8 0) :: CB 3 [b8 0; b8 0; b8 0] :: cs).
Proof. intros m A cs [[[_ W] B] R]. exact (conj (conj (conj I (conj (eq_refl _) W)) B) R). Qed.

Lemma rw_cells_C8_zero_split : forall m A cs, rw_cells asegs m A (C8 (Z_to_bv 64 0) :: cs) -> rw_cells asegs m A (C4 (Z_to_bv 64 0) :: C4 (Z_to_bv 64 0) :: cs).
Proof. intros m A cs [[[_ W] B] R]. exact (conj (conj (conj I (conj I W)) B) R). Qed.
Lemma rw_cells_C4C4_C8_zero : forall m A cs,
  rw_cells asegs m A (C4 (Z_to_bv 64 0) :: C4 (Z_to_bv 64 0) :: cs) -> rw_cells asegs m A (C8 (Z_to_bv 64 0) :: cs).
Proof. intros m A cs [[[_ [_ W]] B] R]. exact (conj (conj (conj I W) B) R). Qed.
End HCW.

Section Seg3.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (sp gp tp t0 t1 t2 a1 a2 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ra stat s4v rax : word) (j8 : list byte) (jslot : word).
  Variables (lo size msz a pa PS BSL nresv nch : Z) (chunks : list Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -96).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 416 <= bv_unsigned sp.
  Hypothesis SZ : 0x10000 < size /\ size <= 2^41. Hypothesis MSZ : size + 4096 <= msz /\ msz < size + 8192.
  Hypothesis AR : aapp a msz /\ a + msz <= aceil.
  Hypothesis PAR : aapp pa kPtrArrayReserve /\ pa + kPtrArrayReserve <= aceil.
  Hypothesis NCH : 0 <= nch < nresv /\ nresv <= 2^20. Hypothesis LEN : zlen chunks = nch.
  Hypothesis PSE : PS = pa + 8 * nch.
  Hypothesis BSLE : BSL = 6976320 + 8 * Z.log2 msz.
  Hypothesis PLC : hidden (a + msz <= pa \/ pa + kPtrArrayReserve <= a).
  Hypothesis STAT : stat = wz (AINST + 688).
  Hypothesis FR : laframe sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ra m j8.
  Hypothesis INST64 : rw_cells asegs m 6976216 [C8 (wz 4096); C8 (wz pa); C8 (wz pa)].
  Hypothesis NRES : rw_cells asegs m 6976264 [C8 (wz nresv); C8 (wz nch); C8 (wz 0)].
  Hypothesis SST : stk asegs m 6976288 6976832.
  Hypothesis MTX : rw_cells asegs m 6976832 [C4 (wz 1); C4 (wz 0)].
  Hypothesis GST : stk asegs m 6976840 6976880.
  Hypothesis PA : u64arr asegs m pa (wlist chunks).
  Hypothesis SLOT : rw_cells asegs m PS [C8 jslot].
  Hypothesis HDR : rw_cells asegs m a [C8 (wz a); C8 (wz msz); C8 (wz size)].
  Hypothesis HDR2 : stk asegs m (a + 24) (a + 4096).

  Let ARE : 12599296 <= a /\ a + msz <= aceil. Proof. exact (aapp_env _ _ (proj1 AR) ltac:(lia)). Qed.   (* [comment removed for export] *)
  Let PAE : 12599296 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; lia)). Qed.   (* [comment removed for export] *)
  Theorem large_alloc_seg3 :
    evt asegs (large_alloc_seg3_post sp gp tp s10 s11 F fc m lo size msz a pa PS BSL nresv nch chunks s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ra)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2
               stat (wz (AINST + 64)) (wz (a + 4096)) a1 a2 (wz nch) a4 a5 a6 a7
               (wz msz) (wz (clzbits msz)) s4v (wz a) (wz (a + msz)) (wz (a + 4096 + size)) (wz 7) (wz (a + 4096)) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19bb98) fc None m (seg_rom asegs)).
  Proof.
    assert (L2 : 16 <= Z.log2 msz <= 41).
    { split. - replace 16 with (Z.log2 (2^16)) by reflexivity. apply Z.log2_le_mono. lia.
      - replace 41 with (Z.log2 (2^41 + 8192)) by reflexivity. apply Z.log2_le_mono. lia. }
    pose proof (clzbits_eq msz ltac:(hci; lia)) as CLZ.
    assert (BND : aceil <= lo /\ 12599296 <= a /\ a + msz <= aceil /\ 12599296 <= pa /\ pa + 8388608 <= aceil /\ 140735332483072 <= aceil   (* [comment removed for export] *)
                 /\ pa + 8 * nch = PS /\ PS + 8 <= pa + 8388608 /\ 6976448 <= BSL /\ BSL + 8 <= 6976656).
    { unfold AHI_LO, kPtrArrayReserve in *. acb. aunf. lia. }
    assert (LENW : Z.of_nat (length (wlist chunks)) = nch) by (unfold wlist; rewrite length_map; unfold zlen in LEN; lia).
    region_sides. name_bands.
    unfold AINST in *. change (6976152 + 64) with 6976216 in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof (munch_refl [(a + 24, a + 32); (PS, PS + 8); (6976272, 6976281); (6976288, 6976320); (BSL, BSL + 8); (6976832, 6976833); (6976856, 6976872)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    unfold laframe in FR. region_table.
    subst stat. unfold wz in *. change (6976152 + 688) with 6976840 in *.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ (a + 24) (a + 32) (a + 4096) HDR2 ltac:(hci; lia)) as [HD3 HD4]. clear HDR2.
    destruct (stk_cells _ _ _ HD3 ltac:(hci; lia)) as [hj HJ]. clear HD3. replace (a + 32 - (a + 24)) with 8 in HJ by lia. change (Z.to_nat 8) with 8%nat in HJ.
    step. step. rewrite CLZ, (unsigned_lit (63 - Z.log2 msz)) by lia. rewrite lxor63_sub by lia. replace (63 - (63 - Z.log2 msz)) with (Z.log2 msz) by lia.
    st1.
    step. step. rewrite (unsigned_lit nch), Z.shiftl_mul_pow2 by lia. change (2^3) with 8. replace (pa + nch * 8) with PS by lia.
    st1.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ 6976288 6976312 6976832 SST ltac:(hci; lia)) as [SS1 SS2]. clear SST.
    destruct (stk_cells _ _ _ SS1 ltac:(hci; lia)) as [sj SJ]. clear SS1. change (Z.to_nat (6976312 - 6976288)) with 24%nat in SJ.
    apply (rw_cells_split_CB asegs _ _ [] 24 sj [] [8;8;8]%nat) in SJ; [| reflexivity]. cbn [mk_CB_cells app] in SJ.
    repeat match type of SJ with context [CB ?n (take ?k ?l)] => let J := fresh "jk" in remember (take k l) as J in SJ end.
    repeat match type of SJ with context [CB ?n (drop ?k ?l)] => let J := fresh "jk" in remember (drop k l) as J in SJ end.
    repeat match goal with H : _ = take _ _ |- _ => clear H | H : _ = drop _ _ |- _ => clear H end.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ 6976312 6976320 6976832 SS2 ltac:(hci; lia)) as [SS3 SS4]. clear SS2.
    destruct (stk_cells _ _ _ SS3 ltac:(hci; lia)) as [mj MJ]. clear SS3. change (Z.to_nat (6976320 - 6976312)) with 8%nat in MJ.
    step. step. step. step. step. step.
    (* [comment removed for export] *)
    st1.
    destruct (proj1 (rw_cells_app asegs _ 6976264 [C8 (Z_to_bv 64 nresv); C8 (Z_to_bv 64 (nch + 1))] [C8 (Z_to_bv 64 0)]) NRES) as [NRES1 SRT].
    clear NRES. cbn [cells_size csize Nat.add] in SRT. change (6976264 + Z.of_nat 16) with 6976280 in SRT.
    apply rw_cells_C8_zero_split in SRT. apply rw_cells_C4_0_bytes in SRT.
    st1. st1. st1.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ 6976320 BSL 6976832 SS4 ltac:(hci; lia)) as [SS5 SS6]. clear SS4.
    destruct (stk_split asegs _ BSL (BSL + 8) 6976832 SS6 ltac:(hci; lia)) as [SS7 SS8]. clear SS6.
    destruct (stk_cells _ _ _ SS7 ltac:(hci; lia)) as [bj BJ]. clear SS7. replace (BSL + 8 - BSL) with 8 in BJ by lia. change (Z.to_nat 8) with 8%nat in BJ.
    step. if_cases K; zify_cond K.
    2: step.
    all: clear K.
    all: step; rewrite (unsigned_lit (Z.log2 msz)), Z.shiftl_mul_pow2 by lia; change (2^3) with 8; step;
         replace (6976216 + Z.log2 msz * 8) with (BSL + -104) by lia.
    all: step.
    (* [comment removed for export] *)
    all: step; st1; st1; step.
    all: destruct (stk_split asegs _ 6976840 6976856 6976880 GST ltac:(hci; lia)) as [GS1 GS2]; clear GST;
         destruct (stk_split asegs _ 6976856 6976872 6976880 GS2 ltac:(hci; lia)) as [GS3 GS4]; clear GS2;
         destruct (stk_cells _ _ _ GS3 ltac:(hci; lia)) as [gj GJ]; clear GS3; change (Z.to_nat (6976872 - 6976856)) with 16%nat in GJ;
         apply (rw_cells_split_CB asegs _ _ [] 16 gj [] [8;8]%nat) in GJ; [| reflexivity]; cbn [mk_CB_cells app] in GJ;
         repeat match type of GJ with context [CB ?n (take ?k ?l)] => let J := fresh "jk" in remember (take k l) as J in GJ end;
         repeat match type of GJ with context [CB ?n (drop ?k ?l)] => let J := fresh "jk" in remember (drop k l) as J in GJ end;
         repeat match goal with H : _ = take _ _ |- _ => clear H | H : _ = drop _ _ |- _ => clear H end.
    all: assert (GA1 : 6976856 mod 8 = 0) by reflexivity; assert (GR1 : 0 <= 6976856 < 2^64) by lia;
         assert (GA2 : 6976864 mod 8 = 0) by reflexivity; assert (GR2 : 0 <= 6976864 < 2^64) by lia.
    all: astep.
    all: step; astep.
    (* [comment removed for export] *)
    all: step; apply rw_cells_C4_1_bytes in MTX; st1; apply rw_cells_bytes_C4_0 in MTX; apply rw_cells_C4C4_C8_zero in MTX.
    (* [comment removed for export] *)
    all: do 11 step.
    all: step; step.
    all: release_frame FR ST (bv_unsigned sp).
    (* [comment removed for export] *)
    all: apply rw_cells_bytes_C4_0 in SRT; apply rw_cells_C4C4_C8_zero in SRT;
         pose proof (proj2 (rw_cells_app asegs _ 6976264 [C8 (Z_to_bv 64 nresv); C8 (Z_to_bv 64 (nch + 1))] [C8 (Z_to_bv 64 0)])
                       (conj NRES1 SRT)) as NRES'; cbn [app] in NRES'; clear NRES1 SRT.
    all: pose proof (proj2 (rw_cells_app asegs _ a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 msz); C8 (Z_to_bv 64 size)] [C8 (Z_to_bv 64 nch)])
                       (conj HDR ltac:(hci; cbn [cells_size csize Nat.add]; replace (a + Z.of_nat 24) with (a + 24) by lia; exact HJ))) as HDR';
         cbn [app] in HDR'; clear HDR HJ.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
           assert (PA' : u64arr asegs mc pa (wlist (chunks ++ [a])))
           by (unfold wlist, wz; rewrite map_app; cbn [map]; apply (proj2 (u64arr_snoc asegs _ _ _ _));
               split; [exact PA| rewrite length_map; replace (pa + 8 * Z.of_nat (length chunks)) with PS by (unfold zlen in LEN; lia); exact SLOT]) end.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
           pose proof (stk_of_rw_cells _ _ _ _ SJ) as Q1; pose proof (stk_of_rw_cells _ _ _ _ MJ) as Q2; pose proof (stk_of_rw_cells _ _ _ _ BJ) as Q3;
           pose proof (stk_of_rw_cells _ _ _ _ GJ) as Q4;
           cbn [cells_size csize Nat.add] in Q1, Q2, Q3, Q4;
           change (6976288 + Z.of_nat 24) with 6976312 in Q1; change (6976312 + Z.of_nat 8) with 6976320 in Q2;
           replace (BSL + Z.of_nat 8) with (BSL + 8) in Q3 by lia; change (6976856 + Z.of_nat 16) with 6976872 in Q4;
           assert (SST' : stk asegs mc 6976288 6976832)
             by (eapply stk_merge; [exact Q1| eapply stk_merge; [exact Q2| eapply stk_merge; [exact SS5| eapply stk_merge; [exact Q3| exact SS8| lia]| lia]| lia]| lia]);
           assert (GST' : stk asegs mc 6976840 6976880)
             by (eapply stk_merge; [exact GS1| eapply stk_merge; [exact Q4| exact GS4| lia]| lia]);
           clear Q1 Q2 Q3 Q4 SJ MJ BJ GJ SS5 SS8 GS1 GS4 end.
    all: apply evt_done; unfold large_alloc_seg3_post; do 14 eexists; eexists;
         split; [reflexivity|]; split; [exact MU|]; split; [exact WM|];
         repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.
End Seg3.

