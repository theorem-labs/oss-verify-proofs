(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import DrvAgree Startup_kit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX F_syscalls StdioFiles Startup F_atexit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation pph := UImg.u_phdrs.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma implM_of_enode : forall {A} (n : node) (pl : resp -> option A) (P : A -> machine_state -> Prop) (s : PState) ms,
impl usegs (at_node usegs) (enode n pl) (epost P) ms ->
implM usegs (msys n pl) s (fun a s' ms' => P a ms' /\ s' = s) ms.
Proof.
intros A n pl P s ms H. unfold implM, msys, enode in *. cbn in *.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn in *; [|exact Hk].
eapply evt_mono; [exact Hk|]. intros ms2 HQ. cbn. auto.
Qed.
Section Pieces.
Variables (sp : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (m : mem).
Notation usp := (bv_unsigned sp).
Hypothesis IMG : bytes_at usegs m usp (build_stack_bytes pph sp argv envp uid hw draw).
#[using="IMG"] Lemma stack_pieces :
bytes_at usegs m usp (le8 (Z_to_bv 64 (argc argv))) /\
bytes_at usegs m (usp + 8) (u64s (argv_ptrs sp argv envp ++ [Z_to_bv 64 0])) /\
bytes_at usegs m (usp + 8 * (argc argv + 2)) (u64s (envp_ptrs sp argv envp ++ [Z_to_bv 64 0])) /\
bytes_at usegs m (usp + 8 * (argc argv + envc envp + 3)) (u64s (auxv_words pph sp argv envp uid hw)) /\
bytes_at usegs m (str_base sp argv envp) (flatten_strings argv) /\
bytes_at usegs m (env_base sp argv envp) (flatten_strings envp) /\
bytes_at usegs m (rnd_addr sp argv envp) (rnd_bytes draw).
Proof.
pose proof IMG as B. rewrite build_stack_bytes_eq in B.
unfold raw_bytes in B. remember (auxv_words pph sp argv envp uid hw) as AW eqn:EAW. cbn [u64s app] in B.
rewrite u64s_app in B. cbn [u64s app] in B. rewrite u64s_app in B. cbn [u64s app] in B.
repeat rewrite <- app_assoc in B. cbn [app] in B.
pose proof (raw_len_nonneg argv envp) as RN.
pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
apply bytes_at_app in B. destruct B as [B0 B]. rewrite length_le8 in B.
apply bytes_at_app in B. destruct B as [B1 B]. rewrite u64s_length in B. unfold argv_ptrs in B. rewrite map_length, str_ptrs_length in B.
apply bytes_at_app in B. destruct B as [B2 B]. rewrite length_le8 in B.
apply bytes_at_app in B. destruct B as [B3 B]. rewrite u64s_length in B. unfold envp_ptrs in B. rewrite map_length, str_ptrs_length in B.
apply bytes_at_app in B. destruct B as [B4 B]. rewrite length_le8 in B.
apply bytes_at_app in B. destruct B as [B5 B]. rewrite u64s_length in B. replace (length AW) with 20%nat in B by (subst AW; reflexivity).
apply bytes_at_app in B. destruct B as [B6 B].
apply bytes_at_app in B. destruct B as [B7 B].
apply bytes_at_app in B. destruct B as [B8 B]. rewrite repeat_length in B.
repeat match goal with |- _ /\ _ => split end.
- exact B0.
- rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app usegs m _ _ _)). split; [exact B1|].
rewrite u64s_length. unfold argv_ptrs at 1. rewrite map_length, str_ptrs_length.
Local Ltac2 Set LiaHints.tbl := fun () => "0060>13456465564.2435523325713.2444921921024.2457630657688.2461608112175.2462905188850.2400000100200600700A00BSSS2L1SS2RN2L12L2S".
replace (usp + 8 + Z.of_nat (8 * length argv))%Z with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv))%Z by lia. exact B2.
- rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app usegs m _ _ _)). split.
+ replace (usp + 8 * (argc argv + 2))%Z with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8)%Z by (unfold argc; lia). exact B3.
+ rewrite u64s_length. unfold envp_ptrs at 1. rewrite map_length, str_ptrs_length.
replace (usp + 8 * (argc argv + 2) + Z.of_nat (8 * length envp))%Z
with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp))%Z by (unfold argc; lia). exact B4.
- replace (usp + 8 * (argc argv + envc envp + 3))%Z
with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8)%Z by (unfold argc, envc; lia). exact B5.
- replace (str_base sp argv envp) with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8 + Z.of_nat (8 * 20))%Z
by (unfold str_base, struct_size, argc, envc; lia). exact B6.
- replace (env_base sp argv envp) with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8 + Z.of_nat (8 * 20) + Z.of_nat (length (flatten_strings argv)))%Z
by (unfold env_base, str_base, struct_size, argc, envc; lia). exact B7.
- replace (rnd_addr sp argv envp) with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8 + Z.of_nat (8 * 20)
+ Z.of_nat (length (flatten_strings argv)) + Z.of_nat (length (flatten_strings envp)) + Z.of_nat (Z.to_nat (pad_len argv envp)))%Z
by (unfold rnd_addr, raw_len, struct_size, argc, envc; lia). exact B.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="IMG"] Lemma argv_cstring : forall i s, nth_error argv i = Some s -> usp mod 8 = 0 ->
exists p slack, nth_error (argv_ptrs sp argv envp) i = Some (Z_to_bv 64 p) /\ str_base sp argv envp <= p /\
p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= usp + Z.of_nat (length (build_stack_bytes pph sp argv envp uid hw draw)) /\
bytes_at usegs m p (s ++ Z_to_bv 8 0 :: slack) /\
(- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack).
Proof.
intros i s Hn AL. destruct (str_ptrs_nth argv (str_base sp argv envp) i s Hn) as (off & Hp & Ho & Ht & Hf).
pose proof (raw_len_nonneg argv envp) as RN. pose proof (build_stack_bytes_length pph sp argv envp uid hw draw) as BL.
pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
set (p := str_base sp argv envp + off).
set (e := p + Z.of_nat (length s) + 1).
set (k := (- e) mod 8).
Local Ltac2 Set LiaHints.tbl := fun () => "00<0>12193207191.2813140445951.2316552917612.2817487635879.2932382291344.2336955936750.2739193773425.2940170709087.3057983930333.3063373880569.24638956421.26  66149329423.5800000400>00I00P00W00\00i01101<01=01A01TS2LSS2Ht2RN2L2S2HK3OFF2LSS2Ho2LSS2Ho2RNS3OFFS2Ho2Ht2L12LSS3OFF2LSS2HK3OFF2LSSS2HoS2AL1H2H02H42H93H19".
assert (HK : 0 <= k < 8) by (subst k; apply Z.mod_pos_bound; lia).
assert (OFF : usp <= p /\ e + k <= usp + Z.of_nat (length (build_stack_bytes pph sp argv envp uid hw draw))).
{ subst p e k. unfold str_base, struct_size, raw_len in *. split; [lia|].
rewrite BL. apply ceil8_le.
- unfold pad_len, raw_len, struct_size. Z.div_mod_to_equations. lia.
- unfold raw_len, struct_size. lia. }
exists p, (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) (build_stack_bytes pph sp argv envp uid hw draw))).
split; [unfold argv_ptrs; rewrite nth_error_map, Hp; reflexivity|]. split; [subst p; lia|].
assert (LS : length (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) (build_stack_bytes pph sp argv envp uid hw draw))) = Z.to_nat k).
{ rewrite length_firstn, length_skipn. lia. }
rewrite LS. split; [lia|]. split; [| lia].
destruct stack_pieces as (_ & _ & _ & _ & B6 & _).
pose proof (bytes_at_slice usegs pph sp argv envp uid hw draw m (str_base sp argv envp) (flatten_strings argv) (Z.to_nat off) (length s + 1) B6 ltac:(lia)) as BS.
rewrite Hf in BS. replace (str_base sp argv envp + Z.of_nat (Z.to_nat off)) with p in BS by (subst p; lia).
pose proof (bytes_at_slice usegs pph sp argv envp uid hw draw m usp (build_stack_bytes pph sp argv envp uid hw draw) (Z.to_nat (e - usp)) (Z.to_nat k) IMG ltac:(lia)) as BK.
replace (usp + Z.of_nat (Z.to_nat (e - usp))) with (p + Z.of_nat (length (s ++ [Z_to_bv 8 0]))) in BK by (rewrite length_app; cbn [length]; subst e; lia).
pose proof (proj2 (bytes_at_app usegs m p _ _) (conj BS BK)) as BB. rewrite <- app_assoc in BB. cbn [app] in BB. exact BB.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Pieces.
End CANSEC1.
Ltac pimg_chunk0 NONE m A cs H :=
let bs := eval vm_compute in (cells_bytes cs) in
assert (H : rw_cells usegs m A cs);
[ apply (InitMem.rw_cells_recast usegs m A [CB (length bs) bs] cs);
[ apply (InitMem.rw_cells_image0 usegs m A bs);
[ intros a Ha; cbn [length] in Ha; apply NONE; [lia| cbn [outside pcrt_written]; lia] | vm_compute; reflexivity | lia | cbn [length]; lia ]
| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
| ].
Section CANSEC2. Context {rc : runConstT}.
Section InitFacts.
Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (m : mem).
Notation usp0 := (bv_unsigned sp0).
Hypothesis NONE : forall a : word, (0x1d000 <= bv_unsigned a < 0x50000)%Z -> outside (pcrt_written) (bv_unsigned a) -> m a = None.
Hypothesis LIBC1 : rw_cells usegs m 0x4f1c0 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)].
Hypothesis LIBC2 : rw_cells usegs m 0x4f1c8 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)].
Hypothesis GOTG : rw_cells usegs m 0x1dbb0 [C8 (Z_to_bv 64 0x4f1a0)].
Hypothesis GUARD : rw_cells usegs m 0x4f1a0 [C8 CAN].
Hypothesis MI : mem_inv usegs m.
Hypothesis IMG : bytes_at usegs m usp0 (build_stack_bytes pph sp0 argv envp uid hw draw).
Hypothesis SPLO : sp_window_lo <= usp0.
Hypothesis HSEC : SECRET = InitMem.draw_secret draw.
Hypothesis HATOP : ATOP = usp0 - 8388608.
#[using="NONE LIBC1 LIBC2 GOTG GUARD MI"] Lemma heap_init : RHEAP (ps_init (reservedZ usegs) ATOP) [] m /\ rw_cells usegs m RAUXV_CELL [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp))].
Proof.
apply RMalloc_ifaceP.RHEAP_init_proof; [| exact LIBC1| exact LIBC2| exact GOTG| exact GUARD| exact MI].
intros a Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0020>45263069469.218791590957.21 000004008S2HaS2Ha".
apply NONE; [lia|]. unfold pcrt_written. cbn. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="argv envp uid hw draw NONE LIBC1 LIBC2 GOTG GUARD MI IMG HSEC HATOP"] Lemma rauxv_ok_init : rauxv_ok m usp0.
Proof.
destruct (stack_pieces sp0 argv envp uid hw draw m IMG) as (_ & _ & _ & AUXW & _ & _ & RND).
pose proof (build_stack_bytes_length pph sp0 argv envp uid hw draw) as BL. pose proof (raw_len_nonneg argv envp) as RLN.
pose proof (bytes_at_bound _ _ _ _ IMG) as IB. unfold sp_window_lo in SPLO.
pose proof (bv_unsigned_in_range 64 uid) as RU. unfold bv_modulus in RU. cbn in RU.
pose proof (bv_unsigned_in_range 64 hw) as RH. unfold bv_modulus in RH. cbn in RH.
atop_facts.
exists (auxv_addr sp0 argv envp), (Z.of_N (ph_addr pph)), (Z.of_N (ph_ent pph)), (Z.of_N (ph_num pph)), (bv_unsigned hw), 4096, (bv_unsigned uid), (bv_unsigned uid), 0, (rnd_addr sp0 argv envp).
split; [apply (proj2 heap_init)|].
split. { unfold auxv_addr. replace (rauxv_list _ _ _ _ _ _ _ _ _) with (auxv_words pph sp0 argv envp uid hw); [exact AUXW|].
unfold rauxv_list, auxv_words. cbn [map]. unfold wz. rewrite !Z_to_bv_bv_unsigned. reflexivity. }
split. { rewrite rnd_bytes_split in RND. apply bytes_at_app in RND. destruct RND as [_ R]. rewrite length_le8 in R.
rewrite HSEC. unfold wz. exact R. }
unfold auxv_addr, rnd_addr, raw_len, struct_size, argc, envc, sp_window_lo, stack_max_size in *.
pose proof (flatten_strings_length argv). pose proof (flatten_strings_length envp).
Local Ltac2 Set LiaHints.tbl := fun () => "00>0>10122503303.2815045117442.2816680732231.2818928845742.2827950873319.2831290183736.2831794499664.2835598384055.2842664638542.2848048716802.2853124814311.2853765666882.2868362714949.288901798543.28 00000400500?00@00G00N00R00V00]00a01101201301IS2RUSS3RLN1H2H0SS2BL2IBS5HATOPS2RHS2RHS2BL2IBS2RUS2BL3RLN2IB1H2H0SSS5HATOP3RLN5ATOPR1H2H0".
repeat split; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc NONE"] Lemma stage_init : STG m.
Proof.
exists (repeat (Z_to_bv 8 0) PSTAGE_LEN). unfold UREAD_STAGE.
Local Ltac2 Set LiaHints.tbl := fun () => "0070>18934757900.2118934757900.2318939196172.1945259155485.2359640509922.218795537709.23 9385721756.21 00000100200300700800<00=SSSS2HaSS2HaS".
assert (E : PSTAGE_LEN = Z.to_nat 65536) by (apply Nat2Z.inj; rewrite PSTAGE_LEN_Z, Z2Nat.id by lia; reflexivity).
rewrite E. replace (Z.to_nat 65536) with (length (repeat (Z_to_bv 8 0) (Z.to_nat 65536))) at 1 by (rewrite repeat_length; reflexivity).
apply (InitMem.rw_cells_image0 usegs m).
- intros a Ha. rewrite repeat_length, Z2Nat.id in Ha by lia. apply NONE; [lia| cbn [outside pcrt_written]; lia].
- vm_compute. reflexivity.
- lia.
- rewrite repeat_length, Z2Nat.id by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc NONE"] Lemma atx_state0_init : atx_state false m.
Proof.
unfold atx_state, atx_cells, PATX, PAEF_INCB. cbn [Z.add].
Local Ltac2 Set LiaHints.tbl := fun () => "00P0>10281681175.2415115125335.2619108561676.2142225966732.2542350063895.2542702687884.2445263069469.2145263069469.2245263069469.2345263069469.2445263069469.2545263069469.2645263069469.2745263069469.2845572422220.264841972887.21 4901350092.20 49735790551.2051084331148.1952451425815.2253509059351.1958967646103.2364192038796.2266321910284.238791590957.21 8791590957.22 8791590957.23 8791590957.24 8791590957.25 8791590957.26 8791590957.27 8791590957.28 00000100200300400500600:00>00B00F00J00N00R00V00W00X00Y00Z00[00\00]00^00_00`00d00h00l01001401801<01@SSSSSSS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaSSSSSSSSSSS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2Ha".
pimg_chunk0 NONE m 0x4ef78 [C1 (Z_to_bv 8 0)] X1.
pimg_chunk0 NONE m 0x4ef7c [C4 (Z_to_bv 64 0)] X2.
pimg_chunk0 NONE m 0x4ef80 [C4 (Z_to_bv 64 0)] X3.
pimg_chunk0 NONE m 0x4ef88 [C8 (Z_to_bv 64 0)] X4.
pimg_chunk0 NONE m 0x4ef90 [C8 (Z_to_bv 64 0)] X5.
pimg_chunk0 NONE m 0x4ef98 [C8 (Z_to_bv 64 0)] X6.
pimg_chunk0 NONE m 0x4f098 [C8 (Z_to_bv 64 0)] X7.
pimg_chunk0 NONE m 0x2ee34 [C1 (Z_to_bv 8 0)] X8.
repeat match goal with |- _ /\ _ => split end; assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc NONE"] Lemma rstatx0_init : rw_cells usegs m 0x1ebc8 [C8 (Z_to_bv 64 0x1ebc8)] /\ (exists reg : bool, atx_state reg m).
Proof.
pimg_chunk0 NONE m 0x1ebc8 [C8 (Z_to_bv 64 0x1ebc8)] D1.
split; [exact D1| exists false; apply atx_state0_init].
Qed.
#[using="rc NONE"] Lemma trun_cells0_init : trun_cells0 m.
Proof.
unfold trun_cells0, PINIT_FLAG, PGOT_FUZZ_INIT, PFUZZ_INIT, PGOT_STDERR, PSTDERR_PTR, wz.
Local Ltac2 Set LiaHints.tbl := fun () => "00@0>16809312396.2018888398231.1923019149324.1940428538892.2140910539159.2144686254348.2245263069469.2145263069469.2245263069469.2345263069469.244547342999.22 47401593623.208791590957.21 8791590957.22 8791590957.23 8791590957.24 00000100200300400500600:00>00B00F00G00H00L00P00T00XSSSSSSS2HaS2HaS2HaS2HaSSS2HaS2HaS2HaS2Ha".
pimg_chunk0 NONE m 0x2ee30 [C1 (Z_to_bv 8 0)] H1.
pimg_chunk0 NONE m 0x1db78 [C8 (Z_to_bv 64 0)] H2.
pimg_chunk0 NONE m 0x1db70 [C8 (Z_to_bv 64 0x1db20)] H7.
pimg_chunk0 NONE m 0x1db20 [C8 (Z_to_bv 64 0x1ebf0)] H8.
pose proof atx_state0_init as AX0.
repeat match goal with |- _ /\ _ => split end; assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc NONE"] Lemma stderr_file0_init : stderr_file0 m.
Proof.
unfold stderr_file0, file_cells, wz.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>45263069469.2147011713431.195984154636.19 8791590957.21 00000400500600:S2HaSSS2Ha".
pimg_chunk0 NONE m 0x1ebf0%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x17538 0x4f600 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)) H.
unfold file_cells in H. exact H.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End InitFacts.
#[using="Type"] Lemma le4_of_bytes : forall b0 b1 b2 b3 : byte, exists w : word, le4 w = [b0; b1; b2; b3].
Proof.
intros b0 b1 b2 b3.
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
unfold bv_modulus in R0, R1, R2, R3. cbn in R0, R1, R2, R3.
set (v := bv_unsigned b0 + 2^8 * bv_unsigned b1 + 2^16 * bv_unsigned b2 + 2^24 * bv_unsigned b3).
exists (Z_to_bv 64 v). unfold le4. rewrite Z_to_bv_unsigned.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>16039682215.9 29442577268.1137865589167.1163368328200.119311361852.11 00000=00A00B00C00DS2R02R12R22R3S2HVSSS".
assert (HV : 0 <= v < 2^32) by (subst v; lia).
replace (bv_wrap 64 v) with v by (unfold bv_wrap, bv_modulus; rewrite Z.mod_small; [reflexivity|]; cbn; lia).
cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add].
rewrite !Z.shiftr_div_pow2 by lia.
assert (E0 : Z_to_bv 8 v = b0).
{ apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.mul Z.of_N]. subst v. Z.div_mod_to_equations. nia. }
assert (E1 : Z_to_bv 8 (v / 2^8) = b1).
{ apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.mul Z.of_N]. subst v. Z.div_mod_to_equations. nia. }
assert (E2 : Z_to_bv 8 (v / 2^16) = b2).
{ apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.mul Z.of_N]. subst v. Z.div_mod_to_equations. nia. }
assert (E3 : Z_to_bv 8 (v / 2^24) = b3).
{ apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.mul Z.of_N]. subst v. Z.div_mod_to_equations. nia. }
rewrite E0, E1, E2, E3. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma libc_head_byte : forall (m : mem) (a : Z), 0x4f1c0 <= a < 0x4f1c8 ->
exists b : byte, mrd usegs m (wa a) = Some b /\ wview usegs m (wa a) <> None.
Proof.
intros m a Ha.
assert (IMG : exists b0, seg_rom usegs (wa a) = Some b0 /\ wview usegs (fun _ => None) (wa a) <> None).
{ Local Ltac2 Set LiaHints.tbl := fun () => "0010=10448594162.4000004S2Ha".
assert (E : a = 0x4f1c0 \/ a = 0x4f1c1 \/ a = 0x4f1c2 \/ a = 0x4f1c3 \/ a = 0x4f1c4 \/ a = 0x4f1c5 \/ a = 0x4f1c6 \/ a = 0x4f1c7) by lia.
destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; (eexists; split; [vm_compute; reflexivity| vm_compute; discriminate]). }
destruct IMG as (b0 & SR & WV).
destruct (m (wa a)) as [b|] eqn:E.
- exists b. split; [unfold mrd; rewrite E; reflexivity|]. unfold wview. rewrite E. discriminate.
- exists b0. split; [unfold mrd; rewrite E; exact SR|]. unfold wview in *. rewrite E. exact WV.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma RHEAP_libc_head : forall s LB m, RHEAP s LB m ->
exists (cdt thr sec : byte) (tm1 : word),
rw_cells usegs m 0x4f1c0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
Proof.
intros s LB m (st & LB0 & _ & _ & MREP & _).
destruct MREP as (_ & _ & (_ & NL & _) & _).
Local Ltac2 Set LiaHints.tbl := fun () => "00G0>10382249147.3412686012388.1313604614334.3415680004686.3522766053480.3527946767981.3432807390947.1935993367851.3337511955296.2239596678079.3439734296475.7 40806832971.3443480110125.3444282701794.3445411093168.3351412661265.3454466274937.3455409538213.1655684169784.316892186215.10 737057864.34  7449913633.25 8892637969.32 00000100200300700;00<00=00>00?00@00A00B00C00D00E00F00G00H00I00J00K00L00MSSFS2HiS2HiFSSSFSFSFSFFSSSFSS".
destruct (libc_head_byte m 0x4f1c0 ltac:(lia)) as (b0 & R0 & W0).
destruct (libc_head_byte m 0x4f1c1 ltac:(lia)) as (b1 & R1 & W1).
destruct (libc_head_byte m 0x4f1c2 ltac:(lia)) as (b2 & R2 & W2).
destruct (libc_head_byte m 0x4f1c4 ltac:(lia)) as (b4 & R4 & W4).
destruct (libc_head_byte m 0x4f1c5 ltac:(lia)) as (b5 & R5 & W5).
destruct (libc_head_byte m 0x4f1c6 ltac:(lia)) as (b6 & R6 & W6).
destruct (libc_head_byte m 0x4f1c7 ltac:(lia)) as (b7 & R7 & W7).
destruct (le4_of_bytes b4 b5 b6 b7) as [tm1 Htm].
destruct NL as [[_ NLB] NLW]. unfold RNEED_LOCKS in NLB, NLW.
pose proof (proj2 (proj2 NLB) 0%nat ltac:(cbn; lia)) as R3. cbn [cells_bytes cbytes app nth_error b8 MallocRep.b8] in R3.
pose proof (proj2 (proj2 NLW) 0 ltac:(cbn; lia)) as W3.
exists b0, b1, b2, tm1. split; [split|].
- cbn. repeat split; exact I.
- cbn [cells_bytes cbytes app]. rewrite Htm. cbn [app]. split; [lia|]. split; [cbn; lia|].
intros i Hi. cbn [length] in Hi.
destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ]; try lia.
+ exact R0. + exact R1. + exact R2.
+ replace (0x4f1c0 + 3) with (0x4f1c3 + Z.of_nat 0) by lia. exact R3.
+ exact R4. + exact R5. + exact R6. + exact R7.
- cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|].
intros i Hi.
assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; cbn [Z.add].
+ exact W0. + exact W1. + exact W2.
+ replace (0x4f1c0 + 3) with (0x4f1c3 + 0) by lia. exact W3.
+ exact W4. + exact W5. + exact W6. + exact W7.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma RHEAP_need_locks : forall s LB m, RHEAP s LB m -> rw_cells usegs m PNEED_LOCKS [C1 (Z_to_bv 8 0)].
Proof.
intros s LB m (st & LB0 & _ & _ & MREP & _). destruct MREP as (_ & _ & (_ & NL & _) & _).
unfold PNEED_LOCKS. unfold RNEED_LOCKS in NL. exact NL.
Qed.
#[using="Type"] Lemma RHEAP_ssp : forall s LB m, RHEAP s LB m -> ssp_cells m CAN.
Proof.
intros s LB m (st & LB0 & _ & _ & MREP & _). destruct MREP as (_ & _ & (_ & _ & _ & G1 & G2) & _).
unfold ssp_cells, got_ssp, ssp_guard. unfold RGOT_SSP, RSSP_GUARD in G1, G2. split; [exact G1| exact G2].
Qed.
End CANSEC2.
