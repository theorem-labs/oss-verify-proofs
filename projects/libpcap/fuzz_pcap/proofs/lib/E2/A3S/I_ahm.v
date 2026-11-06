(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ZBridge Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells ShadowTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lrsc_stepS AMO :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply (evtF_step_acc segs RNG);
      [ reflexivity
      | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; simp_is_x0; simp_regs; amo_align AMO; rewrite ?Z.eqb_refl; exec_cbv; amo_align AMO; rewrite ?Z.eqb_refl;
        simp_is_x0; simp_regs; vnorm_tail;
        try solve_load; try solve_store; reflexivity
      | solve_accs
      | simp_regs; vnorm_tail; mem_after_store_opt ]
    end end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AHM_SIZE : Z := 31051.
Definition AHM_MAGIC : Z := 0x8713f185cccd38dd.     (* [comment removed for export] *)
Definition ahm_h1 (a : Z) : Z := (a * 1024 + a) mod 2^64.
Definition ahm_hash (a : Z) : Z := Z.lxor (Z.shiftr (ahm_h1 a) 6) (ahm_h1 a).
Definition ahm_idx (a : Z) : Z := ahm_hash a mod AHM_SIZE.
Definition AHM_BUCKET : Z := 120.
Definition AHM_BYTES : Z := 3727360.                  (* [comment removed for export] *)

Definition ahm_magic__stmt : Prop := forall a, 0 <= a < 2^64 -> (a * AHM_MAGIC) / 2^78 = a / 31051.
Section Sz1.
Variables a : ltac2:(SecDiet.SzSec.tyM 'ahm_magic__stmt "v" @a).
#[using="Type"] Lemma ahm_magic__body : ltac2:(SecDiet.SzSec.bodyP 'ahm_magic__stmt "v").
Proof.
  intros Ha.
 symmetry. unfold AHM_MAGIC.
  pose proof (Z.div_mod a 31051 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound a 31051 ltac:(lia)) as MB.
  assert (QB : 0 <= a / 31051 <= 2^64 / 31051) by (split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]).
  assert (E64 : 2^64 / 31051 = 594078904824628) by (vm_compute; reflexivity). rewrite E64 in QB. clear E64.
  apply Z.div_unique with (r := (a / 31051) * 7615 + (a mod 31051) * 0x8713f185cccd38dd); [lia|].
  change (2^78) with 302231454903657293676544. lia.
Qed.
End Sz1.
Lemma ahm_magic : ltac:(let t := eval cbv delta [ahm_magic__stmt] in ahm_magic__stmt in exact t).
Proof. intros a. ltac2:(SecDiet.SzSec.closeP 'ahm_magic__body "v"). Qed.

Lemma ahm_hash_range : forall a, 0 <= ahm_hash a < 2^64.
Proof.
  intros a. unfold ahm_hash, ahm_h1. pose proof (Z.mod_pos_bound (a * 1024 + a) (2^64) ltac:(lia)) as R.
  apply (zr_lxor _ _); [apply zr_shiftr; [exact R | lia] | exact R].
Qed.

Lemma ahm_idx_range : forall a, 0 <= ahm_idx a < 31051.
Proof. intros a. unfold ahm_idx, AHM_SIZE. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
Definition ahm_bucket_off__stmt : Prop := forall h, 0 <= h < 2^64 ->
  Z.shiftl ((h - (Z.shiftr (Z.shiftr (h * 9733388776646719709) 64 mod 18446744073709551616) 14 * 31051) mod 18446744073709551616) mod 18446744073709551616) 7 mod 18446744073709551616
  - Z.shiftl ((h - (Z.shiftr (Z.shiftr (h * 9733388776646719709) 64 mod 18446744073709551616) 14 * 31051) mod 18446744073709551616) mod 18446744073709551616) 3 mod 18446744073709551616
  = 120 * (h mod 31051).
Section Sz4.
Variables h : ltac2:(SecDiet.SzSec.tyM 'ahm_bucket_off__stmt "v" @h).
#[using="Type"] Lemma ahm_bucket_off__body : ltac2:(SecDiet.SzSec.bodyP 'ahm_bucket_off__stmt "v").
Proof.
  intros Hh.
  assert (Q : Z.shiftr (Z.shiftr (h * 9733388776646719709) 64 mod 18446744073709551616) 14 = h / 31051).
  { rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.mod_small.
    - rewrite Z.div_div by lia. change (2^64 * 2^14) with (2^78). apply (ahm_magic h Hh).
    - split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. lia. }
  rewrite Q.
  pose proof (Z.div_mod h 31051 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound h 31051 ltac:(lia)) as MB.
  assert (QB : 0 <= h / 31051) by (apply Z.div_pos; lia).
  rewrite (Z.mod_small (h / 31051 * 31051)) by lia.
  replace (h - h / 31051 * 31051) with (h mod 31051) by lia.
  rewrite (Z.mod_small (h mod 31051)) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia. rewrite !Z.mod_small by lia. lia.
Qed.
End Sz4.
Lemma ahm_bucket_off : ltac:(let t := eval cbv delta [ahm_bucket_off__stmt] in ahm_bucket_off__stmt in exact t).
Proof. intros h. ltac2:(SecDiet.SzSec.closeP 'ahm_bucket_off__body "v"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition ahm_bucket0 : list cell :=
  [C8 (Z_to_bv 64 0); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0); CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0); CB 24 (repeat (Z_to_bv 8 0) 24)].

(* [comment removed for export] *)
Definition ahm_handle (mapw bkt cellw : word) (fp : Z) (idxw : word) (created : byte) (rest : list byte) : list cell :=
  [C8 mapw; C8 bkt; C8 cellw; C8 (Z_to_bv 64 fp); C8 idxw; C1 created; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 5 rest].

Definition ahm_acquire_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo H BKT fp : Z) (mapw : word) (rest : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp); (H, H + 48); (BKT, BKT + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' H (ahm_handle mapw (Z_to_bv 64 BKT) (Z_to_bv 64 0) fp (Z_to_bv 64 4294967295) (Z_to_bv 8 0) rest)
    /\ rw_cells asegs m' BKT ahm_bucket0.

Definition ahm_acquire_miss_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo MAP TABLE H fp : Z) (mapw bkt0 cell0 idx0 : word) (cr0 : byte) (rest : list byte),
  let BKT := TABLE + 120 * ahm_idx fp in
  a0 = Z_to_bv 64 MAP -> a1 = Z_to_bv 64 H ->
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 ->
  rw_cells asegs m MAP [C8 (Z_to_bv 64 TABLE)] ->
  rw_cells asegs m H (ahm_handle mapw bkt0 cell0 fp idx0 cr0 rest) ->
  rw_cells asegs m BKT ahm_bucket0 ->
  0 < fp < 2^64 -> TABLE mod 8 = 0 -> 0x603000 <= TABLE -> TABLE + AHM_BYTES <= lo ->
  0x10000 <= MAP -> MAP + 8 <= 0x603000 -> 0x603000 <= lo ->
  bv_unsigned sp <= H -> H + 48 <= 2^63 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG H 48 -> rng RNG BKT 120 ->
  evtF asegs RNG (ahm_acquire_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo H BKT fp mapw rest m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4af78) fc None m (seg_rom asegs)).
Section Sz5.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo MAP TABLE H fp mapw bkt0 cell0 idx0 cr0 rest : ltac2:(SecDiet.SzSec.tyM 'ahm_acquire_miss_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma ahm_acquire_miss_spec__body : ltac2:(SecDiet.SzSec.bodyP 'ahm_acquire_miss_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros BKT -> -> MI ST LO MAPC HC BC FP TAL TLO THI MLO MHI GLO HLO HHI RIMG RSTK RH RB.
  pose proof (ahm_idx_range fp) as IDX. pose proof (ahm_hash_range fp) as HR.
  assert (BR : TABLE <= BKT /\ BKT + 120 <= TABLE + AHM_BYTES /\ BKT mod 8 = 0).
  { subst BKT. unfold AHM_BYTES. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. }
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp); (H, H + 48); (BKT, BKT + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold ahm_handle, ahm_bucket0 in *. unfold AHM_BYTES in *.
  carve_frame 176%nat ST.
  (* [comment removed for export] *)
  lazymatch goal with
  | FRx : rw_cells asegs m ?A [CB 176 ?j] |- _ =>
      apply (rw_cells_split_CB asegs m A [] 176 j [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx;
        [ | reflexivity ];
      cbn [app mk_CB_cells] in FRx;
      repeat match type of FRx with
      | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
      end
  end.
  do 14 zstep. do 8 zstep. do 3 zstep. do 22 zstep.
  replace (Z.lxor (Z.shiftr ((Z.shiftl fp 10 + fp) mod 18446744073709551616) 6) ((Z.shiftl fp 10 + fp) mod 18446744073709551616)) with (ahm_hash fp)
    by (unfold ahm_hash, ahm_h1; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  do 8 zstep.
  rewrite (ahm_bucket_off (ahm_hash fp) HR). change (ahm_hash fp mod 31051) with (ahm_idx fp). fold BKT.
  (* [comment removed for export] *)
  do 4 zstep. do 13 zstep. zstep. if_false.
  zstep. zstep. if_false.
  (* [comment removed for export] *)
  zstep. zstep. zstep. if_cases K; zify_cond K. { exfalso. clear -K FP. lia. } clear K.
  zstep. zstep. zstep. if_cases K; zify_cond K. { exfalso. clear -K FP. lia. } clear K.
  zstep. zstep. zstep. if_cases K; zify_cond K. { exfalso. clear -K FP. lia. } clear K.
  zstep. zstep. if_true.
  (* [comment removed for export] *)
  assert (AMO : amo_aligned AD (Z_to_bv 64 BKT) = true) by (apply amo_alignedD_intro; lia).
  do 11 zstep. zstep. zstep. if_false.
  zstep. zstep. lrsc_stepS AMO. zstep. if_false. lrsc_stepS AMO. zstep. if_false.
  (* [comment removed for export] *)
  zstep. zstep. zstep. if_cases K; zify_cond K. { exfalso. clear -K FP. lia. } clear K.
  zstep. zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. clear -K FP. lia. } clear K.
  zstep. zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. clear -K FP. lia. } clear K.
  zstep. zstep. if_true.
  zstep. zstep. if_false.
  zstep. zstep. if_true.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. if_false.
  zstep. zstep. if_true.
  do 6 zstep. zstep. if_true.
  lrsc_stepS AMO. zstep. if_false. lrsc_stepS AMO. zstep. if_false.
  zstep. if_true. zstep. if_true.
  (* [comment removed for export] *)
  do 14 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  apply evtF_done. unfold ahm_acquire_post, ahm_handle, ahm_bucket0.
  do 16 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
Qed.
End Sz5.
#[using="Type"] Lemma ahm_acquire_miss_spec : ltac:(let t := eval cbv delta [ahm_acquire_miss_spec__stmt] in ahm_acquire_miss_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo MAP TABLE H fp mapw bkt0 cell0 idx0 cr0 rest. ltac2:(SecDiet.SzSec.closeP 'ahm_acquire_miss_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ahm_release_nocell_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo H fp : Z) (mapw bkt idxw : word) (cr : byte) (rest : list byte),
  a1 = Z_to_bv 64 H ->
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 ->
  rw_cells asegs m H (ahm_handle mapw bkt (Z_to_bv 64 0) fp idxw cr rest) ->
  bv_unsigned sp <= H -> H + 48 <= 2^63 ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG H 48 ->
  evtF asegs RNG (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' H (ahm_handle mapw bkt (Z_to_bv 64 0) fp idxw cr rest))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4b798) fc None m (seg_rom asegs)).
Section Sz6.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo H fp mapw bkt idxw cr rest : ltac2:(SecDiet.SzSec.tyM 'ahm_release_nocell_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma ahm_release_nocell_spec__body : ltac2:(SecDiet.SzSec.bodyP 'ahm_release_nocell_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros -> MI ST LO HC HLO HHI RSTK RH.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold ahm_handle in *.
  carve_frame 16%nat ST.
  zstep. zstep. zstep. zstep. if_true.
  zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  apply evtF_done. unfold ahm_handle.
  do 16 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
Qed.
End Sz6.
#[using="Type"] Lemma ahm_release_nocell_spec : ltac:(let t := eval cbv delta [ahm_release_nocell_spec__stmt] in ahm_release_nocell_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo H fp mapw bkt idxw cr rest. ltac2:(SecDiet.SzSec.closeP 'ahm_release_nocell_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section AhmTable. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition ahm_zero (m : word -> option byte) (T : Z) : Prop :=
  wr_at asegs m T AHM_BYTES /\ forall i, 0 <= i < AHM_BYTES -> mrd asegs m (wa (T + i)) = Some (Z_to_bv 8 0).

#[using="Type"] Lemma ahm_bucket0_bytes : cells_bytes ahm_bucket0 = repeat (Z_to_bv 8 0) 120.
Proof. vm_compute. reflexivity. Qed.

Definition ahm_zero_bucket__stmt : Prop := forall m T idx, ahm_zero m T -> 0 <= idx < 31051 -> rw_cells asegs m (T + 120 * idx) ahm_bucket0.
Section Sz8.
Variables m T idx : ltac2:(SecDiet.SzSec.tyM 'ahm_zero_bucket__stmt "vvv" @m).
#[using="Type"] Lemma ahm_zero_bucket__body : ltac2:(SecDiet.SzSec.bodyP 'ahm_zero_bucket__stmt "vvv").
Proof.
  intros [(T0 & THI & WR) Z0] IDX.
 unfold AHM_BYTES in *.
  split; [split|].
  - unfold ahm_bucket0. cbn. repeat split; reflexivity.
  - rewrite ahm_bucket0_bytes. unfold bytes_at. rewrite repeat_length. split; [lia|]. split; [lia|].
    intros i Hi. rewrite nth_error_repeat by exact Hi.
    replace (T + 120 * idx + Z.of_nat i) with (T + (120 * idx + Z.of_nat i)) by lia. apply Z0. lia.
  - unfold ahm_bucket0. cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|].
    intros i Hi. replace (T + 120 * idx + i) with (T + (120 * idx + i)) by lia. apply WR. lia.
Qed.
End Sz8.
#[using="Type"] Lemma ahm_zero_bucket : ltac:(let t := eval cbv delta [ahm_zero_bucket__stmt] in ahm_zero_bucket__stmt in exact t).
Proof. intros m T idx. ltac2:(SecDiet.SzSec.closeP 'ahm_zero_bucket__body "vvv"). Qed.

(* [comment removed for export] *)
Definition ahm_munch_restore__stmt : Prop := forall W m m' BKT,
  munch W m m' -> 0x603000 <= BKT -> BKT + 120 <= 2^64 ->
  rw_cells asegs m BKT ahm_bucket0 -> rw_cells asegs m' BKT ahm_bucket0 ->
  forall W', (forall a, outside W' a -> outside W a \/ BKT <= a < BKT + 8) -> munch W' m m'.
Section Sz9.
Variables W m m' BKT : ltac2:(SecDiet.SzSec.tyM 'ahm_munch_restore__stmt "vvvv" @W).
#[using="Type"] Lemma ahm_munch_restore__body : ltac2:(SecDiet.SzSec.bodyP 'ahm_munch_restore__stmt "vvvv").
Proof.
  intros MU BLO BHI [[_ B1] _] [[_ B2] _] W' HW x Hx.
  destruct (HW _ Hx) as [O | IN]; [exact (MU x O)|].
  rewrite ahm_bucket0_bytes in B1, B2. unfold bytes_at in B1, B2. destruct B1 as (_ & _ & R1). destruct B2 as (_ & _ & R2). rewrite repeat_length in R1, R2.
  set (i := Z.to_nat (bv_unsigned x - BKT)).
  specialize (R1 i ltac:(subst i; lia)). specialize (R2 i ltac:(subst i; lia)).
  replace (BKT + Z.of_nat i) with (bv_unsigned x) in R1, R2 by (subst i; lia).
  rewrite wa_unsigned_id in R1, R2.
  pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. change (2 ^ Z.of_N 64) with (2^64) in XR.
  pose proof (mrd_no_image asegs m BKT (BKT + 120) (bv_unsigned x) (no_image_asan _ _ BLO) ltac:(lia) ltac:(lia) BHI) as E1.
  pose proof (mrd_no_image asegs m' BKT (BKT + 120) (bv_unsigned x) (no_image_asan _ _ BLO) ltac:(lia) ltac:(lia) BHI) as E2.
  rewrite wa_unsigned_id in E1, E2. congruence.
Qed.
End Sz9.
#[using="Type"] Lemma ahm_munch_restore : ltac:(let t := eval cbv delta [ahm_munch_restore__stmt] in ahm_munch_restore__stmt in exact t).
Proof. intros W m m' BKT. ltac2:(SecDiet.SzSec.closeP 'ahm_munch_restore__body "vvvv"). Qed.
End AhmTable.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lrsc_stepS AMO :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply (evtF_step_acc segs RNG);
      [ reflexivity
      | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; simp_is_x0; simp_regs; amo_align AMO; rewrite ?Z.eqb_refl; exec_cbv; amo_align AMO; rewrite ?Z.eqb_refl;
        simp_is_x0; simp_regs; vnorm_tail;
        try solve_load; try solve_store; reflexivity
      | solve_accs
      | simp_regs; vnorm_tail; mem_after_store_opt ]
    end end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AHM_SIZE : Z := 31051.
Definition AHM_MAGIC : Z := 0x8713f185cccd38dd.     (* [comment removed for export] *)
Definition ahm_h1 (a : Z) : Z := (a * 1024 + a) mod 2^64.
Definition ahm_hash (a : Z) : Z := Z.lxor (Z.shiftr (ahm_h1 a) 6) (ahm_h1 a).
Definition ahm_idx (a : Z) : Z := ahm_hash a mod AHM_SIZE.
Definition AHM_BUCKET : Z := 120.
Definition AHM_BYTES : Z := 3727360.                  (* [comment removed for export] *)

Definition ahm_magic__stmt : Prop := forall a, 0 <= a < 2^64 -> (a * AHM_MAGIC) / 2^78 = a / 31051.
Section Sz1.
Variables a : ltac2:(SecDiet.SzSec.tyM 'ahm_magic__stmt "v" @a).
#[using="Type"] Lemma ahm_magic__body : ltac2:(SecDiet.SzSec.bodyP 'ahm_magic__stmt "v").
Proof.
  intros Ha.
 symmetry. unfold AHM_MAGIC.
  pose proof (Z.div_mod a 31051 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound a 31051 ltac:(lia)) as MB.
  assert (QB : 0 <= a / 31051 <= 2^64 / 31051) by (split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]).
  assert (E64 : 2^64 / 31051 = 594078904824628) by (vm_compute; reflexivity). rewrite E64 in QB. clear E64.
  apply Z.div_unique with (r := (a / 31051) * 7615 + (a mod 31051) * 0x8713f185cccd38dd); [lia|].
  change (2^78) with 302231454903657293676544. lia.
Qed.
End Sz1.
Lemma ahm_magic : ltac:(let t := eval cbv delta [ahm_magic__stmt] in ahm_magic__stmt in exact t).
Proof. intros a. ltac2:(SecDiet.SzSec.closeP 'ahm_magic__body "v"). Qed.

Lemma ahm_hash_range : forall a, 0 <= ahm_hash a < 2^64.
Proof.
  intros a. unfold ahm_hash, ahm_h1. pose proof (Z.mod_pos_bound (a * 1024 + a) (2^64) ltac:(lia)) as R.
  apply (zr_lxor _ _); [apply zr_shiftr; [exact R | lia] | exact R].
Qed.

Lemma ahm_idx_range : forall a, 0 <= ahm_idx a < 31051.
Proof. intros a. unfold ahm_idx, AHM_SIZE. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
Definition ahm_bucket_off__stmt : Prop := forall h, 0 <= h < 2^64 ->
  Z.shiftl ((h - (Z.shiftr (Z.shiftr (h * 9733388776646719709) 64 mod 18446744073709551616) 14 * 31051) mod 18446744073709551616) mod 18446744073709551616) 7 mod 18446744073709551616
  - Z.shiftl ((h - (Z.shiftr (Z.shiftr (h * 9733388776646719709) 64 mod 18446744073709551616) 14 * 31051) mod 18446744073709551616) mod 18446744073709551616) 3 mod 18446744073709551616
  = 120 * (h mod 31051).
Section Sz4.
Variables h : ltac2:(SecDiet.SzSec.tyM 'ahm_bucket_off__stmt "v" @h).
#[using="Type"] Lemma ahm_bucket_off__body : ltac2:(SecDiet.SzSec.bodyP 'ahm_bucket_off__stmt "v").
Proof.
  intros Hh.
  assert (Q : Z.shiftr (Z.shiftr (h * 9733388776646719709) 64 mod 18446744073709551616) 14 = h / 31051).
  { rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.mod_small.
    - rewrite Z.div_div by lia. change (2^64 * 2^14) with (2^78). apply (ahm_magic h Hh).
    - split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. lia. }
  rewrite Q.
  pose proof (Z.div_mod h 31051 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound h 31051 ltac:(lia)) as MB.
  assert (QB : 0 <= h / 31051) by (apply Z.div_pos; lia).
  rewrite (Z.mod_small (h / 31051 * 31051)) by lia.
  replace (h - h / 31051 * 31051) with (h mod 31051) by lia.
  rewrite (Z.mod_small (h mod 31051)) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia. rewrite !Z.mod_small by lia. lia.
Qed.
End Sz4.
Lemma ahm_bucket_off : ltac:(let t := eval cbv delta [ahm_bucket_off__stmt] in ahm_bucket_off__stmt in exact t).
Proof. intros h. ltac2:(SecDiet.SzSec.closeP 'ahm_bucket_off__body "v"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition ahm_bucket0 : list cell :=
  [C8 (Z_to_bv 64 0); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0); CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0); CB 24 (repeat (Z_to_bv 8 0) 24)].

(* [comment removed for export] *)
Definition ahm_handle (mapw bkt cellw : word) (fp : Z) (idxw : word) (created : byte) (rest : list byte) : list cell :=
  [C8 mapw; C8 bkt; C8 cellw; C8 (Z_to_bv 64 fp); C8 idxw; C1 created; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 5 rest].

Definition ahm_acquire_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo H BKT fp : Z) (mapw : word) (rest : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp); (H, H + 48); (BKT, BKT + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' H (ahm_handle mapw (Z_to_bv 64 BKT) (Z_to_bv 64 0) fp (Z_to_bv 64 4294967295) (Z_to_bv 8 0) rest)
    /\ rw_cells asegs m' BKT ahm_bucket0.

Definition ahm_acquire_miss_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo MAP TABLE H fp : Z) (mapw bkt0 cell0 idx0 : word) (cr0 : byte) (rest : list byte),
  let BKT := TABLE + 120 * ahm_idx fp in
  a0 = Z_to_bv 64 MAP -> a1 = Z_to_bv 64 H ->
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 ->
  rw_cells asegs m MAP [C8 (Z_to_bv 64 TABLE)] ->
  rw_cells asegs m H (ahm_handle mapw bkt0 cell0 fp idx0 cr0 rest) ->
  rw_cells asegs m BKT ahm_bucket0 ->
  0 < fp < 2^64 -> TABLE mod 8 = 0 -> 0x604000 <= TABLE -> TABLE + AHM_BYTES <= lo ->
  0x10000 <= MAP -> MAP + 8 <= 0x604000 -> 0x604000 <= lo ->
  bv_unsigned sp <= H -> H + 48 <= 2^63 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG H 48 -> rng RNG BKT 120 ->
  evtF asegs RNG (ahm_acquire_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo H BKT fp mapw rest m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4afe0) fc None m (seg_rom asegs)).
Section Sz5.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo MAP TABLE H fp mapw bkt0 cell0 idx0 cr0 rest : ltac2:(SecDiet.SzSec.tyM 'ahm_acquire_miss_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma ahm_acquire_miss_spec__body : ltac2:(SecDiet.SzSec.bodyP 'ahm_acquire_miss_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros BKT -> -> MI ST LO MAPC HC BC FP TAL TLO THI MLO MHI GLO HLO HHI RIMG RSTK RH RB.
  pose proof (ahm_idx_range fp) as IDX. pose proof (ahm_hash_range fp) as HR.
  assert (BR : TABLE <= BKT /\ BKT + 120 <= TABLE + AHM_BYTES /\ BKT mod 8 = 0).
  { subst BKT. unfold AHM_BYTES. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. }
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp); (H, H + 48); (BKT, BKT + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold ahm_handle, ahm_bucket0 in *. unfold AHM_BYTES in *.
  carve_frame 176%nat ST.
  (* [comment removed for export] *)
  lazymatch goal with
  | FRx : rw_cells asegs m ?A [CB 176 ?j] |- _ =>
      apply (rw_cells_split_CB asegs m A [] 176 j [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx;
        [ | reflexivity ];
      cbn [app mk_CB_cells] in FRx;
      repeat match type of FRx with
      | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
      end
  end.
  do 14 zstep. do 8 zstep. do 3 zstep. do 22 zstep.
  replace (Z.lxor (Z.shiftr ((Z.shiftl fp 10 + fp) mod 18446744073709551616) 6) ((Z.shiftl fp 10 + fp) mod 18446744073709551616)) with (ahm_hash fp)
    by (unfold ahm_hash, ahm_h1; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  do 8 zstep.
  rewrite (ahm_bucket_off (ahm_hash fp) HR). change (ahm_hash fp mod 31051) with (ahm_idx fp). fold BKT.
  (* [comment removed for export] *)
  do 4 zstep. do 13 zstep. zstep. if_false.
  zstep. zstep. if_false.
  (* [comment removed for export] *)
  zstep. zstep. zstep. if_cases K; zify_cond K. { exfalso. clear -K FP. lia. } clear K.
  zstep. zstep. zstep. if_cases K; zify_cond K. { exfalso. clear -K FP. lia. } clear K.
  zstep. zstep. zstep. if_cases K; zify_cond K. { exfalso. clear -K FP. lia. } clear K.
  zstep. zstep. if_true.
  (* [comment removed for export] *)
  assert (AMO : amo_aligned AD (Z_to_bv 64 BKT) = true) by (apply amo_alignedD_intro; lia).
  do 11 zstep. zstep. zstep. if_false.
  zstep. zstep. lrsc_stepS AMO. zstep. if_false. lrsc_stepS AMO. zstep. if_false.
  (* [comment removed for export] *)
  zstep. zstep. zstep. if_cases K; zify_cond K. { exfalso. clear -K FP. lia. } clear K.
  zstep. zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. clear -K FP. lia. } clear K.
  zstep. zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. clear -K FP. lia. } clear K.
  zstep. zstep. if_true.
  zstep. zstep. if_false.
  zstep. zstep. if_true.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. if_false.
  zstep. zstep. if_true.
  do 6 zstep. zstep. if_true.
  lrsc_stepS AMO. zstep. if_false. lrsc_stepS AMO. zstep. if_false.
  zstep. if_true. zstep. if_true.
  (* [comment removed for export] *)
  do 14 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  apply evtF_done. unfold ahm_acquire_post, ahm_handle, ahm_bucket0.
  do 16 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
Qed.
End Sz5.
#[using="Type"] Lemma ahm_acquire_miss_spec : ltac:(let t := eval cbv delta [ahm_acquire_miss_spec__stmt] in ahm_acquire_miss_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo MAP TABLE H fp mapw bkt0 cell0 idx0 cr0 rest. ltac2:(SecDiet.SzSec.closeP 'ahm_acquire_miss_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ahm_release_nocell_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo H fp : Z) (mapw bkt idxw : word) (cr : byte) (rest : list byte),
  a1 = Z_to_bv 64 H ->
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 ->
  rw_cells asegs m H (ahm_handle mapw bkt (Z_to_bv 64 0) fp idxw cr rest) ->
  bv_unsigned sp <= H -> H + 48 <= 2^63 ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG H 48 ->
  evtF asegs RNG (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' H (ahm_handle mapw bkt (Z_to_bv 64 0) fp idxw cr rest))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4b800) fc None m (seg_rom asegs)).
Section Sz6.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo H fp mapw bkt idxw cr rest : ltac2:(SecDiet.SzSec.tyM 'ahm_release_nocell_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma ahm_release_nocell_spec__body : ltac2:(SecDiet.SzSec.bodyP 'ahm_release_nocell_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros -> MI ST LO HC HLO HHI RSTK RH.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold ahm_handle in *.
  carve_frame 16%nat ST.
  zstep. zstep. zstep. zstep. if_true.
  zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  apply evtF_done. unfold ahm_handle.
  do 16 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
Qed.
End Sz6.
#[using="Type"] Lemma ahm_release_nocell_spec : ltac:(let t := eval cbv delta [ahm_release_nocell_spec__stmt] in ahm_release_nocell_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo H fp mapw bkt idxw cr rest. ltac2:(SecDiet.SzSec.closeP 'ahm_release_nocell_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section AhmTable. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition ahm_zero (m : word -> option byte) (T : Z) : Prop :=
  wr_at asegs m T AHM_BYTES /\ forall i, 0 <= i < AHM_BYTES -> mrd asegs m (wa (T + i)) = Some (Z_to_bv 8 0).

#[using="Type"] Lemma ahm_bucket0_bytes : cells_bytes ahm_bucket0 = repeat (Z_to_bv 8 0) 120.
Proof. vm_compute. reflexivity. Qed.

Definition ahm_zero_bucket__stmt : Prop := forall m T idx, ahm_zero m T -> 0 <= idx < 31051 -> rw_cells asegs m (T + 120 * idx) ahm_bucket0.
Section Sz8.
Variables m T idx : ltac2:(SecDiet.SzSec.tyM 'ahm_zero_bucket__stmt "vvv" @m).
#[using="Type"] Lemma ahm_zero_bucket__body : ltac2:(SecDiet.SzSec.bodyP 'ahm_zero_bucket__stmt "vvv").
Proof.
  intros [(T0 & THI & WR) Z0] IDX.
 unfold AHM_BYTES in *.
  split; [split|].
  - unfold ahm_bucket0. cbn. repeat split; reflexivity.
  - rewrite ahm_bucket0_bytes. unfold bytes_at. rewrite repeat_length. split; [lia|]. split; [lia|].
    intros i Hi. rewrite nth_error_repeat by exact Hi.
    replace (T + 120 * idx + Z.of_nat i) with (T + (120 * idx + Z.of_nat i)) by lia. apply Z0. lia.
  - unfold ahm_bucket0. cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|].
    intros i Hi. replace (T + 120 * idx + i) with (T + (120 * idx + i)) by lia. apply WR. lia.
Qed.
End Sz8.
#[using="Type"] Lemma ahm_zero_bucket : ltac:(let t := eval cbv delta [ahm_zero_bucket__stmt] in ahm_zero_bucket__stmt in exact t).
Proof. intros m T idx. ltac2:(SecDiet.SzSec.closeP 'ahm_zero_bucket__body "vvv"). Qed.

(* [comment removed for export] *)
Definition ahm_munch_restore__stmt : Prop := forall W m m' BKT,
  munch W m m' -> 0x604000 <= BKT -> BKT + 120 <= 2^64 ->
  rw_cells asegs m BKT ahm_bucket0 -> rw_cells asegs m' BKT ahm_bucket0 ->
  forall W', (forall a, outside W' a -> outside W a \/ BKT <= a < BKT + 8) -> munch W' m m'.
Section Sz9.
Variables W m m' BKT : ltac2:(SecDiet.SzSec.tyM 'ahm_munch_restore__stmt "vvvv" @W).
#[using="Type"] Lemma ahm_munch_restore__body : ltac2:(SecDiet.SzSec.bodyP 'ahm_munch_restore__stmt "vvvv").
Proof.
  intros MU BLO BHI [[_ B1] _] [[_ B2] _] W' HW x Hx.
  destruct (HW _ Hx) as [O | IN]; [exact (MU x O)|].
  rewrite ahm_bucket0_bytes in B1, B2. unfold bytes_at in B1, B2. destruct B1 as (_ & _ & R1). destruct B2 as (_ & _ & R2). rewrite repeat_length in R1, R2.
  set (i := Z.to_nat (bv_unsigned x - BKT)).
  specialize (R1 i ltac:(subst i; lia)). specialize (R2 i ltac:(subst i; lia)).
  replace (BKT + Z.of_nat i) with (bv_unsigned x) in R1, R2 by (subst i; lia).
  rewrite wa_unsigned_id in R1, R2.
  pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. change (2 ^ Z.of_N 64) with (2^64) in XR.
  pose proof (mrd_no_image asegs m BKT (BKT + 120) (bv_unsigned x) (no_image_asan _ _ BLO) ltac:(lia) ltac:(lia) BHI) as E1.
  pose proof (mrd_no_image asegs m' BKT (BKT + 120) (bv_unsigned x) (no_image_asan _ _ BLO) ltac:(lia) ltac:(lia) BHI) as E2.
  rewrite wa_unsigned_id in E1, E2. congruence.
Qed.
End Sz9.
#[using="Type"] Lemma ahm_munch_restore : ltac:(let t := eval cbv delta [ahm_munch_restore__stmt] in ahm_munch_restore__stmt in exact t).
Proof. intros W m m' BKT. ltac2:(SecDiet.SzSec.closeP 'ahm_munch_restore__body "vvvv"). Qed.
End AhmTable.
End TwB.
