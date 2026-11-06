(* fs's bridge from the harness contract to the driver's library-invariant contract.  a Theorem Labs lane has no bridge of its
   own (searched: (an internal command):
   only A/ACfn.v, A/AD1q.v and A/FMTfibParts.v), so this file is fs's own.

   LI_fs i W mem says: fuzz/alloc.c's statics are in harness form (FSH_Base.v fs_stat: g_fail_at = SIZE_MAX and
   g_live = 0, the driver's value, because LLVMFuzzerTestOneInput frees every block it makes -- A/ACfn.v
   tfib_lib_post_x's Permutation of ablocks) and g_count is at most i * FS_CNT_LIB.  That is the invariant the
   driver carries: call ci needs LI ci and gives LI (ci + 1) (A/AD1w.v lib_inv_stable / lib_inv_init, A/ACfn.v
   tfib_lib_contract_xI).  The driver makes at most 4 calls, so the count never passes 4 * 96 = 384 and the two
   resource premises of fs_lib_contract_x (FSH_Harness.v) -- cnt + FS_CNT_LIB < 2 ^ 63 and live + LIVE_LIB < 2 ^ 64
   -- hold with room to spare (384 + 96 < 2 ^ 63, 0 + 2 ^ 33 < 2 ^ 64).

   The three results are the three Section hypotheses of A/FSTfibParts.v:
     fs_lib_xI_all : fs_lib_contract_x_all B MT XM_LIB XN_LIB -> tfib_lib_contract_xI_all B MT XM_LIB XN_LIB FS_RLO FS_RHI LI_fs
     LIK_fs        : lib_inv_stable LI_fs
     LI0_fs        : lib_inv_init LI_fs
   LI0_fs reads the image: g_fail_at (.data, 0xa3ca0) holds SIZE_MAX and g_live / g_peak / g_count (.bss,
   0x5da5c0 / 0x5da5e0 / 0x5da600) hold 0, so the pre-loop state, whose bytes at FS_PSTAT_FP are the image's,
   satisfies LI_fs 0.
   rule 24: no function proved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI00 YI04 YI16 YO09 YO0f YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v ACfn AD1w FSPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSH_Gen FSH_Base FSH_Harness.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Abbreviation segs := tfibsegs.

(* the driver's library invariant over fs's static state: at a call site every block the target made is freed, so
   g_live is 0, g_fail_at is SIZE_MAX, and g_count has grown by at most FS_CNT_LIB per call made so far. *)
Definition LI_fs (i : Z) (W : world segs) (mem : word -> option byte) : Prop :=
  exists cnt, fs_stat segs W mem 0 cnt /\ 0 <= cnt <= i * FS_CNT_LIB.

(* ---- the two byte-level facts LIK_fs and LI0_fs rest on ---- *)

(* an 8-byte static cell of FS_PSTAT_FP keeps its value under any change that keeps the bytes of FS_PSTAT_FP *)
Lemma keep_val : forall (W W' : world segs) (m m' : word -> option byte) (g v : Z),
  In (g, g + 8) FS_PSTAT_FP ->
  (forall a, inFP FS_PSTAT_FP a -> aview segs (w_H W') m' a = aview segs (w_H W) m a) ->
  val_mem segs (mrestrict (w_H W) m) g 8 v -> val_mem segs (mrestrict (w_H W') m') g 8 v.
Proof.
intros W W' m m' g v Hg Hk Hv k Hkk.
pose proof (Hk (g + Z.of_nat k) (inFP_FS_PSTAT_FP g Hg (g + Z.of_nat k) ltac:(lia))) as Ha.
unfold aview in Ha. rewrite (Hv k Hkk) in Ha. cbn [option_map] in Ha.
destruct (mbyte segs (mrestrict (w_H W') m') (g + Z.of_nat k)) as [b|] eqn:E; [| discriminate Ha].
cbn [option_map] in Ha. injection Ha as Ha. f_equal. apply bv_eq. exact Ha.
Qed.

(* an 8-byte static cell of FS_PSTAT_FP holds the image value when its bytes are the image's *)
Lemma rom_val : forall (W : world segs) (mem : word -> option byte) (g v : Z),
  In (g, g + 8) FS_PSTAT_FP ->
  (forall a, inFP FS_PSTAT_FP a ->
     aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a))) ->
  (forall k, (k < 8)%nat -> seg_rom segs (Z_to_bv 64 (g + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte v 8 k))) ->
  val_mem segs (mrestrict (w_H W) mem) g 8 v.
Proof.
intros W mem g v Hg H Hrom k Hk.
pose proof (H (g + Z.of_nat k) (inFP_FS_PSTAT_FP g Hg (g + Z.of_nat k) ltac:(lia))) as Hv.
unfold aview in Hv. rewrite (Hrom k Hk) in Hv. cbn [option_map] in Hv.
destruct (mbyte segs (mrestrict (w_H W) mem) (g + Z.of_nat k)) as [b|] eqn:E; [| discriminate Hv].
cbn [option_map] in Hv. injection Hv as Hv. f_equal. apply bv_eq. exact Hv.
Qed.

Lemma pstat_in_live : In (G_LIVE, G_LIVE + 8) FS_PSTAT_FP.
Proof. vm_compute. repeat (first [left; reflexivity | right]). Qed.
Lemma pstat_in_peak : In (G_PEAK, G_PEAK + 8) FS_PSTAT_FP.
Proof. vm_compute. repeat (first [left; reflexivity | right]). Qed.
Lemma pstat_in_count : In (G_COUNT, G_COUNT + 8) FS_PSTAT_FP.
Proof. vm_compute. repeat (first [left; reflexivity | right]). Qed.
Lemma pstat_in_fail : In (G_FAIL, G_FAIL + 8) FS_PSTAT_FP.
Proof. vm_compute. repeat (first [left; reflexivity | right]). Qed.

(* the image bytes of fuzz/alloc.c's statics: g_live / g_peak / g_count are .bss zeros, g_fail_at is SIZE_MAX *)
Lemma rom_live : forall k, (k < 8)%nat -> seg_rom segs (Z_to_bv 64 (G_LIVE + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte 0 8 k)).
Proof.
intros k Hk. assert (H : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7)%nat) by lia.
destruct H as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma rom_peak : forall k, (k < 8)%nat -> seg_rom segs (Z_to_bv 64 (G_PEAK + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte 0 8 k)).
Proof.
intros k Hk. assert (H : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7)%nat) by lia.
destruct H as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma rom_count : forall k, (k < 8)%nat -> seg_rom segs (Z_to_bv 64 (G_COUNT + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte 0 8 k)).
Proof.
intros k Hk. assert (H : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7)%nat) by lia.
destruct H as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma rom_fail : forall k, (k < 8)%nat -> seg_rom segs (Z_to_bv 64 (G_FAIL + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte SIZE_MAXZ 8 k)).
Proof.
intros k Hk. assert (H : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7)%nat) by lia.
destruct H as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

(* ---- the three results ---- *)

Lemma LIK_fs : lib_inv_stable LI_fs.
Proof.
intros ci W W' mem mem' (cnt & (peak & G1 & G2 & G3 & G4 & R) & Hb) Hk.
exists cnt. split; [| exact Hb]. exists peak.
unfold fs_glob, fs_glob_at.
split; [exact (keep_val W W' mem mem' G_LIVE 0 pstat_in_live Hk G1)|].
split; [exact (keep_val W W' mem mem' G_PEAK peak pstat_in_peak Hk G2)|].
split; [exact (keep_val W W' mem mem' G_COUNT cnt pstat_in_count Hk G3)|].
split; [exact (keep_val W W' mem mem' G_FAIL SIZE_MAXZ pstat_in_fail Hk G4) | exact R].
Qed.

Lemma LI0_fs : lib_inv_init LI_fs.
Proof.
intros W mem H. exists 0. split; [| lia]. exists 0.
unfold fs_glob, fs_glob_at.
split; [exact (rom_val W mem G_LIVE 0 pstat_in_live H rom_live)|].
split; [exact (rom_val W mem G_PEAK 0 pstat_in_peak H rom_peak)|].
split; [exact (rom_val W mem G_COUNT 0 pstat_in_count H rom_count)|].
split; [exact (rom_val W mem G_FAIL SIZE_MAXZ pstat_in_fail H rom_fail)|].
unfold SIZE_MAXZ. repeat split; lia.
Qed.

Theorem fs_lib_xI_all : forall {rc : YM05.RunCeil} {LS : lib_shape}
  (B : asyms) (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z),
  @fs_lib_contract_x_all rc LS B MT XM_LIB XN_LIB ->
  @tfib_lib_contract_xI_all rc LS B MT XM_LIB XN_LIB FS_RLO FS_RHI LI_fs.
Proof.
intros rc LS B MT XM_LIB XN_LIB HX fx.
intros ly S W regs mem md p n pl M K ci Hci HLI HAI HPRE CONT.
destruct HLI as (cnt & Hstat & Hc0 & Hcb). unfold FS_CNT_LIB in Hcb.
apply (HX fx ly S W regs mem md p n pl M K 0 cnt HAI HPRE Hstat Hc0
  ltac:(unfold FS_CNT_LIB; lia) ltac:(unfold LIVE_LIB; vm_compute; reflexivity)).
intros l W' c' Hwle HAI' (ly' & S' & regs' & mem' & md' & k & cnt' & Hc' & HPOST & Hstat' & Hcnt').
apply (CONT l W' c' Hwle HAI'). exists ly', S', regs', mem', md', k.
split; [exact Hc'|]. split; [exact HPOST|].
exists cnt'. split; [exact Hstat'|]. unfold FS_CNT_LIB in *. lia.
Qed.
