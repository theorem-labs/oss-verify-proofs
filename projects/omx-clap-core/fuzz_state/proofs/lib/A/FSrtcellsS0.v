(* fs.asan's start-up runtime cells as S0-native facts (no Bz tree in the Require closure).
   rule 24: no function proved (kind: start-up facts - lemmas reading the certified start-up table; no walk).
   - fs_shadow_syms_of: FSH_Base.FsShadowSyms B (lib/A/FSH_Base.v:119-121) from the relocated core's ACeg.TfibLib B
     (tl_got_shadow, tl_shadow_cell): ACeg's A_GOT_shadow 0x9f6f0 / A_shadow_glob 0xa7f38 are AB1w's
     tfib_D_GOT_asan_shadow_memory_dynamic_address / tfib_D_asan_shadow_memory_dynamic_address (AB1w.v:589, :600).
   - fs_rt_vals: at every ASan state (AR) the restricted memory holds, as val_mem facts, the cells of
     FSstrlen.fs_rt_rest (lib/A/FSstrlen.v:533-542), read from AR's ARm and TfibSyms' ts_const through
     AF0x.tfib_const_lookup on lib/A/AF0m.v's rows (S0 9b3dbce0433): z8 0x9f6e0 0x139a68, z8 0x9f6f8 0xa8c28,
     z8 0x9f700 0xa8c30, z8 0x9f708 0xa8c20, z8 0xa1408 0x99070, z8 0xa1430 0x98924, z1 0xa8c18 0x1,
     z8 0xa8c20 0x7fffffffffff, z8 0xa8c28 0x0, z8 0xa8c30 0x0; the three flag bytes 0x139b5d (= 0), 0x139b62 (= 1),
     0x139b63 (= 1) are the little-endian bytes 5, 2, 3 of the words z8 0x139b58 0x101000100000000 and
     z8 0x139b60 0x101010101010101 (val_mem_byte_at).
   lib/A/FSrtcells.v turns fs_rt_vals into the Bz tree's ro_cells (FSstrlen.FsRtCells). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.AB1w.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.AF0x.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YO0f YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK04 YK0i YP09 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AF0m FSH_Base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Module AFx := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.AF0x.
Module ACg := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.ACeg.

(* ---- FsShadowSyms from TfibLib ---- *)
Lemma ACeg_shadow_vals : ACg.A_GOT_shadow = AB1w.tfib_D_GOT_asan_shadow_memory_dynamic_address /\
  ACg.A_shadow_glob = AB1w.tfib_D_asan_shadow_memory_dynamic_address.
Proof. split; vm_compute; reflexivity. Qed.

Lemma fs_shadow_syms_of : forall B, ACg.TfibLib B -> FsShadowSyms B.
Proof.
  intros B TL. destruct ACeg_shadow_vals as (V1 & V2). split.
  - rewrite (ACg.tl_got_shadow B TL). exact V1.
  - rewrite (ACg.tl_shadow_cell B TL). exact V2.
Qed.

(* ---- one byte of a val_mem value (little-endian) is a 1-byte val_mem value ---- *)
Lemma le_byte_range : forall z (w k : nat), 0 <= YO0f.le_byte z w k < 256.
Proof. intros z w k. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia. Qed.

Lemma le_byte_1_0 : forall z, 0 <= z < 256 -> YO0f.le_byte z 1 0 = z.
Proof.
  intros z Hz. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small z 256 Hz). exact (Z.mod_small z 256 Hz).
Qed.

Lemma val_mem_byte : forall m A n v k, (k < n)%nat -> val_mem tfibsegs m A n v ->
  val_mem tfibsegs m (A + Z.of_nat k) 1 (YO0f.le_byte v n k).
Proof.
  intros m A n v k Hk HV j Hj. destruct j as [|j]; [|exfalso; lia].
  change (Z.of_nat 0) with 0. rewrite Z.add_0_r. rewrite (HV k Hk).
  exact (f_equal (fun z => Some (Z_to_bv 8 z)) (eq_sym (le_byte_1_0 _ (le_byte_range v n k)))).
Qed.

Lemma val_mem_byte_at : forall m A n v k a b, (k < n)%nat -> a = A + Z.of_nat k -> YO0f.le_byte v n k = b ->
  val_mem tfibsegs m A n v -> val_mem tfibsegs m a 1 b.
Proof. intros m A n v k a b Hk -> <- HV. exact (val_mem_byte m A n v k Hk HV). Qed.

Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- the start-up cells fs's interceptor walks read, at every ASan state ---- *)
Lemma fs_rt_vals : forall B, AR_laws tfibsegs B -> TfibSyms B ->
  forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md ->
  val_mem tfibsegs (mrestrict (w_H W) mem) 0x9f6e0 8 0x139a68 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0x9f6f8 8 0xa8c28 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0x9f700 8 0xa8c30 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0x9f708 8 0xa8c20 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0xa1408 8 0x99070 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0xa1430 8 0x98924 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0xa8c18 1 1 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0xa8c20 8 0x7fffffffffff /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0xa8c28 8 0 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0xa8c30 8 0 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0x139b5d 1 0 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0x139b62 1 1 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0x139b63 1 1.
Proof.
  intros B _ TB ly S W mem md HAR.
  pose proof (proj1 HAR) as M.
  assert (V : forall a (w : nat) v,
    AFx.cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) ->
    val_mem tfibsegs (mrestrict (w_H W) mem) a w v)
    by (intros a w v E; exact (AFx.tfib_const_lookup B TB ly S (w_H W) mem a w v M E)).
  pose proof (V 0x139b58 8%nat 0x101000100000000 ltac:(vm_compute; reflexivity)) as W58.
  pose proof (V 0x139b60 8%nat 0x101010101010101 ltac:(vm_compute; reflexivity)) as W60.
  split; [apply V; vm_compute; reflexivity|].
  split; [apply V; vm_compute; reflexivity|].
  split; [apply V; vm_compute; reflexivity|].
  split; [apply V; vm_compute; reflexivity|].
  split; [apply V; vm_compute; reflexivity|].
  split; [apply V; vm_compute; reflexivity|].
  split; [apply V; vm_compute; reflexivity|].
  split; [apply V; vm_compute; reflexivity|].
  split; [apply V; vm_compute; reflexivity|].
  split; [apply V; vm_compute; reflexivity|].
  split; [apply (val_mem_byte_at _ 0x139b58 8 0x101000100000000 5);
    [lia | reflexivity | vm_compute; reflexivity | exact W58]|].
  split; [apply (val_mem_byte_at _ 0x139b60 8 0x101010101010101 2);
    [lia | reflexivity | vm_compute; reflexivity | exact W60]|].
  apply (val_mem_byte_at _ 0x139b60 8 0x101010101010101 3);
    [lia | reflexivity | vm_compute; reflexivity | exact W60].
Qed.

End core.
