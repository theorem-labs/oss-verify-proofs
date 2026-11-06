(* fm program part, the driver side of fm's library invariant (FMH_Harness.v fm_LI): it is stable when fuzz/alloc.c's
   statics' bytes are unchanged (fm_LI_stable, A/AD1w.v lib_inv_stable) and holds at call 0 on the start-up bytes
   (fm_LI_init: g_fail_at = SIZE_MAX in .data at 0x9df80, g_live = g_peak = g_count = 0 in zero-filled .bss). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC20 YC5d YCbp YI00 YI04 YI16 YK06 YO09 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest Require Import lib.ZTraceSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v FMPstat AE2k ACfn AD1w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn FMH_Harness.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* a word whose bytes read as the start-up image *)
Lemma val_mem_of_rom : forall (W : world tfibsegs) mem a (n : nat) v,
  (forall k, (k < n)%nat -> aview tfibsegs (w_H W) mem (a + Z.of_nat k) =
     option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k)))) ->
  (forall k, (k < n)%nat -> seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte v n k))) ->
  val_mem tfibsegs (rdW W mem) a n v.
Proof.
intros W mem a n v HV HR k Hk. specialize (HV k Hk). rewrite (HR k Hk) in HV. unfold aview in HV.
destruct (mbyte tfibsegs (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|] eqn:E; cbn in HV; [|discriminate HV].
injection HV as HV. f_equal. apply bv_eq. exact HV.
Qed.

Lemma pstat_word : forall g a, In (g, g + 8) FM_PSTAT_FP -> forall k, (k < 8)%nat -> a = g + Z.of_nat k -> inFP FM_PSTAT_FP a.
Proof. intros g a Hg k Hk ->. apply (inFP_FM_PSTAT_FP g Hg). lia. Qed.

(* fm_stat reads only fuzz/alloc.c's statics *)
Lemma fm_LI_stable_holds : fm_LI_stable.
Proof.
intros ci W W' mem mem' (cnt & (peak & (G1 & G2 & G3 & G4 & R)) & Hc) HK.
exists cnt. split; [|exact Hc]. exists peak.
assert (KW : forall g v, In (g, g + 8) FM_PSTAT_FP -> val_mem tfibsegs (rdW W mem) g 8 v -> val_mem tfibsegs (rdW W' mem') g 8 v).
{ intros g v Hg Hv. eapply (val_mem_kept tfibsegs); [|exact Hv]. intros k Hk. apply HK.
  apply (inFP_FM_PSTAT_FP g Hg). cbn in Hk. lia. }
unfold fm_glob. split; [|split; [|split; [|split]]].
- apply KW; [unfold FM_PSTAT_FP, G_LIVE; right; left; reflexivity | exact G1].
- apply KW; [unfold FM_PSTAT_FP, G_PEAK; right; right; left; reflexivity | exact G2].
- apply KW; [unfold FM_PSTAT_FP, G_COUNT; right; right; right; left; reflexivity | exact G3].
- apply KW; [unfold FM_PSTAT_FP, G_FAIL; left; reflexivity | exact G4].
- exact R.
Qed.

(* at call 0 the statics are the start-up bytes: g_fail_at = SIZE_MAX (.data 0x9df80), g_live = g_peak = g_count = 0 (.bss) *)
Lemma fm_LI_init_holds : fm_LI_init.
Proof.
intros W mem HR. exists 0. split; [|cbn; lia]. exists 0.
assert (KW : forall g v, In (g, g + 8) FM_PSTAT_FP ->
  (forall k, (k < 8)%nat -> seg_rom tfibsegs (Z_to_bv 64 (g + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte v 8 k))) ->
  val_mem tfibsegs (rdW W mem) g 8 v).
{ intros g v Hg Hr. apply val_mem_of_rom; [|exact Hr]. intros k Hk. apply HR. exact (pstat_word g _ Hg k Hk eq_refl). }
unfold fm_glob. split; [|split; [|split; [|split]]].
- apply KW; [unfold FM_PSTAT_FP, G_LIVE; right; left; reflexivity|].
  intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
- apply KW; [unfold FM_PSTAT_FP, G_PEAK; right; right; left; reflexivity|].
  intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
- apply KW; [unfold FM_PSTAT_FP, G_COUNT; right; right; right; left; reflexivity|].
  intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
- apply KW; [unfold FM_PSTAT_FP, G_FAIL; left; reflexivity|].
  intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
- unfold SIZE_MAXZ. lia.
Qed.

End b.

