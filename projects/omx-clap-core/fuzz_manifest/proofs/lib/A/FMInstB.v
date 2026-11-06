(* FmB (A/FMW_seg.v), the B facts fm's walks read, for every B with TfibSyms B (so for fm's TfibB, A/AD2l.v):
   the code addresses (ts_code); the shadow-base .got slot 0x999b0 = 0xa1d78 and the cell 0xa1d78 = 0x7fff8000 in
   every AR state (AR's constant cells: Tfib_const_abs rows 143 and 49, A/AF0m.v); fuzz/alloc.c's statics FM_PSTAT_FP
   neither runtime-owned nor errno (computed over Tfib_owned_static and TFIB_ERRNO). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YP09 YK04 YA0i YA0n YG00 YG01 YG0f YG0n YG0d YI04 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0m AD2l AD1k FMPstat FMW_kit FMW_seg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Lemma fmib_pstat_chk :
  forallb (fun f => forallb (fun r => (fst r + snd r <=? fst f) || (snd f <=? fst r)) Tfib_owned_static &&
    ((snd f <=? TFIB_ERRNO) || (TFIB_ERRNO + 4 <=? fst f))) FM_PSTAT_FP = true.
Proof. vm_compute. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : TfibSyms B.

Lemma fmib_abs_in : forall ly c, In c Tfib_const_abs -> In c (as_const B ly).
Proof.
  intros ly c Hc. rewrite (ts_const B TB ly). unfold Tfib_const. apply in_or_app. right. apply in_or_app. left. exact Hc.
Qed.

Lemma fmib_got_shadow : forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md ->
  val_mem tfibsegs (mrestrict (w_H W) mem) FMW_GOT_shadow 8 FMW_shadow_cell.
Proof.
  intros ly S W mem md (M & _).
  assert (Hin : In (z8 (ANum FMW_GOT_shadow) FMW_shadow_cell) (as_const B ly))
    by (apply fmib_abs_in; apply (nth_error_In Tfib_const_abs 143); reflexivity).
  pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ M) _ Hin) as C.
  unfold cell_holds in C. cbn [c_at c_val c_w z8 c8 aeval] in C.
  intros k Hk. pose proof (C k Hk) as Ck. unfold aview in Ck.
  destruct (mbyte tfibsegs (mrestrict (w_H W) mem) (FMW_GOT_shadow + Z.of_nat k)) as [b|]; [|discriminate Ck].
  cbn [option_map] in Ck. injection Ck as Ck. f_equal. apply bv_eq. rewrite Ck, Z_to_bv_unsigned.
  do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma fmib_shadow_cell : forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md ->
  val_mem tfibsegs (mrestrict (w_H W) mem) FMW_shadow_cell 8 FMW_SB.
Proof.
  intros ly S W mem md (M & _).
  assert (Hin : In (z8 (ANum FMW_shadow_cell) FMW_SB) (as_const B ly))
    by (apply fmib_abs_in; apply (nth_error_In Tfib_const_abs 49); reflexivity).
  pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ M) _ Hin) as C.
  unfold cell_holds in C. cbn [c_at c_val c_w z8 c8 aeval] in C.
  intros k Hk. pose proof (C k Hk) as Ck. unfold aview in Ck.
  destruct (mbyte tfibsegs (mrestrict (w_H W) mem) (FMW_shadow_cell + Z.of_nat k)) as [b|]; [|discriminate Ck].
  cbn [option_map] in Ck. injection Ck as Ck. f_equal. apply bv_eq. rewrite Ck, Z_to_bv_unsigned.
  do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

Theorem fm_FmB : FmB B.
Proof.
  constructor.
  - exact (ts_code B TB).
  - intros ly S W mem md HAR. split; [exact (fmib_got_shadow ly S W mem md HAR) | exact (fmib_shadow_cell ly S W mem md HAR)].
  - intros a (f & Hf & Ha).
    pose proof (proj1 (forallb_forall _ _) fmib_pstat_chk f Hf) as Hb. cbv beta in Hb.
    apply andb_prop in Hb as [Ho He]. split.
    + exact (tfib_not_owned_static B (fst f) (snd f) a TB Ho Ha).
    + rewrite (ts_errno B TB). apply orb_prop in He as [He|He]; apply Z.leb_le in He; lia.
Qed.
End b.

Theorem fm_FmB_TfibB : forall {fx : YK11.FPState} {rc : YM05.RunCeil}, FmB TfibB.
Proof. intros fx rc. exact (fm_FmB TfibB TfibB_syms). Qed.
