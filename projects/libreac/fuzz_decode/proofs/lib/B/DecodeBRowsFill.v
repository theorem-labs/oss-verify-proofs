(* libreac/fuzz_decode image B (fuzz_decode.asan-ubsan): proof of the premise row H_CALLOC_FILL of the closing
   composition lib/B/DecodeBClose.v (dec_b_fill), the zero fill asan_calloc makes through
   __interception::real_memset, which is musl memset at 0x92a1c (lib/A/DecodeCallocRt.v zero_fill_specP).

   The run is coreB's machine run of musl memset, lib/B/YE3d.v tfib_memset (tfib_A_musl_memset = 0x92a1c =
   DEC_B_memset), consumed through SRr_msteps; the post is rebuilt as coreB's asan_memset tail leg does
   (lib/B/YE6t.v ms_tail): dest_ok makes every destination byte writable, so not hidden (YE2y.v
   hidden_not_writable); the allocator relation survives by its frame law (YG0d.v AR_frame_law, from
   YG0q.v AR_laws_ok): owned bytes are not destination bytes, visible bytes stay visible, the hidden bytes are
   untouched (munrestrict), and the model changes only by materialization (same_but_materialized_frame).
   No symbol record is needed.  No Axiom, Parameter or Admitted. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YG0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import
YB1v YF0l YF0m YF0x YB1w YE3d YE2y.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import DecodeCallocKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCallocRt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

(* Row H_CALLOC_FILL (DecodeBClose.v:266), in the image-A twin's shape (lib/A/DecodeARowsFill.v dec_a_fill). *)
Theorem dec_b_fill : forall (fx : YK11.FPState) (rc : YM05.RunCeil) (B : asyms), decode_zero_fill_spec_B B.
Proof.
intros fx rc B. unfold decode_zero_fill_spec_B, zero_fill_specP. change decodesegsB0 with tfibsegs.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST.
pose proof (YG0q.AR_laws_ok tfibsegs B) as LAWS.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof YF0x.Hwx_tfa as Hwx.
set (H := w_H W) in *.
assert (DW : forall a, d <= a < d + n -> writable_at tfibsegs (mrestrict H mem) a /\ H (Z_to_bv 64 a) = false).
{ intros a Ha. destruct (HDST a Ha) as (Hw & _ & _).
  split; [exact Hw|]. destruct (H (Z_to_bv 64 a)) eqn:Hh; [|reflexivity].
  exfalso. exact (hidden_not_writable W mem a ltac:(lia) Hh Hw). }
set (nn := Z.to_nat n). assert (Hnn : Z.of_nat nn = n) by (subst nn; lia).
assert (SOK : store_ok tfibsegs (mrestrict H mem) (w64 d) nn = true).
{ apply store_ok_of_all; unfold w64; rewrite unsigned_lit_small by lia; [lia|].
  intros z Hz. pose proof (proj1 (DW (bv_unsigned z) ltac:(lia))) as Wz. unfold writable_at in Wz.
  rewrite Z_to_bv_bv_unsigned in Wz. exact Wz. }
destruct (tfib_memset (w64 d) (w64 x) (w64 n) nn (mrestrict H mem) (seg_rom tfibsegs) regs G10 G11 G12
  ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia) SOK ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia))
  as (regs2 & Hms & A10 & Hkeep).
set (cb := Z_to_bv 8 (bv_unsigned (w64 x) mod 256)) in Hms.
set (m1r := mrestrict H mem) in *. set (m2r := wbytes m1r (w64 d) (repeat cb nn)) in Hms.
set (mem2 := munrestrict H mem m2r).
assert (LEN : Z.of_nat (length (repeat cb nn)) = n) by (rewrite repeat_length; exact Hnn).
assert (M2out : forall z : word, ~ (d <= bv_unsigned z < d + n) -> mem2 z = mem z).
{ intros z Hz. subst mem2 m2r. unfold munrestrict. destruct (H z) eqn:Hh; [reflexivity|].
  assert (Ew : wbytes m1r (w64 d) (repeat cb nn) z = m1r z).
  { destruct (Z_lt_le_dec (bv_unsigned z) d) as [L|L].
    - apply wbytes_below; unfold w64; rewrite ?LEN, unsigned_lit_small by lia; lia.
    - apply wbytes_above. unfold w64. rewrite LEN, unsigned_lit_small by lia. lia. }
  rewrite Ew. subst m1r. unfold mrestrict. rewrite Hh. reflexivity. }
assert (M2in : forall i, 0 <= i < n -> mem2 (Z_to_bv 64 (d + i)) = Some cb).
{ intros i Hi. subst mem2. unfold munrestrict. rewrite (proj2 (DW (d + i) ltac:(lia))).
  subst m2r. rewrite (wbytes_inside (repeat cb nn) m1r (w64 d) (Z_to_bv 64 (d + i)));
    unfold w64; rewrite ?LEN, ?unsigned_lit_small by lia; [|lia|lia].
  replace (Z.to_nat (d + i - d)) with (Z.to_nat i) by lia. apply nth_error_repeat. lia. }
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> aview tfibsegs H mem2 a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply aview_same. apply M2out. rewrite unsigned_lit_small by lia. exact Ha. }
unfold cfg_at. change (w64 DEC_B_memset) with (Z_to_bv 64 tfib_A_musl_memset).
eapply (SRr_msteps tfibsegs Hwx W); [rewrite restrict_mkst_fx; exact Hms|].
intros model' Hsbm _. rewrite (same_but_materialized_wvb md model' Hsbm). cbn [ms_mem mkst].
change (unrestrict H mem (mkst regs2 (v_jalr (getr regs 1) 0) m2r (seg_rom tfibsegs)))
  with (mkst regs2 (v_jalr (getr regs 1) 0) mem2 (seg_rom tfibsegs)).
apply SRr_ret. split; [reflexivity|].
set (md' := with_vm_backing (m_vm_lazy md) (m_vm_materialized model') md).
exists regs2, mem2, md'.
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md (m_vm_materialized model'))) as MF.
fold md' in MF.
split.
{ unfold cfg_at. replace (v_jalr (getr regs 1) 0) with (w64 (raZ regs))
    by (unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra). reflexivity. }
split.
{ apply (al_frame _ _ LAWS ly S W mem md mem2 md' HAR).
  - intros a Hr Hown. apply AV2; [exact Hr | intros Hd'; exact (proj1 (proj2 (HDST a Hd')) Hown)].
  - intros a Hv. rewrite (YE2y.aview_mod _ mem2 a). rewrite (YE2y.aview_mod _ mem a) in Hv.
    assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
    destruct (Z_lt_le_dec a' d) as [L1|L1]; [rewrite AV2 by lia; exact Hv|].
    destruct (Z_lt_le_dec a' (d + n)) as [L2|L2]; [|rewrite AV2 by lia; exact Hv].
    unfold aview, mbyte, mrestrict. fold H. rewrite (proj2 (DW a' ltac:(lia))).
    replace a' with (d + (a' - d)) by lia. rewrite (M2in (a' - d)) by lia. discriminate.
  - apply MF.
  - apply MF.
  - apply MF.
  - exact (YE2y.hs_kept_unrestrict H mem m2r). }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (K : forall rr : bv 5, bv_unsigned rr < 11 \/ 16 < bv_unsigned rr -> getr regs2 rr = getr regs rr).
  { intros rr Hrr. apply Hkeep; intros E; subst rr; vm_compute in Hrr; destruct Hrr as [X|X]; discriminate X. }
  apply K. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
  rewrite Z.mod_small by lia. lia. }
split; [subst md'; apply with_vm_backing_same|].
split; [exact A10|].
split.
{ intros i Hi. unfold aview, mbyte, mrestrict. rewrite (proj2 (DW (d + i) ltac:(lia))), (M2in i Hi). cbn [option_map].
  f_equal. subst cb. unfold w64. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (256 * 2 ^ 56). change (bv_modulus 8) with 256.
  rewrite Z.mod_mod by lia. apply Z.mod_mod_divide. exists (2 ^ 56). reflexivity. }
split.
{ intros a Hr Hd' _. apply AV2; [exact Hr | exact Hd']. }
intros a Hp.
assert (Hr : apresent H mem2 a <-> apresent H mem2 (a mod 2 ^ 64)).
{ unfold apresent. rewrite <- (YE2y.Z_to_bv64_of_mod a). tauto. }
apply (proj2 Hr). clear Hr.
assert (Hp' : apresent H mem (a mod 2 ^ 64)) by (unfold apresent; rewrite (YE2y.Z_to_bv64_of_mod a); exact Hp).
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' d) as [L1|L1]; [| destruct (Z_lt_le_dec a' (d + n)) as [L2|L2]].
2:{ split; [exact (proj2 (DW a' ltac:(lia)))|]. exists cb. replace a' with (d + (a' - d)) by lia. apply M2in. lia. }
all: apply (apresent_same H mem mem2 a');
  [rewrite (M2out (Z_to_bv 64 a')) by (rewrite unsigned_lit_small by lia; lia); reflexivity | exact Hp'].
Qed.
