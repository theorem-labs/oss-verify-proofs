(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgNearS.v at 92636bfca57b; the module paths name reac-pw/fuzz_rate, and the image is reac-pw/fuzz_rate's image A (fuzz_rate.asan). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgNearS.v at b089f28d962e; the image is reac-pw/fuzz_rate's image B (fuzz_rate.asan-ubsan, lib/AU/Img0.v). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgNearSB.v at 7e722b95884; relocated to reac-pw/fuzz_role's ASan image B (fuzz_role.asan-ubsan, lib/AU/Img0.v): the module paths name reac-pw/fuzz_role. *)
(* The seam of reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0) between the lib/Lib walks over the image
   lib/AU/Img0.v rsegs and the call-site form the harness continues from (SRr, lib/Reusable/YA0n.v).

   A lib/Lib walk (lib/AU/RPgNearC.v is one) asks `mem_inv rsegs m` of the store it runs on. The harness's store at a
   call site is `mrestrict (w_H W) memc`, of which that is not derivable, so the walk runs on the NORMALIZED store
     normalize_cj rsegs (mrestrict (w_H W) memc)                                   (lib/MemNorm.v)
   which drops every stored byte at a read-only address and every stored byte at or above TASK_SIZE outside the
   image; `mem_inv` and `task_mem` hold of it by construction. This file moves the run between the two stores and
   into SRr:
   - read agreement (MemNorm.ro_agree) from the contract's `rom_view` premise (YG0d.v): every byte of a read-only
     segment reads as the image's;
   - the run: the walk's `evt` on the normalized store gives an `evt` on the harness's restricted store ending in a
     state related by `ms_rel_cj` that keeps the dropped bytes (`cj_same`), through MemNorm.evt_normalize_cj; the
     register file is transported to the harness's by Lib/RegisterBridge; lib/Lib's `msteps` is the same relation as
     YK0i's, so YA0n.SRr_msteps closes the join (near_srr_of_norm_evt);
   - the small reader bridges the two halves need: the harness reads memory through `aview rsegs (w_H W) mem`
     (YG0n.v), a Z -> option Z reader over `mrestrict (w_H W) mem`, and lib/Lib reads it through
     `Mem.mrd rsegs m (Mem.wa a)` over the same store; the two are the same function (near_aview_mrd, by
     reflexivity), so a view equation becomes a lib/Lib `bytes_at` and an 8-byte cell value becomes `le8`.

   These are short generic lemmas; the shapes follow proofs/libreac/fuzz_boxreg/lib/A/FMgxa_bridge.v and
   proofs/libreac/fuzz_boxreg/lib/A/Rt/FMgxaSeamNorm.v at 781f46bc05c, and the le8 / le_byte digit bridges
   follow this unit's lib/KindBGlue.v (word_mem_le8, bytes_at_le8_word). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YK11 YK14 YK0s YK15 YK18 YK0i YP09 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require
PropExec MState Mem Exec Frame FP Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* lib/Lib and lib/Reusable have modules of the same short names; every lib/Lib one is named by its full path. *)
Module LPE := OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib.PropExec.
Module LMS := OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib.MState.
Module LM := OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib.Mem.
Module LEx := OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib.Exec.
Module LF := OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib.Frame.
Module LFP := OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib.FP.
Module R6 := OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib.Regs6ss.
Module RBr := OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib.RegisterBridge.
Module MN := OSSVerify.Proofs.reac_pw.fuzz_role.lib.MemNorm.

(* ===================================================================================== *)
(* 0. the image                                                                           *)
(* ===================================================================================== *)

Lemma near_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* MemNorm's W^X side condition: no writable executable segment overlaps a read-only one *)
Lemma near_wx_apart : MN.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma near_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (HB : forallb (fun s : Segment => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd) rsegs = true)
by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB sg Hin) as H. apply Z.leb_le in H. lia.
Qed.

Lemma near_fs_some : forall (l : list Segment) x n seg, find_segment l x n = Some seg ->
In seg l /\ Z.of_N (seg_base seg) <= x /\ x + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
induction l as [|s l IH]; intros x n seg H; cbn in H; [discriminate|].
match type of H with context [if ?c then _ else _] => destruct c eqn:E end.
- injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1, E2.
split; [left; reflexivity | lia].
- destruct (IH x n seg H) as (H1 & H2). split; [right; exact H1 | exact H2].
Qed.

Lemma near_fs_none : forall a, ~ in_img rsegs a -> find_segment rsegs a 1 = None.
Proof.
intros a Hn. destruct (find_segment rsegs a 1) as [sg|] eqn:E; [|reflexivity].
exfalso. destruct (near_fs_some rsegs a 1 sg E) as (Hin & H1 & H2).
apply Hn. exists sg. split; [exact Hin | lia].
Qed.

Lemma near_rom_none : forall a, 0 <= a < 2 ^ 64 -> ~ in_img rsegs a -> LPE.seg_rom rsegs (LM.wa a) = None.
Proof.
intros a Ha Hn. apply (MN.seg_rom_unmapped rsegs).
rewrite LM.wa_unsigned by exact Ha. apply near_fs_none, Hn.
Qed.

(* a byte off the image and below TASK_SIZE is not dropped by the normalization *)
Lemma near_keep : forall a, 0 <= a < TASK_SIZE -> ~ in_img rsegs a -> MN.cj_drop rsegs (LM.wa a) = false.
Proof.
intros a Ha Hn. unfold TASK_SIZE in Ha.
apply MN.cj_drop_false_intro.
- unfold LM.ro_addr. rewrite LM.wa_unsigned by lia. rewrite near_fs_none by exact Hn. reflexivity.
- right. rewrite LM.wa_unsigned by lia. unfold TASK_SIZE. lia.
Qed.

(* ===================================================================================== *)
(* 1. the reader bridges                                                                  *)
(* ===================================================================================== *)

Section Rd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma near_aview_mrd : forall (H : word -> bool) mem (x : word),
aview rsegs H mem (bv_unsigned x)
= option_map (fun b : byte => bv_unsigned b) (LM.mrd rsegs (mrestrict H mem) x).
Proof.
intros H mem x. unfold aview, mbyte, LM.mrd. rewrite LMS.Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma near_byte_eq : forall o1 o2 : option byte,
option_map (fun b : byte => bv_unsigned b) o1 = option_map (fun b : byte => bv_unsigned b) o2 -> o1 = o2.
Proof.
intros [b1|] [b2|] E; cbn [option_map] in E; try discriminate E; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma near_mrd_of_view : forall (H : word -> bool) mem a v, 0 <= a < 2 ^ 64 ->
aview rsegs H mem a = Some v -> LM.mrd rsegs (mrestrict H mem) (LM.wa a) = Some (Z_to_bv 8 v).
Proof.
intros H mem a v Ha E.
pose proof (near_aview_mrd H mem (LM.wa a)) as E'.
rewrite (LM.wa_unsigned a Ha), E in E'.
destruct (LM.mrd rsegs (mrestrict H mem) (LM.wa a)) as [bb|] eqn:Em; cbn [option_map] in E'; [|discriminate E'].
injection E' as E'. subst v. f_equal. symmetry. apply bv_eq. rewrite Z_to_bv_unsigned.
apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* read agreement at the harness's restricted store, from the contract's rom_view premise *)
Lemma near_ro_agree : forall (W : world rsegs) memc,
rom_view rsegs W memc -> MN.ro_agree rsegs (mrestrict (w_H W) memc).
Proof.
intros W memc HR x Hro.
assert (Hin : in_rom rsegs (bv_unsigned x)).
{ unfold LM.ro_addr in Hro.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [sg|] eqn:E; [|discriminate Hro].
  destruct (near_fs_some rsegs _ _ sg E) as (Hsg & H1 & H2).
  exists sg. split; [exact Hsg|]. split; [apply negb_true_iff in Hro; exact Hro | lia]. }
pose proof (HR (bv_unsigned x) Hin) as E.
rewrite LMS.Z_to_bv_bv_unsigned in E.
apply near_byte_eq. rewrite <- near_aview_mrd. exact E.
Qed.

End Rd.

(* ===================================================================================== *)
(* 2. 8-byte cells: val_mem (the harness's) and bytes_at of le8 (lib/Lib's)                *)
(* ===================================================================================== *)

Lemma near_nth_le_bytes : forall n z k, (k < n)%nat ->
nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. do 3 f_equal. lia.
Qed.

Lemma near_le_byte_bv : forall v k, 0 <= v < 2 ^ 64 ->
Z_to_bv 8 (YO0f.le_byte v 8 k) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
intros v k Hv. unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64.
rewrite (Z.mod_small v (2 ^ 64)) by lia.
apply LM.Z_to_bv8_mod. change 256 with (2 ^ 8). apply Z.mod_mod. lia.
Qed.

Section Cells. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma near_val_bytes : forall m a v, 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 ->
val_mem rsegs m a 8 v -> LM.bytes_at rsegs m a (LM.le8 (Z_to_bv 64 v)).
Proof.
intros m a v Hv Ha Hb Hw. split; [exact Ha|]. rewrite LM.length_le8. split; [lia|].
intros i Hi.
unfold LM.le8, word_to_le_bytes. rewrite near_nth_le_bytes by exact Hi.
rewrite LMS.unsigned_lit by lia. rewrite <- near_le_byte_bv by exact Hv. exact (Hw i Hi).
Qed.

Lemma near_bytes_val : forall m a (w : word),
LM.bytes_at rsegs m a (LM.le8 w) -> val_mem rsegs m a 8 (bv_unsigned w).
Proof.
intros m a w (Ha & Hb & H) k Hk.
pose proof (bv_unsigned_in_range 64 w) as Hr. unfold bv_modulus in Hr.
change (2 ^ Z.of_N 64) with (2 ^ 64) in Hr.
rewrite near_le_byte_bv by exact Hr.
rewrite LM.length_le8 in H. specialize (H k Hk). unfold LM.le8, word_to_le_bytes in H.
rewrite near_nth_le_bytes in H by exact Hk. exact H.
Qed.

End Cells.

(* ===================================================================================== *)
(* 3. the run: a walk on the normalized store, read at a harness call site                *)
(* ===================================================================================== *)

(* lib/Lib's step relation is the harness's: each step of either asks the same two things *)
Lemma near_msteps : forall ms ms', LEx.msteps rsegs ms ms' -> YK0i.msteps rsegs ms ms'.
Proof.
intros ms ms' H. induction H as [ms | ms ms1 ms2 Hstep _ IH].
- apply YK0i.mst_refl.
- destruct Hstep as [Hsvc Hok]. eapply YK0i.mst_step; [exact Hsvc | exact Hok | exact IH].
Qed.

Lemma near_mrestrict_munrestrict : forall (H : word -> bool) full m x,
mrestrict H (munrestrict H full m) x = mrestrict H m x.
Proof. intros H full m x. unfold mrestrict, munrestrict. destruct (H x); reflexivity. Qed.

Lemma near_ret_pc : forall k : word, YK0s.ret_ok k -> LMS.ret_pc k = k.
Proof.
intros k Hk. unfold YK0s.ret_ok, v_jalr, jalr_tgtZ in Hk. rewrite Z.add_0_r in Hk.
pose proof (bv_unsigned_in_range 64 k) as Hr. unfold bv_modulus in Hr.
change (2 ^ Z.of_N 64) with (2 ^ 64) in Hr.
assert (Hz : bv_unsigned k = Z.land (bv_unsigned k) (-2) mod 2 ^ 64).
{ rewrite <- Hk at 1. rewrite Z_to_bv_unsigned. reflexivity. }
assert (Hm2 : forall x : Z, (x mod 2 ^ 64) mod 2 = x mod 2).
{ intros x. change ((x mod 2 ^ 64) mod 2) with ((x mod 2 ^ 64) mod 2 ^ 1).
  change (x mod 2) with (x mod 2 ^ 1). rewrite <- !Z.land_ones by lia.
  rewrite <- Z.land_assoc. reflexivity. }
assert (Hl2 : forall x : Z, Z.land x (-2) mod 2 = 0).
{ intros x. change (Z.land x (-2) mod 2) with (Z.land x (-2) mod 2 ^ 1).
  rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. apply Z.land_0_r. }
assert (Hm : bv_unsigned k mod 2 = 0) by (rewrite Hz, Hm2; apply Hl2).
rewrite <- (LMS.Z_to_bv_bv_unsigned k). apply LMS.ret_pc_even; [exact Hr | exact Hm].
Qed.

Section Run. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The premise in the shape a lib/Lib walk delivers, on the normalized store; the conclusion in the shape the
   harness continues from. can is the walk's end state with the canonical register map, msf the harness's. *)
Theorem near_srr_of_norm_evt :
forall (W : world rsegs) (pc : Z) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model)
(Q : machine_state -> Prop) (POST : world rsegs -> config -> Prop),
rom_view rsegs W memc ->
LEx.evt rsegs Q
(LMS.MS (R6.mkR_of regs) (@fp_regs fx) (Z_to_bv 64 pc) (@fp_csr fx) None
(MN.normalize_cj rsegs (mrestrict (w_H W) memc)) (LPE.seg_rom rsegs)) ->
(forall (msf can : machine_state) (sq : machine_state) (model' : Model),
Q sq -> MN.ms_rel_cj rsegs can sq ->
MN.cj_same rsegs (mrestrict (w_H W) memc) (ms_mem can) ->
R6.ms_eqv can msf ->
same_but_materialized mdc model' -> hclean (w_H W) msf ->
POST W (mkCfg (unrestrict (w_H W) memc msf) model')) ->
SRr rsegs W (cfg_at rsegs pc regs memc mdc) POST.
Proof.
intros W pc regs memc mdc Q POST HRV HEV HK.
pose proof (MN.evt_normalize_cj rsegs Q (R6.mkR_of regs) (@fp_regs fx) (Z_to_bv 64 pc) (@fp_csr fx) None
(mrestrict (w_H W) memc) (LPE.seg_rom rsegs) near_wx_apart (near_ro_agree W memc HRV) HEV) as EV1.
pose proof (RBr.canonical_contract_transport rsegs _
(restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 pc) memc (YK11.seg_rom rsegs))) EV1) as EV2.
destruct EV2 as (msf & Hms & can & (sq & HQ & Hrel & Hsame) & Heqv).
unfold cfg_at.
apply (SRr_msteps rsegs near_wx W (@YK11.mkst fx regs (w64 pc) memc (YK11.seg_rom rsegs)) msf mdc POST).
- exact (near_msteps _ _ Hms).
- intros model' Hsm Hcl. apply SRr_ret.
  exact (HK msf can sq model' HQ Hrel Hsame Heqv Hsm Hcl).
Qed.

End Run.
