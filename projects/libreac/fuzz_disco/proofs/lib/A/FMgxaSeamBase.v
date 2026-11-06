(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMgxaSeamBase.v (a working branch 3e35620c52e); relocated to libreac/fuzz_disco.asan by reloc.py (target disco-A): module paths changed; 0 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table: this file's rows in provenance/evidence/g9-gxa/g9tool/g9-table-disco-A.tsv); names: record RT_IImgA -> . *)
(* Step 1 of the evt -> SRr seam at musl vfprintf: the PRIMITIVE BRIDGES between the harness's
   view of memory and the CJ tree's.

   The harness reads memory through `aview segs (w_H W) mem` (YG0n.v:18), a Z -> option Z reader
   over the restricted store `mrestrict (w_H W) mem`.  The CJ tree reads it through
   `Mem.mrd segs m (Mem.wa a)` (CJ/Lib/Mem.v:58) over the same store.  The two are the same
   function (aview_mrd, by reflexivity), so every fact the shared contract states as a view
   equation becomes a CJ `bytes_at`, and every `writable_at` becomes a CJ `wr_at`.

   This file holds only what both halves of the seam need: the reader identity, bytes, words,
   writability, mem_inv, and the return-address and configuration shapes.  The ASan shadow lives in
   FMgxaSeamShadow.v and the contract translation in FMgxaSeam*.v. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0d YA0n YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require Mem Frame Cells Step MState.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.I Require Import RecAsanVfA.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import FMgxa_bridge.
Import ListNotations.
Local Open Scope Z_scope.

(* the store the CJ walk runs on, from the harness's world and memory *)
Definition cjstore (H : word -> bool) (mem : word -> option byte) : word -> option byte :=
  mrestrict H mem.

(* a Theorem Labs lane's premise (a working branch 445e498a469 lib/A/FMbz_str.v:288), restated here because
   a Theorem Labs lane dropped it from asnprintf_realizes (analyses/rtprintf/design/SNPRINTF-SHARED.md (a working branch 952598da9f3b) section 3): the mutable
   store holds no byte at a read-only address and none above the user address limit.  The CJ engine
   asks for it under the name mem_inv at every walk. *)
Definition store_cleanU (H : word -> bool) (mem : word -> option byte) : Prop :=
  forall a : word, cjstore H mem a <> None ->
    Mem.ro_addr tfibsegs a = false /\ bv_unsigned a < TASK_SIZE.

Section B. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- the reader identity ---- *)
Lemma aview_mrd : forall H mem a,
  aview tfibsegs H mem a
  = option_map (fun b : byte => bv_unsigned b) (Mem.mrd tfibsegs (cjstore H mem) (Mem.wa a)).
Proof. reflexivity. Qed.

Lemma byte_roundtrip : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small, bv_unsigned_in_range. Qed.

Lemma mrd_of_view : forall H mem a v,
  aview tfibsegs H mem a = Some v -> Mem.mrd tfibsegs (cjstore H mem) (Mem.wa a) = Some (Z_to_bv 8 v).
Proof.
intros H mem a v E. rewrite aview_mrd in E.
destruct (Mem.mrd tfibsegs (cjstore H mem) (Mem.wa a)) as [b|] eqn:Eb; cbn in E; [|discriminate].
injection E as <-. rewrite byte_roundtrip. reflexivity.
Qed.

(* ---- bytes ---- *)
Definition zb8 (l : list Z) : list byte := map (Z_to_bv 8) l.

Lemma zb8_length : forall l, length (zb8 l) = length l.
Proof. intros. unfold zb8. apply length_map. Qed.

Lemma bytes_at_of_view : forall H mem p (l : list Z),
  0 <= p -> p + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall i, (i < length l)%nat -> aview tfibsegs H mem (p + Z.of_nat i) = Some (nth i l 0)) ->
  Mem.bytes_at tfibsegs (cjstore H mem) p (zb8 l).
Proof.
intros H mem p l Hp Hhi HV. split; [exact Hp|]. split; [rewrite zb8_length; exact Hhi|].
intros i Hi. rewrite zb8_length in Hi.
rewrite (mrd_of_view H mem (p + Z.of_nat i) (nth i l 0) (HV i Hi)).
unfold zb8. symmetry. apply map_nth_error. apply nth_error_nth'. exact Hi.
Qed.

(* ---- writability ---- *)
Lemma wr_at_of_writable : forall H mem p n,
  0 <= p -> p + n <= 2 ^ 64 ->
  (forall a, p <= a < p + n -> writable_at tfibsegs (cjstore H mem) a) ->
  Mem.wr_at tfibsegs (cjstore H mem) p n.
Proof.
intros H mem p n Hp Hhi HW. split; [exact Hp|]. split; [exact Hhi|].
intros i Hi. exact (HW (p + i) ltac:(lia)).
Qed.

(* ---- mem_inv ---- *)
Lemma mem_inv_of_store_clean : forall H mem,
  store_cleanU H mem -> Mem.mem_inv tfibsegs (cjstore H mem).
Proof.
intros H mem HC. apply Mem.mem_inv_intro. intros a b E.
destruct (HC a ltac:(rewrite E; discriminate)) as [Hro Hlt].
split; [exact Hro | right; exact Hlt].
Qed.

(* ---- the return address ---- *)
(* ecall_pre carries YK0s.ret_ok (getr regs 1): the saved ra has bit 0 clear, so the CJ walk's
   `ret_pc ra` is the harness's `w64 (raZ regs)`. *)
Lemma w64_unsigned : forall x : word, w64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small, bv_unsigned_in_range. Qed.

Lemma ret_pc_raZ : forall (ra : word), YK0s.ret_ok ra -> MState.ret_pc ra = w64 (bv_unsigned ra).
Proof.
intros ra H. unfold YK0s.ret_ok, v_jalr, jalr_tgtZ in H. rewrite Z.add_0_r in H.
assert (Hr : 0 <= bv_unsigned ra < 2 ^ 64).
{ pose proof (bv_unsigned_in_range 64 ra) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in R. exact R. }
assert (HM : (Z.land (bv_unsigned ra) (-2)) mod 2 ^ 64 = bv_unsigned ra).
{ apply (f_equal (fun x : word => bv_unsigned x)) in H.
  rewrite Z_to_bv_unsigned in H. unfold bv_wrap in H.
  change (bv_modulus 64) with (2 ^ 64)%Z in H. exact H. }
assert (HO : Z.odd (Z.land (bv_unsigned ra) (-2)) = false).
{ rewrite <- Z.bit0_odd, Z.land_spec.
  replace (Z.testbit (-2) 0) with false by reflexivity. apply andb_false_r. }
assert (HX : bv_unsigned ra mod 2 = 0).
{ assert (Hy : Z.even (Z.land (bv_unsigned ra) (-2)) = true)
    by (rewrite <- Z.negb_odd, HO; reflexivity).
  apply Z.even_spec in Hy. destruct Hy as [m Hm].
  rewrite <- HM, Hm.
  replace (2 ^ 64)%Z with (2 * 2 ^ 63)%Z by (vm_compute; reflexivity).
  rewrite Z.mul_mod_distr_l by lia.
  rewrite Z.mul_comm, Z_mod_mult. reflexivity. }
replace (MState.ret_pc ra) with (MState.ret_pc (w64 (bv_unsigned ra)))
  by (rewrite w64_unsigned; reflexivity).
unfold w64. apply MState.ret_pc_even; assumption.
Qed.

End B.
