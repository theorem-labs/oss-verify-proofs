(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/ErrnoGS.v (commit 30a1993588f, c5 + memnorm; file sha256 a5b0e58a7e95) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/ErrnoGS.v at commit 789778cb16f, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* The secondary path's errno add-ons: ErrnoG.v's restatements of AGif4.AIfaceS's fields with errno kept.

   Moved here from ErrnoG.v, names and statements unchanged: aes_depot_t, aes_post_grant_v_t, aes_post_grant_t and
   the record AIfaceSE.  They name AGif4's sfin / skern / CZS; in their own file they keep ErrnoG.v's Require closure
   free of AGif4 and of the files below.  errno_kept / errno_kept_v are ErrnoG.v's.  No arm is proved here.

   The file is image-free: it takes the image classes as AGif4 does ([Context {IM : AImg} {IMS : AImgS}]).

   Require hazard: the Require closure reaches YA08 / YA09 / YA0e through AGif4 (ErrnoGS -> AGif4 -> YA09, AGif4 ->
   YG0b -> YA08 / YA0e), whose non-local
   Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false) (last at YA08.v:1313, YA09.v:3351,
   YA0e.v:3763) escapes Require: a file that Requires this one has lia's conversion of Z.div / Z.modulo to euclidean
   equations switched off, even when it had switched it on.  Consumer fix, one line after its Require block:
   #[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0b YG0g YG0h YG0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0v YK13 YP0n YA05 YA09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseAGS AGif2 AllocG AGif4.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ErrnoG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The Allocate callees, secondary path (AGif4.AIfaceS's parameters).                                               *)
(* Add-ons: ifs_depot (AGif4.v:244-265), whose post frames the raw memory only (AGif4.v:262-263), outside the       *)
(* depot's stack window and [ims_dzone], which AImgS does not keep apart from errno (one form); ifs_post_grant      *)
(* (AGif4.v:301-319), whose view and raw frames (AGif4.v:313-319) exclude ascratch on the grant arm (two forms).     *)
(* No add-on: ifs_post_null (AGif4.v:289-299) is the refusal arm (a0 = PNull), where alloc_leaf_e asks nothing of    *)
(* errno; the other fields state no memory frame.                                                                   *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {IMS : AImgS}.
Local Open Scope am_scope.

(* The add-ons, over the variables they use (AIfaceS's, in AIfaceS's order). *)
Section v.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable nmax : Z.
Variable lmax : Z.
Variable dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop.

(* AIfaceS.ifs_depot with errno kept *)
Definition aes_depot_t : Prop :=
forall inst ly S W mem0 md0 tr (Wy : world im_segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (buf : Z),
ARX inst ly S W mem0 md0 -> U tr S ->
(forall x : word, w_H W x = false -> w_H Wy x = false) ->
(forall x : word, ims_dzone ly (bv_unsigned x) \/ CZS ly inst (bv_unsigned x) -> mem x = mem0 x) ->
(forall k, 1 <= k < 4 -> aview im_segs (w_H Wy) mem (inst + o_sec_mutex + k) = Some 0) ->
getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 im_tp -> YK0s.ret_ok (getr regs 1) ->
(forall i, (i < length tr)%nat -> val_mem im_segs (mrestrict (w_H Wy) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
buf + 8 * 30 <= bv_unsigned (getr regs 2) - ImgBaseAGS.DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - ImgBaseAGS.DEP_STK ->
bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
(forall a, bv_unsigned (getr regs 2) - ImgBaseAGS.DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H Wy) mem a) ->
SRr im_segs Wy (mkCfg (mkst regs (Z_to_bv 64 ims_depot) mem (seg_rom im_segs)) md)
(fun W' c' => W' = Wy /\ exists z regs' mem' mat,
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
  regs_preserved regs regs' /\
  (forall x : word, ~ (bv_unsigned (getr regs 2) - ImgBaseAGS.DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
     ~ ims_dzone ly (bv_unsigned x) -> mem' x = mem x) /\
  errno_kept B mem mem' /\
  (forall a, apresent (w_H Wy) mem a -> apresent (w_H Wy) mem' a) /\
  dpost inst ly S W tr z mem').

(* AIfaceS.ifs_post_grant's premises: errno kept from Allocate's entry ([W], [mem0]) to its return ([Wz], [mem']),
   on the view (the form of AGif4.v:313-315) and on the raw memory (the form of AGif4.v:317-319) *)
Definition aes_post_grant_v_t : Prop :=
forall inst ly S W mem0 md0 n tr regs0 mb grow z Wz mdz regs' mem',
ARX inst ly S W mem0 md0 -> rpre S n -> 64513 <= n < nmax -> blocks_bytes S + n <= lmax -> U tr S ->
ims_wframe W ly regs0 mem0 tr -> getr regs0 11 = w64 inst ->
(grow = true <-> Z.of_nat (length (st_sec_arr S)) = st_sec_reserved S) ->
skern grow W Wz md0 mdz ly mb (ImgBaseAGS.MSv n) (ImgBaseAGS.QSv ly (Z.of_nat (length (st_sec_arr S)))) ->
sfin W ly regs0 mem0 inst n tr (Z.of_nat (length (st_sec_arr S))) (st_sec_reserved S) mb
  (fun zz m => dpost inst ly S W tr zz m) grow z Wz regs' mem' ->
aok S (KDepot tr) z ->
errno_kept_v im_segs B W Wz mem0 mem'.
Definition aes_post_grant_t : Prop :=
forall inst ly S W mem0 md0 n tr regs0 mb grow z Wz mdz regs' mem',
ARX inst ly S W mem0 md0 -> rpre S n -> 64513 <= n < nmax -> blocks_bytes S + n <= lmax -> U tr S ->
ims_wframe W ly regs0 mem0 tr -> getr regs0 11 = w64 inst ->
(grow = true <-> Z.of_nat (length (st_sec_arr S)) = st_sec_reserved S) ->
skern grow W Wz md0 mdz ly mb (ImgBaseAGS.MSv n) (ImgBaseAGS.QSv ly (Z.of_nat (length (st_sec_arr S)))) ->
sfin W ly regs0 mem0 inst n tr (Z.of_nat (length (st_sec_arr S))) (st_sec_reserved S) mb
  (fun zz m => dpost inst ly S W tr zz m) grow z Wz regs' mem' ->
aok S (KDepot tr) z ->
errno_kept B mem0 mem'.
End v.

(* AIfaceS's add-ons (AIfaceS's parameters). *)
Record AIfaceSE (B : asyms) (U : list Z -> astate -> Prop) (mt : Z -> list Z -> M sptr)
(ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (rpre : astate -> Z -> Prop) (nmax lmax : Z) (lpost : astate -> Prop)
(dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop) (mtag stag : Z) : Prop := {
  aes_depot : aes_depot_t B U ARX dpost;
  aes_post_grant_v : aes_post_grant_v_t B U ARX rpre nmax lmax dpost;
  aes_post_grant : aes_post_grant_t B U ARX rpre nmax lmax dpost
}.
End s.
