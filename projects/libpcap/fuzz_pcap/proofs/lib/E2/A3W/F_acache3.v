(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation acache_rec t c := (t + 208 + c * 80) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition cb_sm (s : Z) : Z :=
  let x1 := Z.lor s (Z.shiftr s 1) in let x2 := Z.lor x1 (Z.shiftr x1 2) in let x3 := Z.lor x2 (Z.shiftr x2 4) in
  let x4 := Z.lor x3 (Z.shiftr x3 8) in let x5 := Z.lor x4 (Z.shiftr x4 16) in let x6 := Z.lor x5 (Z.shiftr x5 32) in
  Z.lxor x6 18446744073709551615.
End CANSEC1.
Arguments cb_sm : simpl never.
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition cb_clz (y : Z) : Z :=
  let a := (y - Z.land (Z.shiftr y 1) 6148914691236517205) mod 18446744073709551616 in
  let b := Z.land a 3689348814741910323 + Z.land (Z.shiftr a 2) 3689348814741910323 in
  Z.shiftr ((Z.land ((b + Z.shiftr (b mod 18446744073709551616) 4) mod 18446744073709551616) 1085102592571150095
             * 72340172838076673) mod 18446744073709551616) 56.
End CANSEC2.
Arguments cb_clz : simpl never.
Section CANSEC3. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition cb_fin (s : Z) : Z :=
  let k := cb_clz (cb_sm s) in let sh := (bv_swrap 32 (62 - k)) mod 18446744073709551616 in
  Z.lor (Z.lxor ((Z.shiftl k 1) mod 18446744073709551616) 126) (Z.land (Z.shiftr s (sh mod 64)) 1)
  + Z.b2z (0 <? Z.land s (Z.lxor ((bv_swrap 32 (Z.shiftl 18446744073709551615 (sh mod 32))) mod 18446744073709551616) 18446744073709551615))
  + -2.
End CANSEC3.
Arguments cb_fin : simpl never.
Section CANSEC4. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition cb_sm_ok (s : Z) : bool :=
  negb (s mod 8 =? 0) || (let y := cb_sm s in let k := cb_clz y in (0 <=? y) && (y <? 2^64) && (47 <=? k) && (k <=? 54)).
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma mod64_land : forall x, x mod 18446744073709551616 = Z.land x 18446744073709551615.
Proof. intros x. change 18446744073709551616 with (2^64). change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity. Qed.
#[using="Type"] Lemma mod32_land : forall x, x mod 4294967296 = Z.land x 4294967295.
Proof. intros x. change 4294967296 with (2^32). change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity. Qed.
#[using="Type"] Lemma forallb_range_ext : forall f g, (forall z, f z = g z) -> forall n lo, forallb_range f lo n = forallb_range g lo n.
Proof. intros f g H n. induction n as [|n IH]; intros lo; cbn [forallb_range]; [reflexivity|]. rewrite H, IH. reflexivity. Qed.
Definition cb_clz_f (y : Z) : Z :=
  let a := Z.land (y - Z.land (Z.shiftr y 1) 6148914691236517205) 18446744073709551615 in
  let b := Z.land a 3689348814741910323 + Z.land (Z.shiftr a 2) 3689348814741910323 in
  Z.shiftr (Z.land (Z.land (Z.land (b + Z.shiftr (Z.land b 18446744073709551615) 4) 18446744073709551615) 1085102592571150095
             * 72340172838076673) 18446744073709551615) 56.
#[using="Type"] Lemma cb_clz_f_eq : forall y, cb_clz y = cb_clz_f y.
Proof. intros y. unfold cb_clz, cb_clz_f. rewrite !mod64_land. reflexivity. Qed.
Definition cb_sm_ok_f (s : Z) : bool :=
  negb (s mod 8 =? 0) || (let y := cb_sm s in let k := cb_clz_f y in (0 <=? y) && (y <? 2^64) && (47 <=? k) && (k <=? 54)).
#[using="Type"] Lemma cb_sm_ok_f_eq : forall s, cb_sm_ok s = cb_sm_ok_f s.
Proof. intros s. unfold cb_sm_ok, cb_sm_ok_f. rewrite cb_clz_f_eq. reflexivity. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma mod8_land : forall x, x mod 8 = Z.land x 7.
Proof. intros x. change 8 with (2^3). change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Definition cb_sm_ok_g (s : Z) : bool :=
  if Z.land s 7 =? 0 then (let y := cb_sm s in let k := cb_clz_f y in (0 <=? y) && (y <? 18446744073709551616) && (47 <=? k) && (k <=? 54)) else true.
#[using="Type"] Lemma cb_sm_ok_g_eq : forall s, cb_sm_ok s = cb_sm_ok_g s.
Proof. intros s. rewrite cb_sm_ok_f_eq. unfold cb_sm_ok_f, cb_sm_ok_g. rewrite mod8_land. destruct (Z.land s 7 =? 0); reflexivity. Qed.
#[using="Type"] Lemma cb_sm_ok_all : forallb_range cb_sm_ok 513 (Z.to_nat (65536 - 513 + 1)) = true.
Proof. rewrite (forallb_range_ext cb_sm_ok cb_sm_ok_g cb_sm_ok_g_eq). vm_cast_no_check (eq_refl true). Qed.   (* [comment removed for export] *)
Local Opaque cb_sm cb_clz.
Local Strategy expand [cb_sm_ok].
#[using="Type"] Lemma cb_sm_ok_sound : forall s, cb_sm_ok s = true -> s mod 8 = 0 -> 0 <= cb_sm s < 2^64 /\ 47 <= cb_clz (cb_sm s) <= 54.
Proof.
  intros z Hz M8. unfold cb_sm_ok in Hz. cbv zeta in Hz. replace (z mod 8 =? 0) with true in Hz by (symmetry; apply Z.eqb_eq; exact M8). cbn [negb orb] in Hz.
  rewrite !Bool.andb_true_iff in Hz. destruct Hz as [[[H1 H2] H3] H4].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
  repeat split; assumption.
Qed.
#[using="Type"] Lemma cb_sm_range : forall s, 513 <= s <= 65536 -> s mod 8 = 0 -> 0 <= cb_sm s < 2^64 /\ 47 <= cb_clz (cb_sm s) <= 54.
Proof.
  exact (range_by_compute (fun s => s mod 8 = 0 -> 0 <= cb_sm s < 2^64 /\ 47 <= cb_clz (cb_sm s) <= 54) cb_sm_ok 513 65536 cb_sm_ok_sound cb_sm_ok_all).
Qed.
Local Transparent cb_sm cb_clz.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bv_swrap32_f (x : Z) : Z := Z.land (x + 2147483648) 4294967295 - 2147483648.
#[using="Type"] Lemma bv_swrap32_f_eq : forall x, bv_swrap 32 x = bv_swrap32_f x.
Proof.
  intros x. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, bv_swrap32_f. change (2 ^ Z.of_N 32) with 4294967296.
  change (4294967296 `div` 2) with 2147483648. rewrite mod32_land. reflexivity.
Qed.
Definition cb_fin_f (s : Z) : Z :=
  let k := cb_clz_f (cb_sm s) in let sh := Z.land (bv_swrap32_f (62 - k)) 18446744073709551615 in
  Z.lor (Z.lxor (Z.land (Z.shiftl k 1) 18446744073709551615) 126) (Z.land (Z.shiftr s (sh mod 64)) 1)
  + Z.b2z (0 <? Z.land s (Z.lxor (Z.land (bv_swrap32_f (Z.shiftl 18446744073709551615 (sh mod 32))) 18446744073709551615) 18446744073709551615))
  + -2.
#[using="Type"] Lemma cb_fin_f_eq : forall s, cb_fin s = cb_fin_f s.
Proof. intros s. unfold cb_fin, cb_fin_f. rewrite cb_clz_f_eq, !bv_swrap32_f_eq, !mod64_land. reflexivity. Qed.
#[using="Type"] Lemma cb_class_chk_eq : forall z, (negb (z mod 8 =? 0) || Z.eqb (cb_fin z mod 2^64) (class_id z mod 2^64))
  = (negb (z mod 8 =? 0) || Z.eqb (Z.land (cb_fin_f z) 18446744073709551615) (Z.land (class_id z) 18446744073709551615)).
Proof. intros z. rewrite cb_fin_f_eq. change (2^64) with 18446744073709551616. rewrite !mod64_land. reflexivity. Qed.
Definition cb_class_g (z : Z) : bool :=
  if Z.land z 7 =? 0 then Z.eqb (Z.land (cb_fin_f z) 18446744073709551615) (Z.land (class_id z) 18446744073709551615) else true.
#[using="Type"] Lemma cb_class_g_eq : forall z, (negb (z mod 8 =? 0) || Z.eqb (cb_fin z mod 2^64) (class_id z mod 2^64)) = cb_class_g z.
Proof. intros z. rewrite cb_class_chk_eq. unfold cb_class_g. rewrite mod8_land. destruct (Z.land z 7 =? 0); reflexivity. Qed.
#[using="Type"] Lemma cb_fin_class_all : forall z, 513 <= z <= 65536 -> z mod 8 = 0 -> Z_to_bv 64 (cb_fin z) = Z_to_bv 64 (class_id z).
Proof.
  apply (range_bv_eq8 cb_fin class_id 513 65536).
  erewrite forallb_range_ext; [| intros z; exact (cb_class_g_eq z)].   (* [comment removed for export] *)
  vm_cast_no_check (eq_refl true).
Qed.

#[using="Type"] Lemma classblock_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (size : Z),
  513 <= size <= 65536 -> size mod 8 = 0 ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' => exists a2' a4' a5' a6' a7' t0' t1',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 (class_id size)) s1 a0 a1 a2' a3 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x3851c) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 size) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38440) fc None m (seg_rom asegs)).
Proof.
  intros until size. intros SZ M8 RIMG RTLS. pose proof (cb_sm_range size SZ M8) as [CBR CLZ].
  do 29 zstep. setreg 12 (Z_to_bv 64 (cb_sm size)) ltac:(reflexivity).            (* [comment removed for export] *)
  do 14 zstep. setreg 12 (Z_to_bv 64 (cb_clz (cb_sm size))) ltac:(reflexivity).   (* [comment removed for export] *)
  do 12 zstep. setreg 8 (Z_to_bv 64 (cb_fin size)) ltac:(reflexivity).            (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 (class_id size))
    ltac:(symmetry; revert M8; revert SZ; clear; revert size;
          exact cb_fin_class_all).   (* [comment removed for export] *)
  apply evtF_done. do 7 eexists. reflexivity.
Qed.
End CANSEC4.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache2.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation acache_rec t c := (t + 208 + c * 80) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition cb_sm (s : Z) : Z :=
  let x1 := Z.lor s (Z.shiftr s 1) in let x2 := Z.lor x1 (Z.shiftr x1 2) in let x3 := Z.lor x2 (Z.shiftr x2 4) in
  let x4 := Z.lor x3 (Z.shiftr x3 8) in let x5 := Z.lor x4 (Z.shiftr x4 16) in let x6 := Z.lor x5 (Z.shiftr x5 32) in
  Z.lxor x6 18446744073709551615.
End CANSEC1.
Arguments cb_sm : simpl never.
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition cb_clz (y : Z) : Z :=
  let a := (y - Z.land (Z.shiftr y 1) 6148914691236517205) mod 18446744073709551616 in
  let b := Z.land a 3689348814741910323 + Z.land (Z.shiftr a 2) 3689348814741910323 in
  Z.shiftr ((Z.land ((b + Z.shiftr (b mod 18446744073709551616) 4) mod 18446744073709551616) 1085102592571150095
             * 72340172838076673) mod 18446744073709551616) 56.
End CANSEC2.
Arguments cb_clz : simpl never.
Section CANSEC3. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition cb_fin (s : Z) : Z :=
  let k := cb_clz (cb_sm s) in let sh := (bv_swrap 32 (62 - k)) mod 18446744073709551616 in
  Z.lor (Z.lxor ((Z.shiftl k 1) mod 18446744073709551616) 126) (Z.land (Z.shiftr s (sh mod 64)) 1)
  + Z.b2z (0 <? Z.land s (Z.lxor ((bv_swrap 32 (Z.shiftl 18446744073709551615 (sh mod 32))) mod 18446744073709551616) 18446744073709551615))
  + -2.
End CANSEC3.
Arguments cb_fin : simpl never.
Section CANSEC4. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition cb_sm_ok (s : Z) : bool :=
  negb (s mod 8 =? 0) || (let y := cb_sm s in let k := cb_clz y in (0 <=? y) && (y <? 2^64) && (47 <=? k) && (k <=? 54)).
(* [comment removed for export] *)
#[using="Type"] Lemma cb_sm_ok_all : forallb_range cb_sm_ok 513 (Z.to_nat (65536 - 513 + 1)) = true.
Proof.   (* [comment removed for export] *)
  assert (E1 : cb_sm = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.cb_sm) by reflexivity.
  assert (E2 : cb_clz = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.cb_clz) by reflexivity.
  assert (E : cb_sm_ok = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.cb_sm_ok) by (unfold cb_sm_ok, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.cb_sm_ok; rewrite E1, E2; reflexivity).
  assert (E0 : forallb_range = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.forallb_range) by reflexivity.   (* [comment removed for export] *)
  rewrite E0, E. exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.cb_sm_ok_all.
Qed.
Local Opaque cb_sm cb_clz.
Local Strategy expand [cb_sm_ok].
#[using="Type"] Lemma cb_sm_ok_sound : forall s, cb_sm_ok s = true -> s mod 8 = 0 -> 0 <= cb_sm s < 2^64 /\ 47 <= cb_clz (cb_sm s) <= 54.
Proof.
  intros z Hz M8. unfold cb_sm_ok in Hz. cbv zeta in Hz. replace (z mod 8 =? 0) with true in Hz by (symmetry; apply Z.eqb_eq; exact M8). cbn [negb orb] in Hz.
  rewrite !Bool.andb_true_iff in Hz. destruct Hz as [[[H1 H2] H3] H4].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
  repeat split; assumption.
Qed.
#[using="Type"] Lemma cb_sm_range : forall s, 513 <= s <= 65536 -> s mod 8 = 0 -> 0 <= cb_sm s < 2^64 /\ 47 <= cb_clz (cb_sm s) <= 54.
Proof.
  exact (range_by_compute (fun s => s mod 8 = 0 -> 0 <= cb_sm s < 2^64 /\ 47 <= cb_clz (cb_sm s) <= 54) cb_sm_ok 513 65536 cb_sm_ok_sound cb_sm_ok_all).
Qed.
Local Transparent cb_sm cb_clz.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma cb_fin_class_all : forall z, 513 <= z <= 65536 -> z mod 8 = 0 -> Z_to_bv 64 (cb_fin z) = Z_to_bv 64 (class_id z).
Proof.   (* [comment removed for export] *)
  assert (E1 : cb_sm = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.cb_sm) by reflexivity.
  assert (E2 : cb_clz = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.cb_clz) by reflexivity.
  assert (E : cb_fin = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.cb_fin) by (unfold cb_fin, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.cb_fin; rewrite E1, E2; reflexivity).
  rewrite E. exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.cb_fin_class_all.
Qed.

#[using="Type"] Lemma classblock_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (size : Z),
  513 <= size <= 65536 -> size mod 8 = 0 ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' => exists a2' a4' a5' a6' a7' t0' t1',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 (class_id size)) s1 a0 a1 a2' a3 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x38584) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 size) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x384a8) fc None m (seg_rom asegs)).
Proof.
  intros until size. intros SZ M8 RIMG RTLS. pose proof (cb_sm_range size SZ M8) as [CBR CLZ].
  do 29 zstep. setreg 12 (Z_to_bv 64 (cb_sm size)) ltac:(reflexivity).            (* [comment removed for export] *)
  do 14 zstep. setreg 12 (Z_to_bv 64 (cb_clz (cb_sm size))) ltac:(reflexivity).   (* [comment removed for export] *)
  do 12 zstep. setreg 8 (Z_to_bv 64 (cb_fin size)) ltac:(reflexivity).            (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 (class_id size))
    ltac:(symmetry; revert M8; revert SZ; clear; revert size;
          exact cb_fin_class_all).   (* [comment removed for export] *)
  apply evtF_done. do 7 eexists. reflexivity.
Qed.
End CANSEC4.
End TwB.
