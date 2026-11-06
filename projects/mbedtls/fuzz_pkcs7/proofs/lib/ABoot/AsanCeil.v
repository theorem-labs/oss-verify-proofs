(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State StackLayout Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PlacementSearch.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanCeil () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "bottomup_floor"; "OSSVerify.KrLib.ABoot.PlacementSearch.no_higher_fit"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "stdpp.bitvector.definitions.bv_unsigned"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_mmap_base"; "Corelib.Init.Datatypes.orb"; "Stdlib.ZArith.BinInt.Z.leb"; "Corelib.Init.Datatypes.negb"; "OSSVerify.KrLib.ABoot.PlacementSearch.higher_fit_b"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "LinuxProcessSemantics.LinuxProcessSem.State.page_size"; "Corelib.Init.Logic.iff"; "Corelib.Init.Datatypes.bool"; "placement_ok_b"; "Corelib.Init.Datatypes.true"; "placement_ok"; "Stdlib.ZArith.BinInt.Z.add"; "LinuxProcessSemantics.LinuxProcessSem.State.alloc_top"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Logic.and"; "alloc_ceiling"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.State.ProcInput"; "LinuxProcessSemantics.LinuxProcessSem.Run.valid_sp"; "init_sp_ok"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.init_model"; "LinuxProcessSemantics.LinuxProcessSem.State.mkVmMapsFull"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_init_sp"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.skipn"; "Corelib.Init.Datatypes.cons"; "Corelib.Lists.ListDef.nth"; "Corelib.Init.Datatypes.nil"].


(* [comment removed for export] *)
Definition alloc_ceiling : Z := 0x7fff7f800000.
Lemma alloc_ceiling_val : alloc_ceiling = 0x7fff7f800000.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition bottomup_floor : Z := 0x2aaaaaaab000.
Lemma bottomup_floor_val : bottomup_floor = 0x2aaaaaaab000.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition placement_ok (h : VmMaps) (aZ nZ : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanCeil ()) "(0.(1.$2.O2.)(3.(4.(5.(6.&40.)(6.&40.))(7.O3.)(8.O3.))O2.O1.(9.&40.(:.O3.))))")
(* [comment removed for export] *).

Definition placement_ok_b (h : VmMaps) (aZ nZ : Z) : bool := ltac2:(CDefT.buildp (gd_tbl_AsanCeil ()) "(;.(<.$2.O2.)(=.(>.(4.(5.(6.&40.)(6.&40.))(7.O3.)(8.O3.))O2.O1.(9.&40.(:.O3.)))))")
(* [comment removed for export] *).

Lemma placement_ok_b_iff : ltac2:(CDefT.buildp (gd_tbl_AsanCeil ()) "Ph,$?.PaZ,$10.PnZ,$10.P,(1.=R2.)P,(11.=R2.)P,(12.$10.(13.R4.$14.)=)P,(12.$10.(13.R4.$14.)=)(15.(12.$16.(17.R7.R6.R5.)$18.)(19.R7.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros h aZ nZ HaPos HnPos HaAl HnAl. unfold placement_ok_b, placement_ok.
  pose proof (bv_unsigned_in_range 64 (vm_mmap_base h)) as [_ Hbase].
  assert (Hb : bv_unsigned (vm_mmap_base h) < two_pow_64) by (unfold two_pow_64; exact Hbase).
  rewrite orb_true_iff, Z.leb_le, negb_true_iff.
  rewrite (no_higher_fit_iff _ _ _ _ HaPos HnPos HaAl HnAl Hb). reflexivity.
Qed.

Lemma placement_ok_b_of_floor : forall h aZ nZ,
  bottomup_floor <= aZ -> placement_ok_b h aZ nZ = true.
Proof. intros h aZ nZ H. unfold placement_ok_b. rewrite (proj2 (Z.leb_le _ _) H). reflexivity. Qed.

Definition hint_placement_ok_b (addr : word) (h : VmMaps) (aZ nZ : Z) : bool :=
  if w_is0 addr then placement_ok_b h aZ nZ else true.

Lemma hint_placement_ok_b_of_floor : forall addr h aZ nZ,
  bottomup_floor <= aZ -> hint_placement_ok_b addr h aZ nZ = true.
Proof. intros addr h aZ nZ H. unfold hint_placement_ok_b. destruct (w_is0 addr); [now apply placement_ok_b_of_floor|reflexivity]. Qed.

Lemma hint_placement_ok_b_nonnull : forall addr h aZ nZ,
  w_is0 addr = false -> hint_placement_ok_b addr h aZ nZ = true.
Proof. intros addr h aZ nZ H. unfold hint_placement_ok_b. now rewrite H. Qed.

(* [comment removed for export] *)
Definition placement_policy : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanCeil ()) "Ph,$?.Pa,(6.&40.)PnZ,$10.P,(11.=R1.)P,(12.$10.(13.R2.$14.)=)P,(12.$10.(13.(9.&40.R4.)$14.)=)P,(11.=(9.&40.R5.))P,(1.(1:.(9.&40.R6.)R5.)(1;.R7.))P,(12.$16.(1<.(4.(5.(6.&40.)(6.&40.))(7.R8.)(8.R8.))R7.(1=.&40.R6.))$18.)(1>.(1.(1:.(9.&40.R8.)R7.)$1?.)(12.$16.(17.R9.(9.&40.R8.)R7.)$18.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition init_sp_ok (h : VmMaps) : Prop := sp_window_lo <= bv_unsigned (vm_init_sp h).

Lemma alloc_ceiling_le_alloc_top : forall h, init_sp_ok h -> alloc_ceiling <= alloc_top h.
Proof. intros h H. unfold init_sp_ok, sp_window_lo in H. unfold alloc_top, alloc_ceiling, stack_max_size. lia. Qed.

Lemma alloc_top_ge_of_ceiling : forall h z, init_sp_ok h -> z <= alloc_ceiling -> z <= alloc_top h.
Proof. intros h z H Hz. pose proof (alloc_ceiling_le_alloc_top h H). lia. Qed.

Lemma init_sp_ok_init_model : ltac2:(CDefT.buildp (gd_tbl_AsanCeil ()) "Preserved,(20.(5.(6.&40.)(6.&40.)))Pbrk0,(6.&40.)Pmbase,(6.&40.)Psp,(6.&40.)Plim,$10.Pinp,$21.P,(22.R3.)(23.(24.(25.R7.R6.R5.R4.R3.R2.)))")
(* [comment removed for export] *).
Proof. intros reserved brk0 mbase sp lim inp (Hlo & _ & _). unfold init_sp_ok. cbn. exact Hlo. Qed.

(* [comment removed for export] *)
Lemma init_sp_ok_same : forall h h', vm_init_sp h' = vm_init_sp h -> init_sp_ok h -> init_sp_ok h'.
Proof. intros h h' E H. unfold init_sp_ok in *. rewrite E. exact H. Qed.

Lemma init_sp_ok_mkVmMapsFull : ltac2:(CDefT.buildp (gd_tbl_AsanCeil ()) "Ph,$?.Pr,(20.(5.(6.&40.)(6.&40.)))Pm,(20.(5.(6.&40.)(6.&40.)))Pna,(20.(5.(6.&40.)(6.&40.)))Psb,(6.&40.)Pb,(6.&40.)Pl,$10.Pmb,(6.&40.)P,(23.R8.)(23.(26.R8.R7.R6.R5.R4.R3.R2.(27.R9.)))")
(* [comment removed for export] *).
Proof. intros. unfold init_sp_ok in *. cbn. assumption. Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_ge_all : forall z, z <= page_round_up_Z z.
Proof.
  intros z. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hr. lia.
Qed.

(* [comment removed for export] *)
Lemma mmap_off_aligned_b_0 : mmap_off_aligned_b (Z_to_bv 64 0) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mmap_anon_b_of_core : forall flags c,
  mmap_flags_core flags = c -> Z.testbit c 5 = true -> mmap_anon_b flags = true.
Proof.
  intros flags c Hc Hb. unfold mmap_anon_b. apply negb_true_iff. apply Z.eqb_neq. intro H0.
  unfold mmap_flags_core in Hc.
  pose proof (Z.land_spec (bv_unsigned flags) MAP_ANONYMOUS 5) as HL. rewrite H0, Z.bits_0 in HL.
  pose proof (Z.ldiff_spec (bv_unsigned flags) MAP_NORESERVE 5) as HD. rewrite Hc, Hb in HD.
  change (Z.testbit MAP_ANONYMOUS 5) with true in HL. change (Z.testbit MAP_NORESERVE 5) with false in HD.
  destruct (Z.testbit (bv_unsigned flags) 5); discriminate.
Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_aligned' : forall z, page_round_up_Z z mod page_size = 0.
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.
Lemma page_round_up_Z_pos' : forall z, 0 < z -> 0 < page_round_up_Z z.
Proof. intros z Hz. pose proof (page_round_up_Z_ge z). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zero_random_draw (rdraw : bv 128) : Prop := rdraw = Z_to_bv 128 0.

Lemma at_random_bytes_zero : at_random_bytes (Z_to_bv 128 0) = repeat (Z_to_bv 8 0) 16.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma firstn1_skipn_nth : ltac2:(CDefT.buildp (gd_tbl_AsanCeil ()) "Pl,(20.(6.&8.))Pi,$28.Pd,(6.&8.)P,(29.R2.(2:.(6.&8.)R3.))(12.(20.(6.&8.))(2;.(6.&8.)#1.(2<.(6.&8.)R3.R4.))(2=.(6.&8.)(2>.(6.&8.)R3.R4.R2.)(2?.(6.&8.))))")
(* [comment removed for export] *).
Proof.
  induction l as [|x l IH]; intros i d Hi; cbn in Hi; [lia|].
  destruct i as [|i]; cbn; [reflexivity|]. apply IH. lia.
Qed.
