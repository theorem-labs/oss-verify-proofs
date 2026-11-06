(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_List MI_Ext.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MI_Ext2 () : Init.string Init.list := ["Corelib.Init.Logic.eq"; "stdpp.gmap.gmap"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "Corelib.Numbers.BinNums.Z"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "OSSVerify.KrLib.Heap.Malloc.meta"; "OSSVerify.KrLib.Heap.Malloc.s_metas"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "OSSVerify.KrLib.Heap.Malloc.lhead"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.get_head"; "OSSVerify.KrLib.Heap.MI_Inv.inv_L"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.Heap.Malloc.s_slots"; "OSSVerify.KrLib.Heap.Malloc.region"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_regions"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Heap.Malloc.rkind"; "OSSVerify.KrLib.Heap.Malloc.r_kind"; "OSSVerify.KrLib.Heap.Malloc.RKGroup"; "Corelib.Init.Datatypes.fst"; "OSSVerify.KrLib.Heap.MI_Inv.group_ok"; "OSSVerify.KrLib.Heap.MI_Inv.inv_S"].


Section EXT2.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).

#[using="Type"] Lemma inv_M_ext : s_metas st' = s_metas st -> s_groups st' = s_groups st -> inv_M X st LS -> inv_M X st' LS.
Proof.
  intros HM HG I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [M1 M2 M3 M4 M5]; constructor.
  - intros m Hm. rewrite !ME in *. apply M1. exact Hm.
  - intros m b Hm. rewrite ME in Hm. destruct (M2 m b Hm) as [H|H]; [left; apply HE; exact H| right; exact H].
  - intros b h Hb. rewrite HG in Hb. ddestruct (M3 b h Hb) as (m & H1 & H2 & H3). exists m. rewrite !ME. auto.
  - intros m Hm. rewrite HM. apply M4. exact Hm.
  - intros z Hz. ddestruct (M5 z Hz) as (H1 & H2 & H3 & b & H4 & H5). rewrite !ME, HG. repeat split; auto. exists b. auto.
Qed.

#[using="Type"] Lemma inv_L_ext : ltac2:(CDefT.buildp (gd_tbl_MI_Ext2 ()) "P,(0.(1.$2.(3.$4.$5.$6.$7.)(8.$4.$5.$9.$6.$7.$:.)$;.)(<.Vst',)(<.Vst,))P,(0.(1.$2.(3.$4.$5.$6.$7.)(8.$4.$5.$9.$6.$7.$:.)$=.)(>.Vst',)(>.Vst,))P,Ph,$?.(0.$10.(11.Vst',R1.)(11.Vst,R1.))P,(12.Vst,VLS,)(12.Vst',VLS,)")
(* [comment removed for export] *).
Proof.
  intros HM HG HE I. pose proof (MR_ext st st' HM) as ME.
  destruct I as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
  - intros h. rewrite HE. apply L1.
  - intros h. apply (dll_ext_metas st st' HM). apply L2.
  - exact L3.
  - exact L4.
  - intros m. rewrite !ME. apply L5.
  - intros m Hm. rewrite !ME. apply L6. exact Hm.
  - intros sc m Hm. ddestruct (L7 sc m Hm) as (H1 & H2 & H3). rewrite (live_group_ext st st' HG), ME. auto.
  - exact L9.
Qed.

#[using="Type"] Lemma group_ok_ext m b ai : ltac2:(CDefT.buildp (gd_tbl_MI_Ext2 ()) "P,(0.(1.$2.(3.$4.$5.$6.$7.)(8.$4.$5.$9.$6.$7.$:.)$;.)(<.Vst',)(<.Vst,))P,(0.(1.$2.(3.$4.$5.$6.$7.)(8.$4.$5.$9.$6.$7.$:.)(13.$2.$6.))(14.Vst',)(14.Vst,))P,Prid,$4.Pr,$15.P,(0.(16.$15.)(17.$4.$15.(1.$4.$5.$9.$15.)(18.$4.$5.$9.$15.)R2.(19.Vst,))(1:.$15.R1.))P,(0.$1;.(1<.R2.)$1=.)P,(0.$4.(1>.$4.$6.O2.)R4.)(0.(16.$15.)(17.$4.$15.(1.$4.$5.$9.$15.)(18.$4.$5.$9.$15.)R5.(19.Vst',))(1:.$15.R4.))P,(1?.VX,Vst,VLS,O3.O2.O1.)(1?.VX,Vst',VLS,O3.O2.O1.)")
(* [comment removed for export] *).
Proof.
  intros HM HS HR I. pose proof (MR_ext st st' HM) as ME.
  destruct I as [G1 G2 G3 G4 G5 G6 G7 G8 G9 G9b G10 G11 G12 G13 G14]; constructor; rewrite ?ME, ?HM, ?HS; try assumption.
  - intros Hml. ddestruct (G13 Hml) as (H0 & r & Hr & Hk & E1 & E2). split; [exact H0|]. exists r. split; [| auto]. apply HR; auto.
  - intros H. ddestruct (G14 H) as (p & i & ? & ? & ? & ? & ?). dexists p, i. rewrite !ME. auto 10.
Qed.

#[using="Type"] Lemma inv_S_ext : ltac2:(CDefT.buildp (gd_tbl_MI_Ext2 ()) "P,(0.(1.$2.(3.$4.$5.$6.$7.)(8.$4.$5.$9.$6.$7.$:.)$;.)(<.Vst',)(<.Vst,))P,(0.(1.$2.(3.$4.$5.$6.$7.)(8.$4.$5.$9.$6.$7.$:.)$=.)(>.Vst',)(>.Vst,))P,(0.(1.$2.(3.$4.$5.$6.$7.)(8.$4.$5.$9.$6.$7.$:.)(13.$2.$6.))(14.Vst',)(14.Vst,))P,(20.VX,Vst,VBL,)(20.VX,Vst',VBL,)")
(* [comment removed for export] *).
Proof.
  intros HM HG HS I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [S1 S2 S3 S4 S5 S6]; constructor.
  - intros s m i H. rewrite HS in H. ddestruct (S1 s m i H) as (? & ? & ?). rewrite (live_group_ext st st' HG), !ME. auto.
  - intros b m i Hb Hi. rewrite HS, ME. apply (S2 b); [apply HE; exact Hb| rewrite <- ME; exact Hi].
  - intros b m ai i Hb Hi. rewrite HG in Hb. rewrite !ME, HG. apply (S3 b m ai i); [exact Hb| rewrite <- ME; exact Hi].
  - intros c Hc. rewrite HS. apply S4. exact Hc.
  - exact S5.
  - intros k Hk. ddestruct (S6 k Hk) as (m & i & ? & ?). dexists m, i. rewrite HS, ME. auto.
Qed.
End EXT2.
