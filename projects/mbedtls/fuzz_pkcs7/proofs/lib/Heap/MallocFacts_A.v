(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocRep MallocTree.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Export MallocBlocks MallocHINV.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MallocFacts_A () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Heap.Malloc.c_mmap_counter"; "OSSVerify.KrLib.Heap.Malloc.ctx"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Heap.Malloc.c_secret"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Heap.Malloc.c_init_done"; "OSSVerify.KrLib.Heap.Malloc.c_seq"; "OSSVerify.KrLib.Heap.Malloc.bounces"; "OSSVerify.KrLib.Heap.Malloc.unmap_seq"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.active"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Heap.Malloc.m_sizeclass"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Heap.Malloc.m_mem"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Heap.Malloc.meta"; "OSSVerify.KrLib.Heap.MallocRep.meta_slot"; "OSSVerify.KrLib.Heap.Malloc.m_avail"; "OSSVerify.KrLib.Heap.Malloc.m_freed"; "OSSVerify.KrLib.Heap.Malloc.m_last_idx"; "OSSVerify.KrLib.Heap.Malloc.m_freeable"; "OSSVerify.KrLib.Heap.Malloc.m_maplen"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "OSSVerify.KrLib.Heap.Malloc.mkGhdr"; "Corelib.Init.Datatypes.bool"; "Stdlib.ZArith.BinInt.Z.testbit"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.Heap.Malloc.region"; "Corelib.Init.Datatypes.fst"; "OSSVerify.KrLib.Heap.Malloc.s_regions"; "OSSVerify.KrLib.Heap.Malloc.rkind"; "OSSVerify.KrLib.Heap.Malloc.r_kind"; "OSSVerify.KrLib.Heap.Malloc.RKGroup"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.modulo"; "sstart_of"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Heap.Malloc.round_up_pg"; "OSSVerify.KrLib.Heap.Malloc.r_len"; "OSSVerify.KrLib.Heap.Malloc.UNIT"; "OSSVerify.KrLib.Heap.Malloc.get_stride"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Heap.Malloc.size_class"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Heap.Malloc.IB"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.Heap.MallocBlocks.block"; "Stdlib.Lists.List.In"; "OSSVerify.KrLib.Heap.MallocBlocks.blk_slot"; "OSSVerify.KrLib.Heap.MallocBlocks.blk_addr"; "OSSVerify.KrLib.Heap.MallocBlocks.blk_size"; "OSSVerify.KrLib.Heap.Malloc.r_base"; "Stdlib.ZArith.BinInt.Z.land"; "OSSVerify.KrLib.Heap.Malloc.s_slots"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Heap.MallocTree.ptrs_in"; "Stdlib.NArith.BinNat.N.lt"; "OSSVerify.KrLib.Heap.Malloc.s_next_rid"; "Stdlib.NArith.BinNat.N.le"; "OSSVerify.KrLib.Heap.Malloc.shadow"; "OSSVerify.KrLib.Heap.Malloc.s_shadow"; "OSSVerify.KrLib.Heap.Malloc.cellval"; "OSSVerify.KrLib.Heap.Malloc.cell_read"; "OSSVerify.KrLib.Heap.Malloc.get_shadow"; "OSSVerify.KrLib.Heap.Malloc.Unknown"; "OSSVerify.KrLib.Heap.Malloc.cptr"; "OSSVerify.KrLib.Heap.Malloc.Known"; "OSSVerify.KrLib.Heap.Malloc.r_cells"; "OSSVerify.KrLib.Heap.Malloc.s_tick"].


(* [comment removed for export] *)
Record block_ok (st : mstate) (b : block) : Prop := mkBO {
  (* [comment removed for export] *)
  bo_slot : exists g idx, (s_slots st) !! (blk_slot b) = Some (g, idx)
            /\ Z.testbit (m_avail (get_meta_rec st g)) idx = false
            /\ Z.testbit (m_freed (get_meta_rec st g)) idx = false
            /\ 0 <= idx <= m_last_idx (get_meta_rec st g)
            (* [comment removed for export] *)
            /\ (exists off, 0 <= off /\ blk_addr b = conc st (blk_slot b) + UNIT * off
                           /\ UNIT * off + blk_size b <= get_stride (get_meta_rec st g) - IB);
  (* [comment removed for export] *)
  bo_region : exists r, (s_regions st) !! (fst (blk_slot b)) = Some r /\ r_kind r = RKGroup;
  bo_size : 0 <= blk_size b
}.

(* [comment removed for export] *)

Definition sstart_of (mr : meta) (i : Z) : Z := snd (default (0%N, 0) (m_mem mr)) + UNIT + get_stride mr * i.

Definition fact_ctx (cs : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_A ()) "(0.(0.(1.=(2.(3.O1.)))(4.(2.(3.O1.))(5.+2.+20.)))(0.(0.(1.=(6.(3.O1.)))(4.(6.(3.O1.))(5.+2.+40.)))(0.(7.(8.$9.(:.(3.O1.))=)(8.$9.(:.(3.O1.))+1.))(0.(0.(1.=(;.(3.O1.)))(4.(;.(3.O1.))+100.))(0.Pi,$9.(0.(1.=(<.O1.R1.))(4.(<.O1.R1.)+100.))Pi,$9.(0.(1.=(=.O1.R1.))(4.(=.O1.R1.)+100.)))))))")
(* [comment removed for export] *).

Definition fact_active (cs : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_A ()) "Psc,$9.Pg,$>.P,(8.$?.(10.O1.R2.)(11.$>.R1.))(0.(0.(1.=R3.)(4.R3.+30.))(0.(8.$9.(12.(13.O1.R2.))R3.)(14.(8.$?.(15.(13.O1.R2.))(16.$>.)))))")
(* [comment removed for export] *).

Definition fact_gmeta (cs : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_A ()) "Pg,$>.Pb,$>.P,(8.$?.(15.(13.O1.R2.))(11.$>.R1.))Zmr,$17.(13.O1.R3.)(0.(18.O1.R4.)(0.(0.(1.=(19.R1.))(4.(19.R1.)(5.+2.+20.)))(0.(0.(1.=(1:.R1.))(4.(1:.R1.)(5.+2.+20.)))(0.(0.(1.=(1;.R1.))(1.(1;.R1.)+1?.))(0.(8.$9.(1<.R1.)+1.)(0.(7.(0.(0.(1.=(12.R1.))(4.(12.R1.)+30.))(0.(1.=(1=.R1.))(4.(1=.R1.)(5.+2.+13.))))(0.(8.$9.(12.R1.)+3?.)(0.(8.$9.(1;.R1.)=)(4.=(1=.R1.)))))(0.(1.=(1=.R1.))(0.(1>.$9.Lai,$9.(0.(8.(1?.$20.)(21.$>.$20.(22.$>.(23.$24.$25.$9.$26.)(27.$24.$25.$28.$9.$26.$29.)$20.)(2:.$>.(23.$24.$25.$9.$26.)(27.$24.$25.$28.$9.$26.$29.)$20.)R4.(2;.O1.))(11.$20.(2<.(11.$>.R5.)R1.)))(0.(0.(1.=R1.)(1.R1.(1;.R2.)))Pi,$9.P,(1.=R1.)P,(8.$2=.(2>.(19.R4.)R2.)$2?.)(1.R3.R4.))))(0.(1>.$30.Lr,$30.(0.(8.(1?.$30.)(21.$24.$30.(22.$24.$25.$28.$30.)(2:.$24.$25.$28.$30.)(31.$24.$9.R4.)(32.O1.))(11.$30.R1.))(0.(8.$33.(34.R1.)$35.)(0.(1.=(36.$24.$9.R4.))(0.(8.$9.(37.(36.$24.$9.R4.)+10.)=)(1.(38.R2.(39.(1;.R2.)+1.))(3:.(3;.R1.))))))))(0.(1.$3<.(3=.R1.))(0.(8.$9.(37.(3=.R1.)$3<.)=)(0.P,(4.(12.R1.)+30.)(4.(3=.R2.)(5.+2.+1?.))(0.P,(4.(12.R1.)+30.)Pi,$9.P,(1.=R1.)P,(8.$2=.(2>.(19.R4.)R2.)$2?.)(1.(3>.$3<.(3?.(12.R5.)))(3=.R5.))P,(4.(12.R1.)+30.)(4.(3>.(3=.R2.)(39.(1;.R2.)+1.))(5.+2.+14.)))))))))))))))")
(* [comment removed for export] *).

Definition fact_avail_clear (cs : mstate) (LB : list block) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_A ()) "Pg,$>.Pb,$>.Pi,$9.P,(8.$?.(15.(13.O2.R3.))(11.$>.R2.))P,(1.=R2.)P,(8.$2=.(2>.(19.(13.O2.R5.))R3.)$2?.)Zmr,$17.(13.O2.R6.)Zlo,$9.(40.(38.R1.R5.)$41.)Zhi,$9.(40.(39.(38.R2.R6.)(3=.R2.))$41.)(0.Pb',(42.$24.$9.)Pgh,$20.P,(8.(1?.$20.)(21.(42.$24.$9.)$20.(22.$>.(23.$24.$25.$9.$26.)(27.$24.$25.$28.$9.$26.$29.)$20.)(2:.$>.(23.$24.$25.$9.$26.)(27.$24.$25.$28.$9.$26.$29.)$20.)R2.(2;.O2.))(11.$20.R1.))P,(8.$24.(31.$24.$9.R3.)(31.$24.$9.R;.))(7.(1.(39.(36.$24.$9.R4.)+9.)R6.)(1.R5.(36.$24.$9.R4.)))Pblk,$43.P,(44.$43.R1.O1.)P,(8.$24.(31.$24.$9.(45.R2.))(31.$24.$9.R:.))(1>.$30.Lr,$30.(0.(8.(1?.$30.)(21.$24.$30.(22.$24.$25.$28.$30.)(2:.$24.$25.$28.$30.)(31.$24.$9.R<.)(32.O2.))(11.$30.R1.))(7.(1.(39.(46.R4.)(47.R4.))(39.(48.R1.)R6.))(1.(39.(48.R1.)R5.)(46.R4.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition fact_free_clear (cs : mstate) (LB : list block) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_A ()) "Pg,$>.Pb,$>.Pi,$9.P,(8.$?.(15.(13.O2.R3.))(11.$>.R2.))P,(1.=R2.)P,(7.(8.$2=.(2>.(19.(13.O2.R5.))R3.)$2?.)(8.$2=.(2>.(1:.(13.O2.R5.))R3.)$2?.))Zmr,$17.(13.O2.R6.)Zlo,$9.(40.(38.R1.R5.)$41.)Zhi,$9.(40.(39.(38.R2.R6.)(3=.R2.))$41.)(0.Pb',(42.$24.$9.)Pgh,$20.P,(8.(1?.$20.)(21.(42.$24.$9.)$20.(22.$>.(23.$24.$25.$9.$26.)(27.$24.$25.$28.$9.$26.$29.)$20.)(2:.$>.(23.$24.$25.$9.$26.)(27.$24.$25.$28.$9.$26.$29.)$20.)R2.(2;.O2.))(11.$20.R1.))P,(8.$24.(31.$24.$9.R3.)(31.$24.$9.R;.))(7.(1.(39.(36.$24.$9.R4.)+9.)R6.)(1.R5.(36.$24.$9.R4.)))Pblk,$43.P,(44.$43.R1.O1.)P,(8.$24.(31.$24.$9.(45.R2.))(31.$24.$9.R:.))(1>.$30.Lr,$30.(0.(8.(1?.$30.)(21.$24.$30.(22.$24.$25.$28.$30.)(2:.$24.$25.$28.$30.)(31.$24.$9.R<.)(32.O2.))(11.$30.R1.))(7.(1.(39.(46.R4.)(47.R4.))(39.(48.R1.)R6.))(1.(39.(48.R1.)R5.)(46.R4.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition fact_hdr_clear (cs : mstate) (LB : list block) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_A ()) "Pb,(42.$24.$9.)Pgh,$20.Pblk,$43.Pr,$30.P,(8.(1?.$20.)(21.(42.$24.$9.)$20.(22.$>.(23.$24.$25.$9.$26.)(27.$24.$25.$28.$9.$26.$29.)$20.)(2:.$>.(23.$24.$25.$9.$26.)(27.$24.$25.$28.$9.$26.$29.)$20.)R4.(2;.O2.))(11.$20.R3.))P,(44.$43.R3.O1.)P,(8.$24.(31.$24.$9.(45.R4.))(31.$24.$9.R6.))P,(8.(1?.$30.)(21.$24.$30.(22.$24.$25.$28.$30.)(2:.$24.$25.$28.$30.)(31.$24.$9.R7.)(32.O2.))(11.$30.R4.))(7.(1.(39.(46.R6.)(47.R6.))(39.(48.R5.)(36.$24.$9.R8.)))(1.(39.(39.(48.R5.)(36.$24.$9.R8.))+10.)(46.R6.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition fact_usage (cs : mstate) : Prop := forall i, 0 <= usage cs i < 2^60.

(* [comment removed for export] *)
Definition fact_masks (cs : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_A ()) "Pg,$>.Pb,$>.P,(8.$?.(15.(13.O1.R2.))(11.$>.R1.))Zmr,$17.(13.O1.R3.)(0.Pi,$9.P,(1.=R1.)P,(8.$2=.(2>.(19.R3.)R2.)$2?.)(1.R3.(1;.R4.))(0.Pi,$9.P,(1.=R1.)P,(8.$2=.(2>.(1:.R3.)R2.)$2?.)(1.R3.(1;.R4.))(8.$9.(49.(19.R1.)(1:.R1.))=)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition fact_maplen (cs : mstate) : Prop :=
  forall g b, m_mem (get_meta_rec cs g) = Some b -> m_maplen (get_meta_rec cs g) < 2^40.

(* [comment removed for export] *)
Definition fact_slots (cs : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_A ()) "Pp,(42.$24.$9.)Pg,$>.Pidx,$9.P,(8.(1?.(42.$>.$9.))(21.(42.$24.$9.)(42.$>.$9.)(22.$>.(23.$24.$25.$9.$26.)(27.$24.$25.$28.$9.$26.$29.)(42.$>.$9.))(2:.$>.(23.$24.$25.$9.$26.)(27.$24.$25.$28.$9.$26.$29.)(42.$>.$9.))R3.(4:.O1.))(11.(42.$>.$9.)(4;.$>.$9.R2.R1.)))(1>.$>.Lb,$>.(0.(8.$?.(15.(13.O1.R4.))(11.$>.R1.))(0.(8.$24.(31.$24.$9.R5.)(31.$24.$9.R1.))(0.(8.$9.(36.$24.$9.R5.)(38.(13.O1.R4.)R3.))(0.(1.=R3.)(1.R3.(1;.(13.O1.R4.))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition fact_slots_complete (cs : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_A ()) "Pg,$>.Pb,$>.Pi,$9.P,(8.$?.(15.(13.O1.R3.))(11.$>.R2.))P,(0.(1.=R2.)(1.R2.(1;.(13.O1.R4.))))(8.(1?.(42.$>.$9.))(21.(42.$24.$9.)(42.$>.$9.)(22.$>.(23.$24.$25.$9.$26.)(27.$24.$25.$28.$9.$26.$29.)(42.$>.$9.))(2:.$>.(23.$24.$25.$9.$26.)(27.$24.$25.$28.$9.$26.$29.)(42.$>.$9.))(4;.$24.$9.(31.$24.$9.R4.)(38.(13.O1.R5.)R3.))(4:.O1.))(11.(42.$>.$9.)(4;.$>.$9.R5.R3.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition fact_ptrs (st : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_A ()) "(0.(4<.Lrid,$24.(4=.R1.(4>.O1.))O1.)Prid,$24.P,(4?.(4>.O1.)R1.)(0.(8.(1?.$30.)(21.$24.$30.(22.$24.$25.$28.$30.)(2:.$24.$25.$28.$30.)R2.(32.O1.))(16.$30.))(8.(1?.$50.)(21.$24.$50.(22.$24.$25.$28.$50.)(2:.$24.$25.$28.$50.)R2.(51.O1.))(16.$50.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition fact_blk_unknown (st : mstate) (LB : list block) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_A ()) "Pblk,$43.Pr,$30.P,(44.$43.R2.O1.)P,(8.(1?.$30.)(21.$24.$30.(22.$24.$25.$28.$30.)(2:.$24.$25.$28.$30.)(31.$24.$9.(45.R3.))(32.O2.))(11.$30.R2.))Pa,$9.P,(0.(1.(46.R5.)R1.)(4.R1.(39.(46.R5.)(47.R5.))))(1>.$9.Lh,$9.(8.$52.(53.(54.O2.(31.$24.$9.(45.R7.)))(40.R3.(48.R6.)))(55.R1.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition fact_blocks_disjoint (st : mstate) (LB : list block) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_A ()) "Pb1,$43.Pb2,$43.P,(44.$43.R2.O1.)P,(44.$43.R2.O1.)P,(8.$24.(31.$24.$9.(45.R4.))(31.$24.$9.(45.R3.)))P,(14.(8.$56.(45.R5.)(45.R4.)))(7.(1.(39.(46.R6.)(47.R6.))(46.R5.))(1.(39.(46.R5.)(47.R5.))(46.R6.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition fact_hdr0 (st : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_A ()) "Pg,$>.Pb,$>.Pi,$9.P,(8.$?.(15.(13.O1.R3.))(11.$>.R2.))P,(0.(1.=R2.)(1.R2.(39.(1;.(13.O1.R4.))+1.)))(8.$52.(53.(54.O1.(31.$24.$9.R4.))(40.(38.(13.O1.R5.)R3.)$41.))(57.=))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition fact_cell_ticks (st : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_A ()) "Prid,$24.Psh,$50.Po,$9.Pv,$9.Pt,$24.P,(8.(1?.$50.)(21.$24.$50.(22.$24.$25.$28.$50.)(2:.$24.$25.$28.$50.)R5.(51.O1.))(11.$50.R4.))P,(8.(1?.(42.$9.$24.))(21.$9.(42.$9.$24.)(22.$9.$26.$29.(42.$9.$24.))(2:.$9.$26.$29.(42.$9.$24.))R4.(58.R5.))(11.(42.$9.$24.)(4;.$9.$24.R3.R2.)))(4?.R3.(59.O1.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
Record MFACTS_g {resv : list (Z * Z)} (st : mstate) (LB : list block) : Prop := mkMF {
  mf_blocks : Forall (block_ok st) LB;
  (* [comment removed for export] *)
  mf_nodup : List.NoDup (map blk_slot LB);
  (* [comment removed for export] *)
  mf_ticks : ticks_ok st;
  (* [comment removed for export] *)
  mf_reserved : s_reserved st = resv;
  mf_ctx : fact_ctx (strip st);
  mf_active : fact_active (strip st);
  mf_gmeta : fact_gmeta (strip st);
  mf_avail_clear : fact_avail_clear (strip st) LB;
  mf_hdr0 : fact_hdr0 st;
  (* [comment removed for export] *)
  mf_free_clear : fact_free_clear (strip st) LB;
  mf_hdr_clear : fact_hdr_clear (strip st) LB;
  mf_usage : fact_usage (strip st);
  mf_masks : fact_masks (strip st);
  mf_maplen : fact_maplen (strip st);
  mf_slots : fact_slots (strip st);
  mf_slots_complete : fact_slots_complete (strip st);
  (* [comment removed for export] *)
  mf_ptrs : fact_ptrs st;
  mf_blk_unknown : fact_blk_unknown st LB;
  mf_blocks_disjoint : fact_blocks_disjoint st LB;
  (* [comment removed for export] *)
  mf_cell_ticks : fact_cell_ticks st
}.

(* [comment removed for export] *)
Notation MFACTS := (@MFACTS_g agent_reserved).


(* [comment removed for export] *)
