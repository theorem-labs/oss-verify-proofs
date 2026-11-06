(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocRep MallocTree MallocBlocks.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MallocFacts_B () : Init.string Init.list := ["OSSVerify.KrLib.Heap.Malloc.aptr"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.m_next"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.iff"; "is_gm"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Heap.Malloc.m_sizeclass"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Heap.Malloc.cellval"; "OSSVerify.KrLib.Heap.Malloc.cell_read"; "OSSVerify.KrLib.Heap.Malloc.get_shadow"; "Corelib.Init.Datatypes.fst"; "Corelib.Numbers.BinNums.N"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.snd"; "OSSVerify.KrLib.Heap.Malloc.Known"; "Stdlib.ZArith.BinInt.Z.land"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.N.eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "OSSVerify.KrLib.Heap.Malloc.g_meta"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Heap.Malloc.g_active_idx"; "OSSVerify.KrLib.Heap.Malloc.m_last_idx"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.Heap.Malloc.s_slots"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Heap.Malloc.slot_start'"; "hosts"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Heap.Malloc.Unknown"; "sstart_of"; "OSSVerify.KrLib.Heap.Malloc.IB"; "OSSVerify.KrLib.Heap.Malloc.c_seq"; "OSSVerify.KrLib.Heap.Malloc.ctx"; "OSSVerify.KrLib.Heap.Malloc.bounces"; "OSSVerify.KrLib.Heap.Malloc.unmap_seq"; "OSSVerify.KrLib.Heap.Malloc.usage"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Heap.Malloc.c_secret"; "OSSVerify.KrLib.Heap.Malloc.brkstate"; "OSSVerify.KrLib.Heap.Malloc.c_brk"; "OSSVerify.KrLib.Heap.Malloc.BrkLive"; "OSSVerify.KrLib.Heap.Malloc.region"; "OSSVerify.KrLib.Heap.Malloc.s_regions"; "OSSVerify.KrLib.Heap.Malloc.rkind"; "OSSVerify.KrLib.Heap.Malloc.r_kind"; "OSSVerify.KrLib.Heap.Malloc.RKBrk"; "ng_ptr"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta"; "OSSVerify.KrLib.Heap.Malloc.c_meta_area_head"; "OSSVerify.KrLib.Heap.Malloc.c_meta_area_tail"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta_areas"; "OSSVerify.KrLib.Heap.Malloc.area"; "OSSVerify.KrLib.Heap.Malloc.s_areas"; "OSSVerify.KrLib.Heap.Malloc.a_next"].


(* [comment removed for export] *)
Definition sstart_of (mr : meta) (i : Z) : Z := snd (default (0%N, 0) (m_mem mr)) + UNIT + get_stride mr * i.

(* [comment removed for export] *)
(* [comment removed for export] *)

Notation rec st m := (get_meta_rec st m) (only parsing).

(* [comment removed for export] *)
Definition hosts (st : mstate) (b g : aptr) : Prop := exists ai, (s_groups st) !! b = Some (mkGhdr (Some g) ai).
Definition is_gm (st : mstate) (g : aptr) : Prop := exists b, hosts st b g.

Definition slot_free (mr : meta) (i : Z) : Prop :=
  Z.testbit (m_freed mr) i = true \/ Z.testbit (m_avail mr) i = true.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record ci_links_t (st : mstate) : Prop := mkCL {
  cl_next : forall m nx, m_next (get_meta_rec st m) = Some nx ->
              m_prev (get_meta_rec st nx) = Some m /\ meta_slot st nx;
  cl_prev : forall m pv, m_prev (get_meta_rec st m) = Some pv ->
              m_next (get_meta_rec st pv) = Some m /\ meta_slot st pv;
  cl_none : forall m, m_next (get_meta_rec st m) = None <-> m_prev (get_meta_rec st m) = None;
  (* [comment removed for export] *)
  cl_self : forall m, m_next (get_meta_rec st m) <> None -> meta_slot st m
}.

(* [comment removed for export] *)
Record ci_heads_t (st : mstate) : Prop := mkCH {
  ch_free : forall h, c_free_meta_head (ctx st) = Some h ->
              m_next (get_meta_rec st h) <> None /\ m_mem (get_meta_rec st h) = None;
  ch_active : forall sc a, active st sc = Some a ->
              0 <= sc < 48 /\ m_next (get_meta_rec st a) <> None /\ is_gm st a /\ m_sizeclass (get_meta_rec st a) = sc
}.

(* [comment removed for export] *)
Definition ci_homog (st : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_B ()) "Pm,$0.Pnx,$0.P,(1.$2.(3.(4.O1.R2.))(5.$0.R1.))(6.(7.(8.O1.R3.)(8.O1.R2.))P,(8.O1.R3.)(1.$9.(:.(4.O1.R3.))(:.(4.O1.R4.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition hdr_known (st : mstate) (p b1 : aptr) (i1 : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_B ()) "(;.$9.Lv3,$9.(;.$9.Llo,$9.(;.$9.Lhi,$9.(6.(1.$<.(=.(>.O4.(?.$10.$9.O3.))(11.(12.$10.$9.O3.)+3.))(13.R3.))(6.(1.$9.(14.R3.+1?.)O1.)(6.(1.$<.(=.(>.O4.(?.$10.$9.O3.))(11.(12.$10.$9.O3.)+2.))(13.R2.))(6.(1.$<.(=.(>.O4.(?.$10.$9.O3.))(11.(12.$10.$9.O3.)+1.))(13.R1.))(1.$9.(15.+10.(16.R2.(15.+100.R1.)))(11.(11.(12.$10.$9.O3.)(12.$10.$9.O2.))+10.)))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Record gmeta_ok (st : mstate) (g b : aptr) : Prop := mkGO {
  go_slot : meta_slot st g;
  go_avail : 0 <= m_avail (get_meta_rec st g) < 2^32;
  go_freed : 0 <= m_freed (get_meta_rec st g) < 2^32;
  go_li : 0 <= m_last_idx (get_meta_rec st g) <= 31;
  go_freeable : m_freeable (get_meta_rec st g) = 1;
  go_sc : (0 <= m_sizeclass (get_meta_rec st g) < 48)
          \/ (m_sizeclass (get_meta_rec st g) = 63 /\ m_last_idx (get_meta_rec st g) = 0 /\ 0 < m_maplen (get_meta_rec st g));
  go_maplen : 0 <= m_maplen (get_meta_rec st g) < 2^35;
  (* [comment removed for export] *)
  go_bits : forall i, 0 <= i ->
      (Z.testbit (m_avail (get_meta_rec st g)) i = true -> i <= m_last_idx (get_meta_rec st g))
      /\ (Z.testbit (m_freed (get_meta_rec st g)) i = true -> i <= m_last_idx (get_meta_rec st g));
  go_mem : m_mem (get_meta_rec st g) = Some b;
  go_region : exists r, (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup
      /\ 0 <= snd b /\ snd b mod 16 = 0
      /\ sstart_of (get_meta_rec st g) (m_last_idx (get_meta_rec st g) + 1) <= round_up_pg (r_len r)   (* [comment removed for export] *)
      /\ (m_maplen (get_meta_rec st g) <> 0 -> snd b = 0 /\ m_maplen (get_meta_rec st g) * 4096 = round_up_pg (r_len r));
  go_stride : UNIT <= get_stride (get_meta_rec st g) /\ get_stride (get_meta_rec st g) mod UNIT = 0;
  (* [comment removed for export] *)
  go_nest : m_maplen (get_meta_rec st g) = 0 ->
      exists g1 i1 b1, (s_slots st) !! b = Some (g1, i1) /\ hosts st b1 g1 /\ fst b1 = fst b
        /\ b = slot_start' (get_meta_rec st g1) i1 /\ 0 <= i1 <= m_last_idx (get_meta_rec st g1)
        /\ ~ slot_free (get_meta_rec st g1) i1
        /\ m_sizeclass (get_meta_rec st g) < m_sizeclass (get_meta_rec st g1)
        (* [comment removed for export] *)
        /\ hdr_known st b b1 i1
}.

Definition ci_gmeta (st : mstate) : Prop := forall b g, hosts st b g -> gmeta_ok st g b.

(* [comment removed for export] *)
Definition ci_groups (st : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_B ()) "Pb,$0.Pgh,$17.P,(1.(18.$17.)(19.$0.$17.(1:.$0.(1;.$10.$1<.$9.$1=.)(1>.$10.$1<.$1?.$9.$1=.$20.)$17.)(21.$0.(1;.$10.$1<.$9.$1=.)(1>.$10.$1<.$1?.$9.$1=.$20.)$17.)R2.(22.O1.))(5.$17.R1.))(;.$0.Lg,$0.(6.(1.$2.(23.R3.)(5.$0.R1.))(6.(24.=(25.R3.))(24.(25.R3.)(26.(4.O1.R1.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition ci_group_inj (st : mstate) : Prop :=
  forall b1 b2 g, hosts st b1 g -> hosts st b2 g -> b1 = b2.

(* [comment removed for export] *)
Definition ci_slots (st : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_B ()) "Ps,$0.Pg,$0.Pi,$9.P,(1.(18.(27.$0.$9.))(19.$0.(27.$0.$9.)(1:.$0.(1;.$10.$1<.$9.$1=.)(1>.$10.$1<.$1?.$9.$1=.$20.)(27.$0.$9.))(21.$0.(1;.$10.$1<.$9.$1=.)(1>.$10.$1<.$1?.$9.$1=.$20.)(27.$0.$9.))R3.(28.O1.))(5.(27.$0.$9.)(29.$0.$9.R2.R1.)))(6.(8.O1.R3.)(6.(1.$0.R4.(2:.(4.O1.R3.)R2.))(6.(24.=R2.)(24.R2.(26.(4.O1.R3.))))))")
(* [comment removed for export] *).
Definition ci_slots_total (st : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_B ()) "Pb,$0.Pg,$0.Pi,$9.P,(2;.O1.R3.R2.)P,(6.(24.=R2.)(24.R2.(26.(4.O1.R3.))))(1.(18.(27.$0.$9.))(19.$0.(27.$0.$9.)(1:.$0.(1;.$10.$1<.$9.$1=.)(1>.$10.$1<.$1?.$9.$1=.$20.)(27.$0.$9.))(21.$0.(1;.$10.$1<.$9.$1=.)(1>.$10.$1<.$1?.$9.$1=.$20.)(27.$0.$9.))(2:.(4.O1.R4.)R3.)(28.O1.))(5.(27.$0.$9.)(29.$0.$9.R4.R3.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition ci_ghdr_unk (st : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_B ()) "Pb,(27.$10.$9.)Pgh,$17.Po,$9.P,(1.(18.$17.)(19.(27.$10.$9.)$17.(1:.$0.(1;.$10.$1<.$9.$1=.)(1>.$10.$1<.$1?.$9.$1=.$20.)$17.)(21.$0.(1;.$10.$1<.$9.$1=.)(1>.$10.$1<.$1?.$9.$1=.$20.)$17.)R3.(22.O1.))(5.$17.R2.))P,(6.(24.=R2.)(2<.R2.+<.))(;.$9.Lh,$9.(1.$<.(=.(>.O1.(?.$10.$9.R6.))(16.(12.$10.$9.R6.)R4.))(2=.R1.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition ci_hdr0 (st : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_B ()) "Pg,$0.Pb,$0.Pi,$9.P,(2;.O1.R2.R3.)P,(6.(24.=R2.)(24.R2.(26.(4.O1.R4.))))(1.$<.(=.(>.O1.(?.$10.$9.R4.))(11.(2>.(4.O1.R5.)R3.)$2?.))(13.=))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Record blk_ok (st : mstate) (blk : block) : Prop := mkBK {
  bk_slot : exists g i b, (s_slots st) !! (blk_slot blk) = Some (g, i) /\ hosts st b g /\ fst b = fst (blk_slot blk)
            /\ 0 <= i <= m_last_idx (get_meta_rec st g)
            /\ ~ slot_free (get_meta_rec st g) i
            /\ (exists off, 0 <= off /\ blk_addr blk = conc st (blk_slot blk) + UNIT * off
                           /\ UNIT * off + blk_size blk <= get_stride (get_meta_rec st g) - IB
                           /\ cell_read (get_shadow st (fst (blk_slot blk))) (snd (blk_slot blk) + UNIT * off - IB) = Known 0
                           /\ hdr_known st (aadd (blk_slot blk) (UNIT * off)) b i);
  (* [comment removed for export] *)
  bk_nogroup : (s_groups st) !! (blk_slot blk) = None;
  bk_size : 0 <= blk_size blk
}.

Definition ci_ctx (st : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_B ()) "(6.(6.(24.=(30.(31.O1.)))(2<.(30.(31.O1.))+100.))(6.Pi,$9.(6.(24.=(32.O1.R1.))(2<.(32.O1.R1.)+100.))(6.Pi,$9.(6.(24.=(33.O1.R1.))(2<.(33.O1.R1.)+100.))(6.Psc,$9.(6.(24.=(34.O1.R1.))(2<.(34.O1.R1.)(35.+2.+40.)))(6.(24.=(36.(31.O1.)))(2<.(36.(31.O1.))(35.+2.+40.)))))))")
(* [comment removed for export] *).

Definition ci_brk (st : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_B ()) "Prid,$10.Poff,$9.P,(1.$37.(38.(31.O1.))(39.R2.R1.))(;.$3:.Lr,$3:.(6.(1.(18.$3:.)(19.$10.$3:.(1:.$10.$1<.$1?.$3:.)(21.$10.$1<.$1?.$3:.)R4.(3;.O1.))(5.$3:.R1.))(1.$3<.(3=.R1.)$3>.)))")
(* [comment removed for export] *).


(* [comment removed for export] *)
Definition ci_mem_hosts (st : mstate) : Prop :=
  forall q b, m_mem (get_meta_rec st q) = Some b -> hosts st b q.

(* [comment removed for export] *)
Definition ng_ptr (st : mstate) (p : optr) : Prop :=
  match p with
  | Some q => exists r, (s_regions st) !! (fst q) = Some r /\ r_kind r <> RKGroup
  | None => True
  end.
(* [comment removed for export] *)
Definition ci_mptrs (st : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocFacts_B ()) "(6.(3?.O1.(40.(31.O1.)))(6.(3?.O1.(41.(31.O1.)))(6.(3?.O1.(42.(31.O1.)))(6.(3?.O1.(43.(31.O1.)))Pa,$0.Par,$44.P,(1.(18.$44.)(19.$0.$44.(1:.$0.(1;.$10.$1<.$9.$1=.)(1>.$10.$1<.$1?.$9.$1=.$20.)$44.)(21.$0.(1;.$10.$1<.$9.$1=.)(1>.$10.$1<.$1?.$9.$1=.$20.)$44.)R2.(45.O1.))(5.$44.R1.))(3?.O1.(46.R2.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Record blk_clear (st : mstate) (LB : list block) (blk : block) : Prop := mkBC {
  bc_region : exists r, (s_regions st) !! (fst (blk_slot blk)) = Some r /\ r_kind r = RKGroup
     /\ r_base r + 16 <= blk_addr blk /\ blk_addr blk + blk_size blk <= r_base r + round_up_pg (r_len r)
     /\ blk_addr blk mod 16 = 0
     /\ (forall a, blk_addr blk <= a < blk_addr blk + blk_size blk ->
           exists h, cell_read (get_shadow st (fst (blk_slot blk))) (a - r_base r) = Unknown h);
  bc_hdrs : forall b gh, (s_groups st) !! b = Some gh -> fst b = fst (blk_slot blk) ->
     blk_addr blk + blk_size blk <= conc st b - IB \/ conc st b + 16 <= blk_addr blk;
  bc_blocks : forall blk', In blk' LB -> blk_slot blk' <> blk_slot blk -> fst (blk_slot blk') = fst (blk_slot blk) ->
     blk_addr blk' + blk_size blk' <= blk_addr blk - 4 \/ blk_addr blk + blk_size blk <= blk_addr blk' - 4
}.

Record CINV (st : mstate) (LB : list block) : Prop := mkCI {
  ci_links : ci_links_t st;
  ci_heads : ci_heads_t st;
  ci_hom : ci_homog st;
  ci_gmetas : ci_gmeta st;
  ci_grps : ci_groups st;
  ci_ginj : ci_group_inj st;
  ci_slts : ci_slots st;
  ci_sltt : ci_slots_total st;
  ci_unk : ci_ghdr_unk st;
  ci_h0 : ci_hdr0 st;
  ci_blks : Forall (blk_ok st) LB;
  ci_nodup : List.NoDup (map blk_slot LB);
  ci_cx : ci_ctx st;
  ci_bk : ci_brk st;
  ci_ticks : ticks_ok st;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ci_memh : ci_mem_hosts st;
  ci_mp : ci_mptrs st;
  ci_bclr : Forall (blk_clear st LB) LB
}.

