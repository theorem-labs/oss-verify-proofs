(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AllocSim MmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehc7Segment46Stdlib6ZArith6BinInt1Zlb2le37Corelib4Init9Datatypesn84Nonen86option37Corelib4Init5Logicq02eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsr9cfind_segment79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~vf5asegs04Nposn84booln85false79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hl77ro_addr35stdpp9bitvectorbdefinitionshpc2bvhpcbbv_unsignedn84Someq03and69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7MmapSim~~~~~~htb5zfilllb3addlb2lthpc7Z_to_bvn84prodn84consn83niln84pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ikf5munchikf5wmonohl77mem_invikf3stkhtb6unfilln84truer98is_ecall79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7SecLazy~~~~~~isb6ECALLW3h5LinuxProcessSemantics5Riscv7Preludejh25bvmapq01Ir9dmachine_statejh29bvmap_set69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9LazyNodes~~~~~~jm26sysret79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~jq82MSjq85MSsvchpc2BVhpc4BvWfhpc6bv_addn84listn84andb69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~kha7hiddenbkhaazin_rangeb3h5LinuxProcessSemanticsfLinuxProcessSem3Runkn25mkCfgkha8restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~kr34lzok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~kv47seg_rom3h5LinuxProcessSemanticsfLinuxProcessSem5Statelje5Modellje8m_vmmapslje9page_sizelje8vm_limitisb4owinkhaaeager_usedkhaain_rangesbkhabpages_totallb3mulr9afetch_wordq03not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~lu62wzlb3pow69OSSVerify6Proofsaboost_jsonafuzz_parse3libaLazyLedger~~~~~~mid9nooverlapljebregion_freeljecmap_containsmideentries_nowrapmidcentry_nowraplje9alloc_toplje4m_fdlje6m_fsyslje4m_iolje5m_limlje6m_proclje6m_timelje7FdStatelje7FsStatelje7IoStatelje8LimStatelje9ProcStatelje9TimeStateisbanonvm_samekhah5same_but_materializedmidbgrant_modelmidccommit_modelhtbcmunmap_modeln83appq02orr95wview" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma asegs_find_segment_none_high : ltac2:(zQ "80!h9!l1!n3!p0!p7!r4!v0!hja>1a$0>1n$0>0@2$2+1^1>0@2$2+nhjgg0^3@3$5@1$4$1@3$6$7^4^3@1$3$1").
Proof.
  intros a n Hn Ha. unfold asegs, RefMemImage.Ref.loaded_segments. cbn -[Z.leb Z.add Z.of_N].
  cbn [Z.of_N seg_base seg_size RefMemImage.RefMemImage_segment_000 RefMemImage.RefMemImage_segment_001 RefMemImage.RefMemImage_segment_002 RefMemImage.RefMemImage_segment_003
       AsanUbsan.AsanUbsan_segment_000 AsanUbsan.AsanUbsan_segment_001
       AsanUbsan.AsanUbsan_segment_002 AsanUbsan.AsanUbsan_segment_003].
  destruct (Z.leb_spec 65536 a); destruct (Z.leb_spec (a + n) (65536 + 356352)); cbn [andb]; try (exfalso; lia).
  destruct (Z.leb_spec 421888 a); destruct (Z.leb_spec (a + n) (421888 + 1323008)); cbn [andb]; try (exfalso; lia).
  destruct (Z.leb_spec 1744896 a); destruct (Z.leb_spec (a + n) (1744896 + 40960)); cbn [andb]; try (exfalso; lia).
  destruct (Z.leb_spec 1785856 a); destruct (Z.leb_spec (a + n) (1785856 + 5632000)); cbn [andb]; try (exfalso; lia).
  reflexivity.
Qed.

Lemma asegs_ro_addr_false_high : ltac2:(zQ "90!hk2!hk8!hkf!r4!hja!hp1!n3!hr9!hrf>1x@1$7@1$0#k0>0@2$6+nhjgg0@2$8@1$0#k0^1@3$3$1@2$5$4^2$2").
Proof. intros x Hx. unfold ro_addr. rewrite asegs_find_segment_none_high by lia. reflexivity. Qed.

(* [comment removed for export] *)
Section Zfill.
  Variables (a n : word) (m : word -> option byte).
  Hypothesis NW : ltac2:(zQ "50!hk2!hrf!ihe!n3!mi7@2$3@2$2@2$1@1$0#k0?1a@2$1@1$0#k0?1n@2$4+2+k0").
  Hypothesis HI : ltac2:(zQ "30!hk2!n3!hrf@2$1+nhjgg0@2$2@1$0#k0?1a").

  Lemma zfill_in : ltac2:(zQ "c0!hk2!hrf!hr9!hse!p7!ht5!r4!ih5!ihe!n3!ii4!ii9>1x@1$2@1$0#k0>0@2$5@2$9@2$1@1$0#k0?1a@2$1@1$0#k0^1@2$a@2$1@1$0#k0^1@2$8@2$1@1$0#k0?1a@2$1@1$0#k0?1n@3$6@1$4@1$2@1$0#8@4$7?1a?1n?1m^2@2$3@1$2@1$0#8@2$b@1$0#8Z").
  Proof.
    intros x Hx. unfold zfill, AllocSim.zmem.
    rewrite (proj2 (Z.leb_le _ _) (proj1 Hx)). rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hx)). reflexivity.
  Qed.

  Lemma zfill_munch : ltac2:(zQ "a0!h9!hk2!hrf!ij4!ijb!ik2!ik8!iob!ih5!ihe@3$7@3$4@2$3$0$0@4$6$0$0@2$2@1$1#k0?1a@2$9@2$2@1$1#k0?1a@2$2@1$1#k0?1n@1$5@2$3$0$0?1m@3$8?1a?1n?1m").
  Proof. intros x Hx. cbn [outside fst snd] in Hx. apply zfill_out. lia. Qed.

  Lemma zfill_wmono : ltac2:(zQ "30!hja!ip4!ih5@3$1$0?1m@3$2?1a?1n?1m").
  Proof.
    intros x Hx. unfold wview in *. unfold zfill, AllocSim.zmem in *.
    destruct (Z.leb (bv_unsigned a) (bv_unsigned x) && Z.ltb (bv_unsigned x) (bv_unsigned a + bv_unsigned n))%bool; [discriminate| exact Hx].
  Qed.

  Lemma zfill_mem_inv : ltac2:(zQ "30!hja!ipd!ih5>0@2$1$0?1m@2$1$0@3$2?1a?1n?1m").
  Proof.
    intros MI x b Hx. unfold zfill, AllocSim.zmem in Hx.
    destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned a + bv_unsigned n));
      cbn [andb] in Hx; try exact (MI x b Hx).
    apply asegs_ro_addr_false_high. lia.
  Qed.

  Lemma zfill_stk : ltac2:(zQ "60!hk2!hrf!hja!iq8!ih5!ihe@4$3$2@3$4?1a?1n?1m@2$1@1$0#k0?1a@2$5@2$1@1$0#k0?1a@2$1@1$0#k0?1n").
  Proof.
    pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 n).
    split; [lia|]. split; [exact NW|]. intros x Hx.
    assert (E : zfill a n m (wa x) = Some (Z_to_bv 8 0)) by (apply zfill_in; rewrite wa_unsigned by lia; lia).
    split.
    - unfold wview. rewrite E. discriminate.
    - exists (Z_to_bv 8 0). unfold mrd. rewrite E. reflexivity.
  Qed.
End Zfill.

(* [comment removed for export] *)
Section Unfill.
  Variables (a n : word) (m : word -> option byte).

  Lemma unfill_munch : ltac2:(zQ "a0!h9!hk2!hrf!ij4!ijb!ik2!ik8!iob!iqf!ihe@3$7@3$4@2$3$0$0@4$6$0$0@2$2@1$1#k0?1a@2$9@2$2@1$1#k0?1a@2$2@1$1#k0?1n@1$5@2$3$0$0?1m@3$8?1a?1n?1m").
  Proof. intros x Hx. cbn [outside fst snd] in Hx. apply unfill_out. lia. Qed.

  Lemma unfill_mem_inv : ltac2:(zQ "30!hja!ipd!iqf>0@2$1$0?1m@2$1$0@3$2?1a?1n?1m").
  Proof.
    intros MI x b Hx. unfold unfill in Hx.
    destruct (Z.leb (bv_unsigned a) (bv_unsigned x) && Z.ltb (bv_unsigned x) (bv_unsigned a + bv_unsigned n))%bool; [discriminate| exact (MI x b Hx)].
  Qed.
End Unfill.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ECALLW : ltac2:(zQ "20!hk2!hr9@1$1@1$0#i0") := ltac2:(zQ "20!hk2!ii9@2$1@1$0#i0+n3").
Lemma is_ecall_ECALLW : ltac2:(zQ "50!hk8!ir9!r4!is0!jg8@3$2$0@1$3$4$1"). Proof. reflexivity. Qed.

Lemma sysret_MSsvc : ltac2:(zQ "f1!hk2!hr9!p7!jj8!jk1!r4!jk5!jl5!jpe!ju5!jub!jv4!jva!ii9!kg2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1R@2$3@1$0#5@1$1@1$0#k0>1F@2$3@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>2x8@1$1@1$0#k0>2fc@1$1@1$0#i0>2rv@1$2@1$1@1$0#k0>1m~0>2ro~0>1r@1$1@1$0#k0>1M~0@3$5$6@3$8@8$a^a^9^8^7^6^5^4^3^2^1@7$9@5$7@1$0#5@1$1@1$0#k0@3$b@1$0#5+aKv$4@2$c@1$0#5+a^2^a^9@3$e@1$0#k0^8@2$d@1$0#k0+4^6^5^1^3").
Proof. reflexivity. Qed.

Section CjNodes.
  Variables (L S Zr : list (word * word)).
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
            (F : bvmap 5 word) (pc : Z) (fc : bv 32) (rv : option word) (m : word -> option byte).
  Let R := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  Let Ra (a : word) := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.

  (* [comment removed for export] *)
  Lemma sr_ecall_MS : forall msF mo (Q : config -> Prop),
    lzok asegs L S Zr (mkCfg msF mo) ->
    restrict L S msF = MS R F (Z_to_bv 64 pc) fc rv m (seg_rom asegs) ->
    fetch_word asegs (Z_to_bv 64 pc) = Some ECALLW ->
    (forall msF', lzok asegs L S Zr (mkCfg msF' mo) ->
       restrict L S msF' = MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs) ->
       hid_same L S msF msF' -> sreach asegs Q (mkCfg msF' mo)) ->
    sreach asegs Q (mkCfg msF mo).
  Proof.
    intros msF mo Q OK VIS FW K.
    eapply (sreach_ecall_lazy asegs L S Zr _ msF mo ECALLW Q OK VIS eq_refl FW is_ecall_ECALLW).
    intros msF' OK' VIS' HS'. apply (K msF' OK'); [| exact HS']. rewrite VIS'. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sr_mmap_kernel_MS : forall (na nr : bool) msF mo (Q : config -> Prop),
    lzok asegs L S Zr (mkCfg msF mo) ->
    restrict L S msF = MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs) ->
    x17 = Z_to_bv 64 222 ->
    let nZ := page_round_up_Z (bv_unsigned x11) in
    let n := Z_to_bv 64 nZ in
    let h := m_vmmaps mo in
    x11 <> Z_to_bv 64 0 ->
    x12 = Z_to_bv 64 (kprot na) -> x13 = Z_to_bv 64 (kflags nr) -> x14 = Z_to_bv 64 (-1) -> x15 = Z_to_bv 64 0 ->
    entries_nowrap (vm_maps h) ->
    (na = false -> nr = false -> eager_used mo + pages_total S * page_size + nZ <= vm_limit h) ->
    (exists g : word, bv_unsigned g mod page_size = 0 /\ 0 < bv_unsigned g /\ bv_unsigned g + nZ <= alloc_top h
                      /\ region_free (vm_reserved h ++ vm_maps h) g n = true) ->
    (nr = true -> forall a : word, region_free (vm_reserved h) a n = true -> bv_unsigned a + nZ <= alloc_top h -> lazy_range_okb asegs (a, n) = true) ->
    (forall (a : word) (msF' : machine_state),
       bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a -> bv_unsigned a + nZ <= alloc_top h ->
       region_free (vm_reserved h ++ vm_maps h) a n = true ->
       let mo' := grant_model (Z_to_bv 64 (kflags nr)) a n na mo in
       lzok asegs ((if nr then [(a, n)] else []) ++ L) S ((if nr && negb na then [(a, n)] else []) ++ Zr) (mkCfg msF' mo') ->
       restrict ((if nr then [(a, n)] else []) ++ L) S msF'
         = MS (Ra a) F (Z_to_bv 64 (pc + 4)) fc rv (if na || nr then unfill a n m else zfill a n m) (seg_rom asegs) ->
       hid_same L S msF msF' ->
       eager_used mo' <= eager_used mo + (if na || nr then 0 else nZ) ->
       sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF mo).
  Proof.
    intros na nr msF mo Q OK VIS H17. cbv zeta. intros LEN H12 H13 H14 H15 NW BUD GAP ROK K.
    eapply (sreach_mmap_kernel_lazy asegs na nr L S Zr msF _ mo x17 Q OK VIS eq_refl); [ rewrite H17; reflexivity | ..];
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 1) with x11;
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 2) with x12;
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 3) with x13;
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 4) with x14;
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 5) with x15;
      [ exact LEN | exact H12 | exact H13 | exact H14 | exact H15 | exact NW | exact BUD | exact GAP | exact ROK | ].
    intros a msF'.
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 1) with x11.
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 0) with x10.
    change (ms_mem (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs))) with m.
    cbv zeta. intros AL POS CE FREE OK' VIS' HS' EAG.
    apply (K a msF' AL POS CE FREE OK'); [| exact HS' | exact EAG].
    rewrite VIS', sysret_MSsvc. unfold R. rewrite mkR_set_a0, lit_add_lit. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sr_mmap_commit_MS : forall (nr : bool) msF mo (Q : config -> Prop),
    lzok asegs L S Zr (mkCfg msF mo) ->
    restrict L S msF = MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs) ->
    x17 = Z_to_bv 64 222 ->
    let addr := x10 in
    let nZ := page_round_up_Z (bv_unsigned x11) in
    let n := Z_to_bv 64 nZ in
    let h := m_vmmaps mo in
    x11 <> Z_to_bv 64 0 ->
    x12 = Z_to_bv 64 3 -> x13 = Z_to_bv 64 (fflags nr) -> x14 = Z_to_bv 64 (-1) -> x15 = Z_to_bv 64 0 ->
    bv_unsigned addr + nZ <= alloc_top h -> bv_unsigned addr mod page_size = 0 -> 0 < bv_unsigned addr ->
    region_free (vm_reserved h) addr n = true -> map_contains (vm_maps h) addr n = true ->
    entries_nowrap (vm_maps h) -> entries_nowrap (vm_noaccess h) -> nooverlap (vm_maps h) ->
    (nr = false -> forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + nZ -> in_rangesb x Zr = false) ->
    (nr = true -> forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + nZ -> in_rangesb x Zr = true) ->
    (nr = true -> lazy_range_okb asegs (addr, n) = true) ->
    (nr = false -> eager_used mo + pages_total S * page_size + nZ <= vm_limit h) ->
    (forall msF' : machine_state,
       let mo' := commit_model (Z_to_bv 64 (fflags nr)) addr n false mo in
       let L' := (if nr then [(addr, n)] else []) ++ maps_subtract L (bv_unsigned addr) (bv_unsigned addr + nZ) in
       lzok asegs L' S Zr (mkCfg msF' mo') ->
       restrict L' S msF'
         = MS (Ra addr) F (Z_to_bv 64 (pc + 4)) fc rv
              (if nr then (fun x => if zin_rangeb (bv_unsigned x) (addr, n) && in_rangesb x S then Some (Z_to_bv 8 0) else m x)
               else zfill addr n m) (seg_rom asegs) ->
       hid_same L' S msF msF' ->
       eager_used mo' <= eager_used mo + (if nr then 0 else nZ) ->
       sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF mo).
  Proof.
    intros nr msF mo Q OK VIS H17. cbv zeta. intros LEN H12 H13 H14 H15 CE AL POS RF MC NW NWA NOV ZF ZT ROK BUD K.
    eapply (sreach_mmap_fixed_commit_lazy asegs nr L S Zr msF _ mo x17 Q OK VIS eq_refl); [ rewrite H17; reflexivity | ..];
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 0) with x10;
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 1) with x11;
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 2) with x12;
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 3) with x13;
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 4) with x14;
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 5) with x15;
      [ exact LEN | exact H12 | exact H13 | exact H14 | exact H15 | exact CE | exact AL | exact POS
      | exact RF | exact MC | exact NW | exact NWA | exact NOV | exact ZF | exact ZT | exact ROK | exact BUD | ].
    intros msF'.
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 1) with x11.
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 0) with x10.
    change (ms_mem (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs))) with m.
    cbv zeta. intros OK' VIS' HS' EAG. apply (K msF' OK'); [| exact HS' | exact EAG].
    rewrite VIS', sysret_MSsvc. unfold R. rewrite mkR_set_a0, lit_add_lit. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sr_munmap_MS : forall msF mo (Q : config -> Prop),
    lzok asegs L S Zr (mkCfg msF mo) ->
    restrict L S msF = MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs) ->
    x17 = Z_to_bv 64 215 ->
    let a := x10 in
    let nZ := page_round_up_Z (bv_unsigned x11) in
    let n := Z_to_bv 64 nZ in
    let h := m_vmmaps mo in
    bv_unsigned a mod page_size = 0 -> x11 <> Z_to_bv 64 0 -> bv_unsigned a + nZ <= TASK_SIZE ->
    map_has (vm_maps h) a n = true ->
    nooverlap (vm_maps h) -> entries_nowrap (vm_maps h) -> entries_nowrap (vm_noaccess h) ->
    (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ -> in_rangesb x L = false) ->
    (forall msF' : machine_state,
       let mo' := munmap_model a n mo in
       lzok asegs (maps_subtract L (bv_unsigned a) (bv_unsigned a + nZ)) S Zr (mkCfg msF' mo') ->
       restrict (maps_subtract L (bv_unsigned a) (bv_unsigned a + nZ)) S msF'
         = MS (Ra (Z_to_bv 64 0)) F (Z_to_bv 64 (pc + 4)) fc rv (unfill a n m) (seg_rom asegs) ->
       hid_same L S msF msF' ->
       (forall x, hiddenb (maps_subtract L (bv_unsigned a) (bv_unsigned a + nZ)) S x = hiddenb L S x) ->
       eager_used mo' + rem (a, n) (cuts mo) <= eager_used mo ->
       sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF mo).
  Proof.
    intros msF mo Q OK VIS H17. cbv zeta. intros AL LEN NW2 HAS NOV NW NWA RL K.
    eapply (sreach_munmap_lazy asegs L S Zr msF _ mo x17 Q OK VIS eq_refl); [ rewrite H17; reflexivity | ..];
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 0) with x10;
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 1) with x11;
      [ exact AL | exact LEN | exact NW2 | exact HAS | exact NOV | exact NW | exact NWA | exact RL | ].
    intros msF'.
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 1) with x11.
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 0) with x10.
    change (ms_mem (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs))) with m.
    cbv zeta. intros OK' VIS' HS' HID EAG. apply (K msF' OK'); [| exact HS' | exact HID | exact EAG].
    rewrite VIS', sysret_MSsvc. unfold R. rewrite mkR_set_a0, lit_add_lit. reflexivity.
  Qed.
End CjNodes.

(* [comment removed for export] *)
Definition owin : ltac2:(zQ "53!hk2!hr9!ij4!kgc!p7&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$3~0&>0@1$1@1$0#k0@1$4@1$1@1$0#8>1L~1>1S~1>1W~0>1m~2~2") := ltac2:(zQ "c2!hk2!hr9!ij4!hk8!kgc!p7!hse!kh3!kl9!km4!ii9!hrf&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$4~0\1L~1\1S~1\1W~0\1m>0@1$1@1$0#k0@1$5@1$1@1$0#8\1a@1$1@1$0#k0M3\0$3@1$5@1$1@1$0#8@2$7@2$9@2$b@1$0#k0^1^3@3$8^5^4^1@2$6@1$1@1$0#8@2$a@1$0#8Z@1^2^1").

Lemma open_window_MS : ltac2:(zQ "hf3!hk2!hr9!ij4!r4!hja!ijb!kgc!jk5!hk8!p7!ir9!kpe!jj8!kq7!kuc!ju5!lj3!ht5!lmc!ln5!lo1!loe!lpa!lq2!lr0!lre!km4!ihe!n3!lsd!hrf&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$6~0&@3$5~0^d^f>1L~1>1S~1>2Zr~1>1W~0>3msF$7>2mo$h2>1R@2$c@1$0#5@1$1@1$0#k0>1F@2$c@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>2fc@1$1@1$0#i0>2rv@1$9@1$1@1$0#k0>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>0@5$e$4^c^b^a@2$b^8^7>0@3$3$7@3$d^d^c^9@7$f^7^6^5^4^3^2@1$h0$4>0>1a@1$1@1$0#k0>0@3$3$8@2$ha@2$he@1$0#k0^1^c$a@3$3$8@2$h8^2^e$a>0@2$hc@2$hb@1$h7^a@2$hd@1$h9@3$5~0^c^e$h4@1$h5@1$h3^a@2$h1@5$e$4^h0~2^e@2$b^c^b@3$3$7@3$d^h0~2^c@7$f^a^9^8^7^6@4$h6^h0^f^d^5@1$h0$4").
Proof.
  intros L S Zr W msF mo R F pc fc rv m OK VIS HW BUD.
  destruct (lzok_open_window asegs L S Zr W msF mo OK HW BUD) as [OK' E]. split; [exact OK'|]. rewrite E, VIS. reflexivity.
Qed.

(* [comment removed for export] *)

Section Owin.
  Variables (L S : list (word * word)) (lo n : Z).
  Hypothesis LO0 : ltac2:(zQ "10!n3@2$0+nhjgg0?2lo"). Hypothesis HI0 : ltac2:(zQ "30!ihe!n3!mi7@2$1@2$0?2lo?1n@2$2+2+k0"). Hypothesis N0 : ltac2:(zQ "10!ii4@2$0Z?1n").
  Let W : word * word := (Z_to_bv 64 lo, Z_to_bv 64 n).

  Lemma zin_W : forall x : word, zin_rangeb (bv_unsigned x) W = true <-> lo <= bv_unsigned x < lo + n.
  Proof.
    intros x. unfold zin_rangeb, W. cbn [fst snd].
    rewrite (unsigned_lit lo) by lia. rewrite (unsigned_lit n) by lia. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
  Qed.

  Variable (m : word -> option byte).

  Lemma owin_munch : munch [(lo, lo + n)] m (owin L S W m).
  Proof.
    intros x Hx. cbn [outside] in Hx. destruct Hx as [Hx _]. unfold owin.
    destruct (zin_rangeb (bv_unsigned x) W) eqn:E; [|reflexivity]. apply zin_W in E. lia.
  Qed.

  Lemma owin_wmono : wmono asegs m (owin L S W m).
  Proof.
    intros x Hx. unfold owin, wview in *. 
    destruct (zin_rangeb (bv_unsigned x) W && hiddenb L S x); [discriminate| exact Hx].
  Qed.

  Lemma owin_mem_inv : mem_inv asegs m -> mem_inv asegs (owin L S W m).
  Proof.
    intros MI x b Hx. unfold owin in Hx.
    destruct (zin_rangeb (bv_unsigned x) W) eqn:E; cbn [andb] in Hx.
    - apply zin_W in E. apply asegs_ro_addr_false_high. lia.
    - exact (MI x b Hx).
  Qed.

  Hypothesis WL : ltac2:(zQ "b0!hk2!hrf!hk8!ir9!ht5!r4!lr0!ihe!n3!ii4!hr9>1x@1$a@1$0#k0>0@2$4@2$8?2lo@2$1@1$0#k0^1@2$9@2$1@1$0#k0^1@2$7?2lo?1n@3$5$2@2$6^2?1L$3").
  Hypothesis SV : ltac2:(zQ "h00!hk2!hr9!r4!hrf!p0!hk8!p7!ir9!ht5!lu0!nq5!hja!lr0!ihe!n3!ii4>1x@1$1@1$0#k0>0@2$8@2$e?2lo@2$3@1$0#k0^1@2$f@2$3@1$0#k0^1@2$d?2lo?1n>0@3$2$5@2$c^2?1S$7@1$9@3$2@1$6@1$1@1$0#8@3$a$b?1m^3@1$4@1$1@1$0#8").

  Lemma owin_stk : stk asegs (owin L S W m) lo (lo + n).
  Proof.
    split; [lia|]. split; [lia|]. intros a Ha.
    assert (AU : bv_unsigned (wa a) = a) by (apply wa_unsigned; lia).
    assert (ZW : zin_rangeb (bv_unsigned (wa a)) W = true) by (apply zin_W; lia).
    assert (FS : find_segment asegs (bv_unsigned (wa a)) 1 = None) by (apply asegs_find_segment_none_high; lia).
    unfold owin, wview, mrd. rewrite ZW. cbn [andb]. unfold hiddenb. rewrite (WL (wa a)) by lia. cbn [andb].
    destruct (in_rangesb (wa a) S) eqn:ES; cbn [negb].
    - pose proof (SV (wa a) ltac:(lia) ES) as V. unfold wview in V. rewrite FS in V.
      destruct (m (wa a)) as [b|]; [| exfalso; exact (V eq_refl)]. split; [discriminate| exists b; reflexivity].
    - split; [discriminate| eexists; reflexivity].
  Qed.
End Owin.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ecall_a2a50 : ltac2:(zQ "90!hk2!hr9!hse!p7!r4!lt3!hja!jg8!ii9@3$4@1$3@1$1@1$0#i0@2$5$6@2$8@1$0#k0+qiqj8@2$2@1$1@1$0#i0$7").
Proof. vm_compute. reflexivity. Qed.

Lemma wz_ne0 : ltac2:(zQ "a0!hk2!ii4!ht5!r4!lu0!h9!mi1!mi7!ii9!hr9>1z$5>0@2$2@2$1Z^1@2$1^1@2$7+2+k0@1$4@3$3@1$9@1$0#k0@1$6^2@2$8@1$0#k0Z").
Proof. intros z Hz E. apply (f_equal bv_unsigned) in E. unfold wz in E. rewrite !unsigned_lit in E by lia. lia. Qed.

Lemma nooverlap_cons_free : ltac2:(zQ "b1!hk2!hr9!ij4!mma!hk8!ijb!kgc!ik8!ir9!r4!mn7&@2$2@1$1@1$0#k0@1$1@1$0#k0>4maps@1$6~0>1a@1$1@1$0#k0>1n@1$1@1$0#k0>0@3$9$4@3$a^3^2^1$8>0@1$3^4@1$3@3$5~0@4$7@1$1@1$0#k0@1$1@1$0#k0^4^3^5").
Proof.
  intros maps a n RF NO. split; [| exact NO]. intros [b s] IN.
  pose proof (RefNodes.region_free_In maps a n b s RF IN). unfold LazyLedger.hi, LazyLedger.lo. cbn [fst snd]. lia.
Qed.

Lemma map_contains_cons : ltac2:(zQ "91!hk2!hr9!ij4!hk8!ir9!r4!mo6!ijb!kgc&@2$2@1$1@1$0#k0@1$1@1$0#k0>4maps@1$8~0>1e~0>2lo@1$1@1$0#k0>1n@1$1@1$0#k0>0@3$5$3@3$6^4^2^1$4@3$5$3@3$6@3$7~0^4^5^3^2$4").
Proof. intros maps e lo n H. unfold map_contains in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.

Lemma entries_nowrap_cons' : ltac2:(zQ "71!hk2!hr9!ij4!mp6!ijb!kgc!mq8&@2$2@1$1@1$0#k0@1$1@1$0#k0>4maps@1$5~0>1e~0>0@1$6^1>0@1$3^3@1$3@3$4~0^3^4").
Proof. intros maps e He H x [<-|IN]; [exact He| exact (H x IN)]. Qed.

(* [comment removed for export] *)
Definition nonvm_same : ltac2:(zQ "10!lmc>2mo$0>3mo'$0P") := ltac2:(zQ "h20!r4!ht5!lmc!mr8!ms5!msd!mt7!mtf!mu8!mv2!ln5!h9!mvc!ng7!nh2!nhd!ni9!nj6\2mo$2\3mo'$2@2$1@3$0$c@1$4^1@1$4^2@2$1@3$0$e@1$6^1@1$6^2@2$1@3$0$d@1$5^1@1$5^2@2$1@3$0$h0@1$8^1@1$8^2@2$1@3$0$f@1$7^1@1$7^2@2$1@3$0$h1@1$9^1@1$9^2@3$0$b@1$3@1$a^1@1$3@1$a^2").
Lemma nonvm_same_refl : ltac2:(zQ "20!lmc!nk3>2mo$0@2$1^1^1"). Proof. intros; repeat split; reflexivity. Qed.
Lemma nonvm_same_trans : ltac2:(zQ "20!lmc!nk3>1a$0>1b$0>1c$0>0@2$1^3^2>0@2$1^3^2@2$1^5^3").
Proof. intros a b c (?&?&?&?&?&?&?) (?&?&?&?&?&?&?). repeat split; congruence. Qed.
Lemma nonvm_same_mat : ltac2:(zQ "30!lmc!nk3!nl1>2mo$0>3mo'$0>0@2$2^2^1@2$1^3^2").
Proof.
  intros mo mo' SB. pose proof (same_but_materialized_fields _ _ SB) as (?&VM&?&?&?&?&?&?).
  repeat split; try assumption. rewrite VM. reflexivity.
Qed.
Lemma nonvm_same_grant : ltac2:(zQ "60!hk2!hr9!hk8!lmc!nk3!nmb>5flags@1$1@1$0#k0>1a@1$1@1$0#k0>1n@1$1@1$0#k0>2na$2>2mo$3@2$4^1@5$5^5^4^3^2^1").
Proof.
  intros flags a n na mo. unfold nonvm_same. rewrite grant_model_vmmaps.
  destruct mo as [fd [maps lazy mat] io fs proc lm tm]. unfold grant_model, with_mmap_backing, vm_add_lazy.
  destruct (mmap_noreserve_b flags); cbn; repeat split; reflexivity.
Qed.
Lemma nonvm_same_commit : ltac2:(zQ "60!hk2!hr9!hk8!lmc!nk3!nna>5flags@1$1@1$0#k0>1a@1$1@1$0#k0>1n@1$1@1$0#k0>2na$2>2mo$3@2$4^1@5$5^5^4^3^2^1").
Proof.
  intros. npose (commit_model_nonvm flags a n na mo) as (?&?&?&?&?&?). unfold nonvm_same. rewrite commit_model_vmmaps.
  repeat split; try assumption.
Qed.
Lemma nonvm_same_munmap : ltac2:(zQ "50!hk2!hr9!lmc!nk3!noa>1a@1$1@1$0#k0>1n@1$1@1$0#k0>2mo$2@2$3^1@3$4^3^2^1").
Proof.
  intros. rewrite munmap_model_eqL. npose (munmap_modelL_nonvm a n mo) as (?&?&?&?&?&?). unfold nonvm_same.
  rewrite munmap_modelL_vmmaps. repeat split; try assumption.
Qed.
(* [comment removed for export] *)
Lemma nonvm_same_atop : ltac2:(zQ "60!lmc!mr8!ln5!r4!h9!nk3>2mo$0>3mo'$0>0@2$5^2^1@3$3$4@1$1@1$2^2@1$1@1$2^3").
Proof. (intros mo mo' nd_i1; ndestruct nd_i1 as (_&_&_&_&_&_&E)). exact E. Qed.

(* [comment removed for export] *)
Lemma free_vs_mapped : ltac2:(zQ "h32!hk2!hr9!n3!ii4!h9!ihe!ij4!hk8!kgc!ir9!r4!mi1!mi7!hrf!npa!ht5!nq0!mn7!lr0&@2$6@1$1@1$0#k0@1$1@1$0#k0&@1$8~0>3res~1>4maps~1>1a$4>1n$4>1B$4>1K$4>0@3$a$7@3$h1@3$e~0^6^5@1$b^4@1$b^3$9>0@2$3Z^5>0@2$3Z^5>0@2$2@2$5^7^6@2$c+2+k0>0@2$2Z^6>0@2$3^7@2$c+2+k0>0@2$3Z^7>0>1x@1$1@1$0#k0>0@2$f@2$2^a@2$d@1$0#k0^1@2$3@2$d@1$0#k0^1@2$5^a^9@3$a$7@2$h2^2^e$9@2$h0@2$2@2$5^c^b^a@2$2@2$5^a^9^c").
Proof.
  intros res maps a n B K FREE A0 N0 AN HB HB2 HK HM.
  destruct (Z.le_gt_cases (a + n) B) as [|NE1]; [left; lia|]. destruct (Z.le_gt_cases (B + K) a) as [|NE2]; [right; lia|]. exfalso.
  remember (wa (Z.max a B)) as x eqn:EX. assert (XU : bv_unsigned x = Z.max a B) by (subst x; apply wa_unsigned; lia).
  pose proof (region_free_not_in _ _ _ x (region_free_app_r _ _ _ _ FREE)) as X.
  unfold wz in X. rewrite (unsigned_lit a), (unsigned_lit n), XU in X by lia.
  specialize (HM x). rewrite XU in HM. rewrite HM in X by lia. specialize (X ltac:(lia)). discriminate X.
Qed.

(* [comment removed for export] *)
