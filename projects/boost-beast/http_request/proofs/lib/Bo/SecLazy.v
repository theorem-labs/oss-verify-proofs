(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AllocSim MmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma bsegs_find_segment_none_high : forall a n, 1 <= n -> 6832128 <= a -> find_segment bsegs a n = None.
Proof.
  intros a n Hn Ha. unfold bsegs, RefMemImage.Ref.loaded_segments. cbn -[Z.leb Z.add Z.of_N].
  cbn [Z.of_N seg_base seg_size RefMemImage.RefMemImage_segment_000 RefMemImage.RefMemImage_segment_001 RefMemImage.RefMemImage_segment_002 RefMemImage.RefMemImage_segment_003
       AsanUbsan.AsanUbsan_segment_000 AsanUbsan.AsanUbsan_segment_001
       AsanUbsan.AsanUbsan_segment_002 AsanUbsan.AsanUbsan_segment_003].
  destruct (Z.leb_spec 65536 a); destruct (Z.leb_spec (a + n) (65536 + 253952)); cbn [andb]; try (exfalso; lia).
  destruct (Z.leb_spec 319488 a); destruct (Z.leb_spec (a + n) (319488 + 831488)); cbn [andb]; try (exfalso; lia).
  destruct (Z.leb_spec 1150976 a); destruct (Z.leb_spec (a + n) (1150976 + 32768)); cbn [andb]; try (exfalso; lia).
  destruct (Z.leb_spec 1183744 a); destruct (Z.leb_spec (a + n) (1183744 + 5648384)); cbn [andb]; try (exfalso; lia).
  reflexivity.
Qed.

Lemma bsegs_ro_addr_false_high : forall x : word, 6832128 <= bv_unsigned x -> ro_addr bsegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite bsegs_find_segment_none_high by lia. reflexivity. Qed.

(* [comment removed for export] *)
Section Zfill.
  Variables (a n : word) (m : word -> option byte).
  Hypothesis NW : bv_unsigned a + bv_unsigned n <= 2^64.
  Hypothesis HI : 6832128 <= bv_unsigned a.

  Lemma zfill_in : forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> zfill a n m x = Some (Z_to_bv 8 0).
  Proof.
    intros x Hx. unfold zfill, AllocSim.zmem.
    rewrite (proj2 (Z.leb_le _ _) (proj1 Hx)). rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hx)). reflexivity.
  Qed.

  Lemma zfill_munch : munch [(bv_unsigned a, bv_unsigned a + bv_unsigned n)] m (zfill a n m).
  Proof. intros x Hx. cbn [outside fst snd] in Hx. apply zfill_out. lia. Qed.

  Lemma zfill_wmono : wmono bsegs m (zfill a n m).
  Proof.
    intros x Hx. unfold wview in *. unfold zfill, AllocSim.zmem in *.
    destruct (Z.leb (bv_unsigned a) (bv_unsigned x) && Z.ltb (bv_unsigned x) (bv_unsigned a + bv_unsigned n))%bool; [discriminate| exact Hx].
  Qed.

  Lemma zfill_mem_inv : mem_inv bsegs m -> mem_inv bsegs (zfill a n m).
  Proof.
    intros MI x b Hx. unfold zfill, AllocSim.zmem in Hx.
    destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned a + bv_unsigned n));
      cbn [andb] in Hx; try exact (MI x b Hx).
    apply bsegs_ro_addr_false_high. lia.
  Qed.

  Lemma zfill_stk : stk bsegs (zfill a n m) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
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

  Lemma unfill_munch : munch [(bv_unsigned a, bv_unsigned a + bv_unsigned n)] m (unfill a n m).
  Proof. intros x Hx. cbn [outside fst snd] in Hx. apply unfill_out. lia. Qed.

  Lemma unfill_mem_inv : mem_inv bsegs m -> mem_inv bsegs (unfill a n m).
  Proof.
    intros MI x b Hx. unfold unfill in Hx.
    destruct (Z.leb (bv_unsigned a) (bv_unsigned x) && Z.ltb (bv_unsigned x) (bv_unsigned a + bv_unsigned n))%bool; [discriminate| exact (MI x b Hx)].
  Qed.
End Unfill.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ECALLW : bv 32 := Z_to_bv 32 0x73.
Lemma is_ecall_ECALLW : is_ecall ECALLW = true. Proof. reflexivity. Qed.

Lemma sysret_MSsvc : forall R F pc x8 fc rv m ro r M,
  sysret (MSsvc R F pc x8 fc rv m ro) r M = MS (bvmap_set 10 r R) F (pc + Z_to_bv 64 4) fc rv M ro.
Proof. reflexivity. Qed.

Section CjNodes.
  Variables (L S Zr : list (word * word)).
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
            (F : bvmap 5 word) (pc : Z) (fc : bv 32) (rv : option word) (m : word -> option byte).
  Let R := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  Let Ra (a : word) := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.

  (* [comment removed for export] *)
  Lemma sr_ecall_MS : forall msF mo (Q : config -> Prop),
    lzok bsegs L S Zr (mkCfg msF mo) ->
    restrict L S msF = MS R F (Z_to_bv 64 pc) fc rv m (seg_rom bsegs) ->
    fetch_word bsegs (Z_to_bv 64 pc) = Some ECALLW ->
    (forall msF', lzok bsegs L S Zr (mkCfg msF' mo) ->
       restrict L S msF' = MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom bsegs) ->
       hid_same L S msF msF' -> sreach bsegs Q (mkCfg msF' mo)) ->
    sreach bsegs Q (mkCfg msF mo).
  Proof.
    intros msF mo Q OK VIS FW K.
    eapply (sreach_ecall_lazy bsegs L S Zr _ msF mo ECALLW Q OK VIS eq_refl FW is_ecall_ECALLW).
    intros msF' OK' VIS' HS'. apply (K msF' OK'); [| exact HS']. rewrite VIS'. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sr_mmap_kernel_MS : forall (na nr : bool) msF mo (Q : config -> Prop),
    lzok bsegs L S Zr (mkCfg msF mo) ->
    restrict L S msF = MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom bsegs) ->
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
    (nr = true -> forall a : word, region_free (vm_reserved h) a n = true -> bv_unsigned a + nZ <= alloc_top h -> lazy_range_okb bsegs (a, n) = true) ->
    (forall (a : word) (msF' : machine_state),
       bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a -> bv_unsigned a + nZ <= alloc_top h ->
       region_free (vm_reserved h ++ vm_maps h) a n = true ->
       let mo' := grant_model (Z_to_bv 64 (kflags nr)) a n na mo in
       lzok bsegs ((if nr then [(a, n)] else []) ++ L) S ((if nr && negb na then [(a, n)] else []) ++ Zr) (mkCfg msF' mo') ->
       restrict ((if nr then [(a, n)] else []) ++ L) S msF'
         = MS (Ra a) F (Z_to_bv 64 (pc + 4)) fc rv (if na || nr then unfill a n m else zfill a n m) (seg_rom bsegs) ->
       hid_same L S msF msF' ->
       eager_used mo' <= eager_used mo + (if na || nr then 0 else nZ) ->
       sreach bsegs Q (mkCfg msF' mo')) ->
    sreach bsegs Q (mkCfg msF mo).
  Proof.
    intros na nr msF mo Q OK VIS H17. cbv zeta. intros LEN H12 H13 H14 H15 NW BUD GAP ROK K.
    eapply (sreach_mmap_kernel_lazy bsegs na nr L S Zr msF _ mo x17 Q OK VIS eq_refl); [ rewrite H17; reflexivity | ..];
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom bsegs)) 1) with x11;
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom bsegs)) 2) with x12;
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom bsegs)) 3) with x13;
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom bsegs)) 4) with x14;
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom bsegs)) 5) with x15;
      [ exact LEN | exact H12 | exact H13 | exact H14 | exact H15 | exact NW | exact BUD | exact GAP | exact ROK | ].
    intros a msF'.
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom bsegs)) 1) with x11.
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom bsegs)) 0) with x10.
    change (ms_mem (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom bsegs))) with m.
    cbv zeta. intros AL POS CE FREE OK' VIS' HS' EAG.
    apply (K a msF' AL POS CE FREE OK'); [| exact HS' | exact EAG].
    rewrite VIS', sysret_MSsvc. unfold R. rewrite mkR_set_a0, lit_add_lit. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sr_mmap_commit_MS : forall (nr : bool) msF mo (Q : config -> Prop),
    lzok bsegs L S Zr (mkCfg msF mo) ->
    restrict L S msF = MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom bsegs) ->
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
    (nr = true -> lazy_range_okb bsegs (addr, n) = true) ->
    (nr = false -> eager_used mo + pages_total S * page_size + nZ <= vm_limit h) ->
    (forall msF' : machine_state,
       let mo' := commit_model (Z_to_bv 64 (fflags nr)) addr n false mo in
       let L' := (if nr then [(addr, n)] else []) ++ maps_subtract L (bv_unsigned addr) (bv_unsigned addr + nZ) in
       lzok bsegs L' S Zr (mkCfg msF' mo') ->
       restrict L' S msF'
         = MS (Ra addr) F (Z_to_bv 64 (pc + 4)) fc rv
              (if nr then (fun x => if zin_rangeb (bv_unsigned x) (addr, n) && in_rangesb x S then Some (Z_to_bv 8 0) else m x)
               else zfill addr n m) (seg_rom bsegs) ->
       hid_same L' S msF msF' ->
       eager_used mo' <= eager_used mo + (if nr then 0 else nZ) ->
       sreach bsegs Q (mkCfg msF' mo')) ->
    sreach bsegs Q (mkCfg msF mo).
  Proof.
    ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.config); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazySR.lzok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(L); constr:(S); constr:(Zr); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.restrict); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.MSsvc); constr:(R); constr:(F); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(pc); constr:(x17); constr:(fc); constr:(rv); constr:(m); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.PropExec.seg_rom); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Logic.not); constr:(x11); constr:(@Corelib.Numbers.BinNums.Z0); constr:(x12); constr:(x13); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.fflags); constr:(x14); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(x15); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(x10); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.alloc_top); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.region_free); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved); constr:(@Corelib.Init.Datatypes.true); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.map_contains); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_maps); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyLedger.entries_nowrap); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyLedger.nooverlap); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.in_rangesb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.lazy_range_okb); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.eager_used); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.pages_total); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_limit); constr:(@Corelib.Init.Datatypes.app); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nil); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.maps_subtract); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyLedger.commit_model); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.MS); constr:(Ra); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.andb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.zin_rangeb); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.MmapSim.zfill); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazySR.hid_same); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SReach.sreach); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Scfg.hunspell_scfg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.sreach_mmap_fixed_commit_lazy); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Scfg.hunspell_alloc_forced); constr:(@Corelib.Init.Logic.eq_refl); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.sysret); constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap_set); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Init.Logic.I); constr:(@stdpp.bitvector.definitions.bv_add); constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.mkR); constr:(x1); constr:(x2); constr:(x3); constr:(x4); constr:(x5); constr:(x6); constr:(x7); constr:(x8); constr:(x9); constr:(x16); constr:(x18); constr:(x19); constr:(x20); constr:(x21); constr:(x22); constr:(x23); constr:(x24); constr:(x25); constr:(x26); constr:(x27); constr:(x28); constr:(x29); constr:(x30); constr:(x31); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.lit_add_lit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.SysStep.mkR_set_a0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.SecLazy.sysret_MSsvc); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.VmMaps)|] [|@x; @nr; @msF'; @x17; @m; @b; @EAG; @HS'; @VIS'; @OK'; @L'; @mo'; @K; @BUD; @ROK; @ZT; @ZF; @NOV; @NWA; @NW; @MC; @RF; @POS; @AL; @CE; @H15; @H14; @H13; @H12; @LEN; @h; @n; @nZ; @addr; @H17; @VIS; @OK; @Q; @mo; @msF|] "#'-#E$c#H#p#I#O#M#z###<#f$$#V#]#^#t#=#%#$#\#'#P#6#8#9#;#?#N#_#,#/$=#&#e#+#h#>#:#(#4#-#B#Z#[#U#g#j#l#v#7#5#@#J#.#*#a#r#u#y#x#0#{#1#2#~#3$#$&$'$,$0$2$5$6$8$7$:#A$D$J$K$L$M$N$O$P$Q$R$S$T$U$V$W$X$Y$Z$[$\$]$^$_$`$a#)#K#E#`#T#d#k#q$+$*$.$/$1$9$A$E$F$G$H$I$b$c$d$>$?#D$e#R#W#n#m#Y#o#s$)$4#Q#c#i#|$-#S#w$3$B#L#b#}$($;$<#X$%$@$C?$G&$H%$I%$J%$K$$L%$M$$N$$O*$P%$Q$$R$$S$$T&$U&$V%$W($X)$Y($Z$$[$$\'$]'$^'$_$$`%$a%$b&k##SySz,RS#5GS,FS&#1S,FS1'S;'#'#'#'#'#;#$#S<US{G\S|S=M$S$NOS-##E-#USH'-S;'#-#-#-#-#'#6#$0##,S$#$2K#.S2#US}#6/$6##2S>#.S3$9##5S4#US~S;$<##8S?##9S@.(?D(@S2UT##%%#)S.USI#&%#VSJ)SA#P#K2K+)S/USK#$s#+,WSL$D##C#H)SM/#WSN#D'#C#H)SO/#7#)SPUSQ#7#)SR/#USS##CS'L(s#<I&@#2$><$#VSTS#S&#C#Lk##%#k#$s#>#k##+##CSBH#C(Hk##*#k#$s#C#k##&##CS(H8s#Fs#FDBVSUG##C#Hk##&##CS)L*S(UT$FVT%#SA%%#%#s#5)S(USV#&%#k##+#VT&s#Ts#TUT'#UT($WSW%3#nC#$#%%S*#%###$WSXS,s#As#>0($#.S*$s#a#3#Ds#9LS),I#5G'FS&#nC#$#%-J#%#+#,0/#*1#FS#USYD6s#n%S<#$s#k#;s#pUSH#USZ#k##s#j#VS[s#6s#'VSTIFVS\$#$)KVT))#US-InC#$##*&#%#$##j#$s#r#WS]Ds#OS-nC#$#%,J#%#$##+4M1NO#s#x#E6#nC#$#%s#$Q#%#B#s##0s#&#A9#FJR.S5$s$$#3#Ds#XLJ*#*JnC#$#%PS5#%#K#s#e%$#&&#.S+$s$,#3#Ds#`LQ,S%#:GS0J#k##(#k##1#k##5#k##s#-#k#&E#USZs$0UT*s$3=$##Ps#Zs$+j#'s$4#=Ps$-4s$6s$-$#S$SC.J$s$=#3#Ds#qLS6,I#5Gs#8FS&#1BFS#nC#$#%s#1Q#%#s#)#s#(>s$@D##E%#nC#$#%s#IS5#%#s#G#s#H0s#K#s#F9#FQR*=*QnC#$#%PS+#%#K#s$+%$#&&#nC#$#%s#<SD#%#s#4#s#3>s$KD#nC#$#%s#>S^#%#s#6#s#5+s#FMs#CNO#s$N#EI#j#(E#-s$Y;#'$6#WT+%#T,YS_&s$S#DS=$s$Ys#NWT-s$Zs$Y#+%M#NO0s$YVT.*s$Wi#BT/S`SaSbScSdSeSfSgShDS2S>S4S?S@SiS$SjSkSlSmSnSoSpSqSrSsStSuSvSw+IM&NO1s$\#E#1j#)&#+&MINO4s$_#E#4j#)s$^#+s#ZMs#WNO9s$b=E#VT0S<s#[4s$bs#Z&$/#YS_6s$c3D-i#CT1S`SaSbScSdSeSfSgShDS2S>S4S?S@SiS$SjSkSlSmSnSoSpSqSrSsStSuSvSwD40/,%$##E2)m#$#^T2S=Ms$lS$NOS-s$kDB4E5>$B#nC#$#%s#sSD#%#s#q#s#r0s#u#s#p1#FS%4Es#&B&#RYS7S%S1#S#Ij#*s#*#j#+s#0#j#,s#4#j#-s#9#5GIFS&s%%1S#FS1nC#$#%s#iS+#%#s#a#s#`>s$xD##E%#9RFS+S%*S%*S+nC#$#%PS^#%#K#s$a%$#&&#,SxS7:GS0S+#k##%#k##+#k##-#k##2#l#.s#js$1#l#/s#NSE#m#6#j#&E#i#ET3GS0T4S*S,FS&S6s%.S)S$S(SBS's#Xs#TS8SRSPSOSMS/SFS9S.S3SGSxS7S%S1RS##j#0s#\#j#1s$9#j#2s$D#j#3s$J#j#4s$P#j#5s$[#j#6s$_#j#7s$c#j#8s$g#j#9s$l#j#:s$r#j#;s$t#j#<s$w#j#=s%##j#>s%%#j#?s%)#j#@s%-#j#As%1#$s%DI)SG.S/$s%G##s%CS4#(s%IS3%#SGUSIS7&$#(s%MS.VSJ#SA#P#K(s%PS92K#USKS3WSL#SFS.#C#H/S.WSN#S/S9#C#H/S97#USQSF7#/S/USS##CS6L(s%_SC&#s%&%$S82s%(#<%#k###s%%k#$s%`#k##*##CS*H(s%hS'&#s%/%$SC2s%1#<%#k###s%)k#$s%i#k##*##CJH8s%ls%lS'S8VSUG##C#Hk##&##CQL%s$Qs%&%#S'USVS8&$#k##'#3s$QS(S'LQ8s%ws%wS)SBWSWs%&#s%$nC#$#%s%&SD#%###s%%(s&#S)%#S(WSXS,$#0s%+&#USYS*8s&#s&#JS6VS[s%K#VS\#s$snC#$##s$w##%#s$q#s$pj#$s&'#WS]S*S)S-nC#$#%s$yS:#%#$##+*Ms$~NO#s&-#Es#q#9RFS:S%*S:nC#$#%PT5#%#K#J%$#&s#q#:GS0S:s#mk##$#k##)#k##+#k##s#|#l#.7s%?#l#/?SE#k#&E#,S5Q:GS0J#k##%#k##s#%#k##s#,#k##s#2#k##s#<#k##s#F#k##s#I#k##s#L#k##s#O#k##s#S#k##s#W#k##s#Z#k##s#^#k##s&1#k##s&3#k##s#e#k##s&;#k##s&?#l#Bs#kT6#l#Cs#ms&N#l#Ds&5P#l#EDs&P#m#s#q#j#Fs&H#j#Gs&T#j#Hs&a#j#Is&d#j#JSE#j#KE#j#%C##"). Qed.

  (* [comment removed for export] *)
  Lemma sr_munmap_MS : forall msF mo (Q : config -> Prop),
    lzok bsegs L S Zr (mkCfg msF mo) ->
    restrict L S msF = MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom bsegs) ->
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
       lzok bsegs (maps_subtract L (bv_unsigned a) (bv_unsigned a + nZ)) S Zr (mkCfg msF' mo') ->
       restrict (maps_subtract L (bv_unsigned a) (bv_unsigned a + nZ)) S msF'
         = MS (Ra (Z_to_bv 64 0)) F (Z_to_bv 64 (pc + 4)) fc rv (unfill a n m) (seg_rom bsegs) ->
       hid_same L S msF msF' ->
       (forall x, hiddenb (maps_subtract L (bv_unsigned a) (bv_unsigned a + nZ)) S x = hiddenb L S x) ->
       eager_used mo' + rem (a, n) (cuts mo) <= eager_used mo ->
       sreach bsegs Q (mkCfg msF' mo')) ->
    sreach bsegs Q (mkCfg msF mo).
  Proof.
    intros msF mo Q OK VIS H17. cbv zeta. intros AL LEN NW2 HAS NOV NW NWA RL K.
    eapply (sreach_munmap_lazy bsegs L S Zr msF _ mo x17 Q OK VIS eq_refl); [ rewrite H17; reflexivity | ..];
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom bsegs)) 0) with x10;
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom bsegs)) 1) with x11;
      [ exact AL | exact LEN | exact NW2 | exact HAS | exact NOV | exact NW | exact NWA | exact RL | ].
    intros msF'.
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom bsegs)) 1) with x11.
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom bsegs)) 0) with x10.
    change (ms_mem (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom bsegs))) with m.
    cbv zeta. intros OK' VIS' HS' HID EAG. apply (K msF' OK'); [| exact HS' | exact HID | exact EAG].
    rewrite VIS', sysret_MSsvc. unfold R. rewrite mkR_set_a0, lit_add_lit. reflexivity.
  Qed.
End CjNodes.

(* [comment removed for export] *)
Definition owin (L S : list (word * word)) (W : word * word) (m : word -> option byte) : word -> option byte :=
  fun a => if zin_rangeb (bv_unsigned a) W && hiddenb L S a then Some (Z_to_bv 8 0) else m a.

Lemma open_window_MS : forall L S Zr W msF mo R F pc fc rv m,
  lzok bsegs L S Zr (mkCfg msF mo) ->
  restrict L S msF = MS R F pc fc rv m (seg_rom bsegs) ->
  (forall a, zin_rangeb (bv_unsigned a) W = true -> in_rangesb a Zr = true) ->
  eager_used mo + pages_total (W :: S) * page_size <= vm_limit (m_vmmaps mo) ->
  lzok bsegs L (W :: S) Zr (mkCfg msF mo) /\ restrict L (W :: S) msF = MS R F pc fc rv (owin L S W m) (seg_rom bsegs).
Proof.
  intros L S Zr W msF mo R F pc fc rv m OK VIS HW BUD.
  destruct (lzok_open_window bsegs L S Zr W msF mo OK HW BUD) as [OK' E]. split; [exact OK'|]. rewrite E, VIS. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma vis_hidden_none : forall L S msF R F pc fc rv m ro,
  restrict L S msF = MS R F pc fc rv m ro -> forall x, hiddenb L S x = true -> m x = None.
Proof.
  intros L S msF R F pc fc rv m ro VIS x Hx.
  assert (E : ms_mem (restrict L S msF) = m) by (rewrite VIS; reflexivity).
  rewrite <- E. cbn [restrict restrict_by with_mem ms_mem restrict_mem_by]. unfold restrict_mem_by. rewrite Hx. reflexivity.
Qed.

Section Owin.
  Variables (L S : list (word * word)) (lo n : Z).
  Hypothesis LO0 : 6832128 <= lo. Hypothesis HI0 : lo + n <= 2^64. Hypothesis N0 : 0 < n.
  Let W : word * word := (Z_to_bv 64 lo, Z_to_bv 64 n).

  Lemma zin_W : forall x : word, zin_rangeb (bv_unsigned x) W = true <-> lo <= bv_unsigned x < lo + n.
  Proof.
    ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Numbers.BinNums.Z); constr:(lo); constr:(@Corelib.Init.Logic.iff); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(n); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.iff_Transitive); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@Stdlib.Bool.Bool.andb_true_iff); constr:(@Corelib.Classes.Morphisms_Prop.and_iff_morphism); constr:(@Corelib.Classes.Morphisms.reflexive_proper_proxy); constr:(@Corelib.Classes.Morphisms.reflexive_reflexive_proxy); constr:(@Corelib.Classes.RelationClasses.iff_Reflexive); constr:(@Stdlib.ZArith.BinInt.Z.leb_le); constr:(@Corelib.Classes.Morphisms.Reflexive_partial_app_morphism); constr:(@Corelib.Classes.Morphisms.respectful); constr:(@Stdlib.ZArith.BinInt.Z.ltb_lt); constr:(@Corelib.Init.Datatypes.prod_ind); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.and_ind); constr:(W); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.unsigned_lit); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(N0); constr:(HI0); constr:(LO0); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.zin_rangeb)|] [|@z; @lemma; @B; @W; @H1; @H0; @H; @b; @a; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__arith; @__sat2; @__sat1; @x|] "#&.#)$(#1#m#n#2#l###5#=#)#U#3#$#t#%#<#w#&#]#/#B#r#;#F#E#>#O#Q#W#Y#b#^#c#\#s#v$#$$$%#R#0#-#,#C#D#G#H#I#K#J#L#N#'#(#P#M#S#V#X#[#Z#d#e#g#h#f#i#k#u#x#z#{#}#~#|$'$&$($)#.#?#4#@#8#p#o#:#j#9#6#7#`#_#y#A#T#a#q8#q$#r%#s&#t%#u%#;%#-%#v'#w*#x%#y+#z%#{%#|%#}%#~&$#$$$,$%$$&$$'%#S%##########US;#US<#'$N0H#VS(&Q''#,H#.'#/'#%I#J$F*,FQ&,#(%#)'#j#$C#0F0,FH.2#/%#%I#J)#*j#$C#'9H0F#.$0/$#%I#J%I&J%I&J($#)&#.@7/3#%I#J%I5J%I&J($#VS=K;4KMS&'$H<<#j#%+#VS>32$F5)1#(s#$*WS?KMS@XS)KM#,ZS*.s#'H--#4KMS&-&#s#%s#%,j#%(#VSAF=&>s#*)9#k#&KKXSBKKMMXS)KM,s#/_SCK%M$S+S*s#0#6s#.H4KMS&/s#.#s#.s#.5j#%(#VSDs#&s#2VSEs#=s#=)s#2s#2j#'$#'s#AP$F#&$s#8($#'s#ES#$F#&$s#<($#k##'#'s#JSF&#s#@'s#LSG$F#&$s#CXS,$#NHj#('#j#)-#YSH.-,#Hj#*1#XS,--##j#+s#T#j#,s#U#YSIs#Vs#V9#S-V>=#Vs#(s#'#Vs#2s#1#5s#a5s#]VSJ$#&L%$L%VSK'&&L#k##%#k##'#$L+WSL,+Nj##S.#j#-%#$L*k##S.#k#-(#VSML2VS/SN#m##1UN#6S06#1C#1C%1CS02C$#2C&#VS1#S2USOS$WS3S$$#USPS$VSQCPUSRCXSSC$N#USTCUSUC7CLVS4CS%*C$S'#+&GDDE#OUSVDVS4Cs$.WS5C#'7Cs#-WSWC#s$+*C%R#+-GDDE#O3S%####3#3#####3#############################5#3S%##3#########3#############################5#7C#*C#Rs#7+s#>GDDE#O*Cs#>Rs#=+s#@GDDE#O*Cs#?S's#8+s#BGDDE#O[SXs#CGDDE%#-s#DGDDE(s#?#-s#EGDDEs#:s#@#-s#FGDDEs#Bs#A#VSYs#GEVS/IJVSZHP%I#Jm$%#WS[CLNXS\HP$#l#.*)#l#/s#Qs#P#l#0s#Vs#U#j#1C#j#2C#&LH,PN$#s#s$=S#$LS#&S#s#v($#k##&#k##(#k##+#k#1C#k#2C#YHFQS6S7S8l#30$#l#4s#qs#}#l#5s#ys#v#l#4s$(s#~#VS9Q#ZS:CQs$os$-s%$#VS(s%*F's%+#6s#v1C#2Cs#ws#u2C$#VS1#S2WS3S$#s#t*Cs#mS's#h+s#oGDDE#OWS5Cs#ns#j*C#Rs#h+s#rGDDE#O*Cs#9Rs#q+s#tGDDE#O-s#uGDDE#s#ps#4-s#vGDDE&s#q#-s#wGDDE*s#r#l#.#s#3s#-l#/s#{s#z#l#0/s$##j#1C#j#2C#&LN,NP$#s$A$s#GPk###s#*k##%#k##(#k#1C#k#2C#YHQFS6S7S8l#3-$#l#4s$<s$H#l#5s$Ds$A#l#4s$Os$I#VS9F#ZS:CFs%As#)s#'#XS]s%Ps%Ps#)s%MWS^s%Qs%Q#'s%S#0#s%=WS_s%Ts%T&'s%V#,&#.s%A#/'#%I#J(s%1s%()$#m#/#VS`s%GS-%I#J)#'m#&#j#6s%a##"). Qed.

  Variable (m : word -> option byte).

  Lemma owin_munch : munch [(lo, lo + n)] m (owin L S W m).
  Proof.
    intros x Hx. cbn [outside] in Hx. destruct Hx as [Hx _]. unfold owin.
    destruct (zin_rangeb (bv_unsigned x) W) eqn:E; [|reflexivity]. apply zin_W in E. lia.
  Qed.

  Lemma owin_wmono : wmono bsegs m (owin L S W m).
  Proof.
    intros x Hx. unfold owin, wview in *. 
    destruct (zin_rangeb (bv_unsigned x) W && hiddenb L S x); [discriminate| exact Hx].
  Qed.

  Lemma owin_mem_inv : mem_inv bsegs m -> mem_inv bsegs (owin L S W m).
  Proof.
    intros MI x b Hx. unfold owin in Hx.
    destruct (zin_rangeb (bv_unsigned x) W) eqn:E; cbn [andb] in Hx.
    - apply zin_W in E. apply bsegs_ro_addr_false_high. lia.
    - exact (MI x b Hx).
  Qed.

  Hypothesis WL : forall x : word, lo <= bv_unsigned x < lo + n -> in_rangesb x L = true.
  Hypothesis SV : forall x : word, lo <= bv_unsigned x < lo + n -> in_rangesb x S = true -> wview bsegs m x <> None.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Datatypes.bool Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Datatypes.option Sort Prop.

  Lemma owin_stk : stk bsegs (owin L S W m) lo (lo + n).
  Proof.
    ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(lo); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(n); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Logic.not); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.option); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.SecLazy.owin); constr:(L); constr:(S); constr:(W); constr:(m); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.wa); constr:(@Corelib.Init.Datatypes.None); constr:(@Corelib.Init.Logic.ex); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mrd); constr:(@Corelib.Init.Datatypes.Some); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(LO0); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(HI0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.wa_unsigned); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.zin_rangeb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.SecLazy.Owin.zin_W); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.SecLazy.bsegs_find_segment_none_high); constr:(@Stdlib.micromega.Tauto.X); constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.andb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.hiddenb); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_writable); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.segment_byte_at); constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_bytes); constr:(@Stdlib.ZArith.BinInt.Z.to_N); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.of_N); constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_base); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.PropExec.seg_rom); constr:(@Corelib.Init.Datatypes.negb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.in_rangesb); constr:(@kc__2); constr:(SV); constr:(@Corelib.Init.Logic.eq_ind); constr:(@kc__3); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Logic.False_ind); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Corelib.Init.Datatypes.false); constr:(WL); constr:(@kc__3 ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH)))))))|] [|@b; @a; @Ha; @__ff; @__varmap; @__wit; @__x1; @__arith; @__sat2; @__sat1; @__x2; @__x3; @x; @__x4; @H; @__p1; @seg; @ES; @o; @V; @e; @H0; @FS; @ZW; @AU|] "#*@#1$E#?#`#k###a#_#C#$#G#h#%#l#6#7#f#&$-#J#'#Y#:#K#>#I#|#(#*#~#)$A#L#S#o#1#E#D#P#t#{$*#+#,#.#-$B$C$D$E$/#;#H#R#T#W#V#X#Z#\#^#i#m#n#j#q#s#u$&$$$)$($'$,$+$2$3$5$9$8$>#/#0$@$=$F#B#=#8#A#5#c#b$##O#M#@#]#x$0$.$7$6$4$;#9#U#p$:#y#w#v#}$%$<#<#Q#[#e#d#g#z#4#F#N#r$1$?O#w&#x$#y%#z$#{%#|'#}*#~%$#%$$$$%%$&+$'&$(%$)&$*%$+$$,%$-$$.%$/%$0'#A$$1%$2%$3%$4&$5*$6%$7%$8$$9%$:%$;$$<%$=%$>$#&)$?'$@&$A$$B&$C&$D)'OP6PS'$S)A#$$$#$#$#$#A#VSD)#',#'PF-F.%$#US5,US6#UI#XSES*S$S(S1,JJK$#K'#'$#&#,MWS7K)#B,F#,$#j#$.#+/#%)#k##3#k#%C#%8#VSFA;-OB'O=-O=k##$#k##&#'Os#'WSGs#(BJj##S2#j#&%#'Os#$k##S2#k#&(#VSHOs#.7SI#m##0UJ#USJS&USKS&CCJUSLCUSMCDS)$#$#D#D#$#$#D#$#$#$#$#$#$#$#$#$#$#$#$#$#$#A#DS)$#D#$#$#$#$#D#$#$#$#$#$#$#$#$#$#$#$#$#$#$#A#EC#FCS)(C$Q#)s#4HDDG#LKDECO(C#Q')s#8HDDG#L.s#9HDDG'&#VSNs#:G7ENVSOFM#E#Nm$%#WSPCOJXSQFM$#l#'*)#l#(s#Ds#C#l#)s#Gs#F#j#*C#'7F'OJk##$#k#*C#VFPS3l#+($#l#,s#Ps#\#l#-s#Xs#U#l#,s#bs#]#CCMUSRC8C$J#FCs$*LCB#ECs$+US5s$'WSSC$#(C&Q#)s#WHDDG#L.s#XHDDG#s#%#l#'#A;l#(,s#[#l#)s#_s#^#j#*C#j#.C#6FJ'#s$06JM'#s$2k##%#k#*C#k#.C#WFS'PS8l#++$#l#,s#ls#x#l#-s#ts#q#l#,s#~s#y#GS9G#G#;C#;C%;CS9/C$#/C&#<#S+G);C#;C-/C#)/C%#<#S+=S&#s#}=S&*#CCR8Cs#0J#(Cs#.Qs#M)s#~HDDG#LFCs#~LCs#1#(Cs#QS.#)s$&HDDG#L>s$'HDDG'#(C&Qs#1)s$)HDDG#L(Cs#WQs#7)s$+HDDG#L(Cs#XS.s#5)s$-HDDG#L>s$.HDDGs#T#.s$/HDDG&s#X#.s$0HDDG)s#Y#.s$1HDDG,s#Z#l#'#s#Vs#Pl#(5s$4#l#)8s$7#j#*C#j#.C#j#/C#'JF-Fs#7%$#6MR'#s$i's#kR'OR-Rs$l%$#k##&#k##(#k##+#k#*C#k#.C#k#/C#HS'PS,S%S8S3l#+3$#l#,s$Ns$Z#l#-s$Vs$S#l#,s$`s$[#VSTJ#*s#Ws$q#C#JUS6s#Y*s#ZF?#S(#E#N*s#]J'P#-$s%/%$#k##'#'P*-+s%3%$#?*S(#E#Nk##%#%)#*s#iM?#S(#E#Nk##.#j##'#j##$Fj##0#USUFYSV2,&$#j#0;#k#0<.,RUSWS)VSXC#WSYC#s#^/C#s#\<#S+/Cs#as#X<#S+=S&#s$v=S&&#CCS%8C#Ms$(8C#Js#YFCs%N(Cs$)S:#)s$yHDDG#L(Cs$JQ%)s${HDDG#LLCs$Ls#[(C(S.#)s$~HDDG#L>s%#HDDG&#(Cs$PQs$1)s%%HDDG#L(Cs$3S.()s%'HDDG#L>s%(HDDG%#.s%)HDDG(s$R#.s%*HDDG/s$S#l#'#s$Os$Il#(4s%-#l#)8s%0#j#*C#j#.C#j#/C#j#1C##CJR'JS%6JR-S%#%%#'MR6MS%-R#%%#k##'#k##,#k#*C#k#.C#k#/C#k#1C#,S-*s$L#HS-S'#PS,S/l#+5&#l#,s%Js%V#l#-s%Rs%O#l#,s%\s%W#VFs#<#l#2s#?s#>#*s$Ts%i?#S(#E#N*s$Ws#AAS)EC#(C#Q#)s%QHDDG#Ll#'#s$vs$pl#(s$bs%T#l#)s%Xs%W#'))l#+$#F/Cs$Gs$?/Cs#I#<#S+=S&#s%^8Cs$>Ms$j8C#Js$k(Cs%-S:s#D)s%^HDDG#L(Cs$lQs#F)s%`HDDG#LZSZs%aHDDGS,>s%bHDDG$#.s%cHDDGs$:s%0s%1.s%dHDDG$s%1#.s%eHDDG)s%2#l#'#s%.s%(l#(-s%h#l#)0s%k#j#*C#j#.C#j#/C#j#3S4##CFM%s#9S%k##s$4s$4k##$#k##&#k#*C#k#.C#k#/C#k#3S4#-S-s&P[F#S-Ps#7S,S/S3l#+.%#l#,s%~s&.#l#-s&*s&'#l#,s&4s&/#XS[s#1s#0s#(#UIS#1Ks#3s#2KS##%$#,S,MS*S$#0F#VS\s&POBs&P#9'nE#$##s&Q&#%#$##*s%6)1K#s#=US]FUS^F,S/*s%;#US_FUS`#2%#3#4)#nE#$##s&]+#%###s&YnI$S#$#0s&^-#%$#4##s&ZnI$s&`$#0s&_0#%$#$s&V###s&`#s&\&#MS*S$.0J#90nE#$##s&e$#%#8##:K2nI$s&h$#0s&g$#%$#$s&^###s&h#s&_j#$s&j#+s&k#%,#j#$E#@s#$S$5#0F#nE#$##s&p##%#s###BnI$s&r$#0s&q##%$#$s&h#5#s&r#s&n&#@@S$5#0J#nE#$##s&w##%#s#*#5nI$s&y$#0s&x##%$#$s&o#4#s&y#s&pj#$s&{#+s&|#%+#j#$E#,S%@#S$7EF#E6F@s#yS$#E#F5J,S;9#nE#$##s'+%#%#s#:##*s%l%1K#s#s,S<*s%o#2#s#53#4s#;#nE#$##s'3s#=#%###s'/nI$S#$#0s'4)#%$#4##s'0nI$s'6$#0s'5,#%$#$s',###s'6#s'2&#5M9-nE#$##s':$#%#s#I##:K/nI$s'=$#0s'<$#%$#$s'3###s'=#s'4j#$s'?#+s'@#%+#k#5<#j#$E##Es#-N,S=*s&)#HS=S'#PS<S>l#+s$Ns$?#l#,s''s'3#l#-s'/s',#l#,s'9s'4#WSas$B#FJKS1s$C#s'M#s'I&#,S>*s&4#2#s#V3#4s#\#nE#$##s'Ts#^#%###s'PnI$S#$#0s'UF#%$#4##s'QnI$s'W$#0s'V?#%$#$s'M###s'W#s'S&#j#6s#p#Ns#qs#/#Fs#oS%nI$s'\$#0s'[s#3#%$#$s'R#s'W#s'\#s'X&#nI$s'_$#0s'^F#%$#$s'U#s'Z#s'_#s'[&#,Sb*s&F#1K#s$M,Sc*s&I#2#s#k3#4s#q#nE#$##s'is#s#%###s'enI$S#$#0s'j)#%$#4##s'fnI$s'l$#0s'kJ#%$#$s'b###s'l#s'h&#:K,nI$s'p$#0s'oM#%$#$s'f###s'p#s'gj#$s'r#+s's#%(#k#76#j#6s'u##s'vs'ms'r&#Bs'yJ#s'y#s'u&#Bs'|M#s'|#s'sj#$s'~#+s(##nI$s($$#6S4F#%$##S2#S0j#8s($#Ns(%(#S?s'}FVS@S0Fl#9$S0#j#2-#m##-7s(*0XSAs(,,J#I0,%#j#74#j#$s(/#U#Fj#$s(1##s(1s(-s(-&#1Ks#Ls$y2s#0s$93#4s$?#nE#$##s(7s$A#%###s(3nI$S#$#0s(8'#%$#4##s(4#s(9#s(5&#:Ks#8#s(<#s(3j#$s(>#+s(?#%'#7s(@s(<UF#VS@%#j#73#YSds(Es#-6#FU#Jl#6s#ks(F#l#7s#Ks#H#l#7s#[s#X#5N9s%AnE#$##s(K$#%#s$Z##1Ks%Bs%62s$#s$R3#4s$X#nE#$##s(Ps$Z#%###s(LnI$S#$#0s(Q'#%$#4##s(MnI$s(S$#0s(R)#%$#$s(I###s(S#s(O&#nE#$##s(U.#%#s$d#s$-:Ks$/nI$s(X$#0s(W$#%$#$s(N###s(X#s(Oj#$s(Z#+s([#%)#m#6#j#5s#x##Es$HSB#s(_s$ns([&##s(as$ps(Xj#$s(c#+s(d#Ns(ds$ss#BS?s(`Fl#9#S0s#Aj#2)#m##)7s(hs$wXSAs(j)s$y#I,)%#5SBnE#$##s(l##%#s${#s#$nI$s(n$#0s(m##%$#$s(d#>#s(n#s(j&#nE#$##s(p'#%#s%##s$HnI$s(r$#0s(q##%$#$s(h#=#s(r#s(ij#$s(t#+s(u#%(#m#.#j#5;#XSes$8=#JU#Fl#5s$Xs$W#l#$s$ZE#5s$[0N#9s$^nE#$##s)#$#%#s%2##*s'ds$`1K#s%k2s%2s%+3#4s%1#nE#$##s))s%3#%###s)%nI$S#$#0s)*'#%$#4##s)&nI$s),$#0s)+*#%$#$s(~###s),#s)(&#0Ns$znE#$##s)/##%#s%>#s%=:Ks%CnI$s)2$#0s)1$#%$#$s)(###s)2#s))j#$s)4#+s)5#%*#m#9#@s$sS*HS;S's$jPS/S-l#+s&@s&1#l#,s(us)%#l#-s(}s(z#l#,s)+s)&#VSfs$y#ZSCENs${*)#MS*S$s${nE#$##s)@##%#s%O#@nI$s)B$#0s)A##%$#$s)8#9#s)B#s)>&#nE#$##s)Ds%V#%#s%S#s%RnI$s)F$#0s)E##%$#$s)<#7#s)F#s)=j#$s)H#+s)I#%(#m#.#0N.nE#$##s)L##%#s%[#s#,nI$s)N$#0s)M##%$#$s)D#s#%#s)N#s)J&#0Ns%bnE#$##s)Q##%#s%`#s%_nI$s)S$#0s)R##%$#$s)I#s#$#s)S#s)Jj#$s)U#+s)V#%)#m#/#?s#6S(ZSCENs%K$#JJKs)Ys%:#s)[#s)W&#WS7Ks)\s%p#s)^#s)Uj#$s)`#+s)a#%'#m#+#l#:s%{s%w#l#;s&Ss&P#l#<s'Qs'O#j#&s)i#j#%C#Is)ns)Ys(7#Is)zs)Ys(T##"). Qed.
End Owin.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ecall_86dd8 : fetch_word bsegs (Z_to_bv 64 0x086c58) = Some ECALLW.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.option); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.Some); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@stdpp.bitvector.definitions.Z_to_bv_obligation_1); constr:(@Corelib.Init.Logic.eq); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.SecLazy.ECALLW)|] Array.empty "##a###3#+#)#.#,#(#'#0#-#&#4#2#3#5#1#*#/%#1$#2$#C########UD#UG#UH#$C$#####$#$#UE#VI,#WJ-$#VF-#VK-##1UD#$4$###$#$###$#$#$###$#$#######UE##C######$#$###$#$#######$###$#$#######UE#VLs#'#VMN#VFs#7OWPs#7$#m$s#-##"). Qed.

Lemma wz_ne0 : forall z, 0 < z < 2^64 -> wz z <> Z_to_bv 64 0.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.wz); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Logic.f_equal); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Init.Logic.eq_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.unsigned_lit); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.Tauto.X); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.not)|] [|@z; @Ha; @__ff; @__varmap; @__wit; @__x1; @__arith; @__sat1; @__sat0; @__p1; @__p2; @E; @Hz|] "#$U#-#e#0#P#3#Q#O###$#X#&#%#'#-#V#7#5#;#<#>#C#E#I#U#[#^#_#@#?#d#,#4#:#9#=#A#D#G#F#H#J#K#L#N#W#Y#Z#\#`#a#]#*#)#(#b#c#e#+#f#8#2#6#T#S#B#1#R#M-#\&#]%#^$#_'#`*#a%#b%#c*#4%#d+$EH%PUQ#%$%#%#%#%#UQ#VS0)#$H#)-#US1'US2#URIVS#%E#%$#US$'URLZS3(C$#&H+*$++(#C$#VS#-K+.##CH&j#$C#VS4;5$E<(E7$E7k##$#k##&#(EAWS5B<Ij##S%#j#%%#(E>k##S%#k#%(#VS6Es#(VS&S7#m##0UI#US8S'US9S'VS:CIUS;CUS<CVS(CEVS=CP&C$O#'&GDDF#JVS(Cs#5WS>C#s#,&C'O#'*GDDF#J*+GDDF'#US?D&C,S)+'.GDDF#J*/GDDF#',0GDDF'&#VS@1FVS&S*S+VSAHL#S*#S+m$%#WSBCEIXSCHL$#l#&*)#l#';:#l#(>=#j#)C#(EI$Is#D)$#k##s#D#k#)C#VHSDSEl#*)$#l#+s#(s#4#l#,s#0s#-#l#+s#:s#5#VS,K#ZS-Cs#?s#=HK##CKs#C#CSFHj#$C#USGC&Cs#+S)s#+'s#-GDDF#J&Cs#-Os#('s#/GDDF#J*s#0GDDF%#l#&#B<l#')s#3#l#(s#7s#6#(EE)#s#Gl#*%#Hl#+s#<s#H#l#,s#Ds#A#l#+s#Ns#I#VS,E#ZS-Cs#V3HE##CME&Cs#;SHs#<'s#>GDDF#JZS.s#?GDDFK*s#@GDDFs#<#ZS.s#AGDDFM,s#BGDDF$s#8#,s#CGDDF's#9#l#&#s#5s#/l#'s#Gs#F#l#(s#Js#I#j#)C#j#-N#j#.N##CHE$EI)#Lk###Mk##&#k#)C#k#-N#k#.N#$S/s#yYHSI#S/MSJl#*-%#l#+s#Zs#f#l#,s#bs#_#l#+s#ls#g#l#/?>#l#/s#4s#3#l#/s#ws#t#j#/s#{#USKs#|m#$#j#0s$'#j#$C##"). Qed.

Lemma nooverlap_cons_free : forall maps (a n : word),
  region_free maps a n = true -> nooverlap maps -> nooverlap ((a, n) :: maps).
Proof.
  intros maps a n RF NO. split; [| exact NO]. intros [b s] IN.
  pose proof (RefNodes.region_free_In maps a n b s RF IN). unfold LazyLedger.hi, LazyLedger.lo. cbn [fst snd]. lia.
Qed.

Lemma map_contains_cons : forall maps (e : word * word) (lo n : word),
  map_contains maps lo n = true -> map_contains (e :: maps) lo n = true.
Proof. intros maps e lo n H. unfold map_contains in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.

Lemma entries_nowrap_cons' : forall maps (e : word * word), entry_nowrap e -> entries_nowrap maps -> entries_nowrap (e :: maps).
Proof. intros maps e He H x [<-|IN]; [exact He| exact (H x IN)]. Qed.

(* [comment removed for export] *)
Definition nonvm_same (mo mo' : Model) : Prop :=
  m_fd mo' = m_fd mo /\ m_io mo' = m_io mo /\ m_fsys mo' = m_fsys mo /\ m_proc mo' = m_proc mo
  /\ m_lim mo' = m_lim mo /\ m_time mo' = m_time mo
  /\ alloc_top (m_vmmaps mo') = alloc_top (m_vmmaps mo).
Lemma nonvm_same_refl : forall mo, nonvm_same mo mo. Proof. intros; repeat split; reflexivity. Qed.
Lemma nonvm_same_trans : forall a b c, nonvm_same a b -> nonvm_same b c -> nonvm_same a c.
Proof. intros a b c (?&?&?&?&?&?&?) (?&?&?&?&?&?&?). repeat split; congruence. Qed.
Lemma nonvm_same_mat : forall mo mo', same_but_materialized mo mo' -> nonvm_same mo mo'.
Proof.
  intros mo mo' SB. pose proof (same_but_materialized_fields _ _ SB) as (?&VM&?&?&?&?&?&?).
  repeat split; try assumption. rewrite VM. reflexivity.
Qed.
Lemma nonvm_same_grant : forall flags a n na mo, nonvm_same mo (grant_model flags a n na mo).
Proof.
  intros flags a n na mo. unfold nonvm_same. rewrite grant_model_vmmaps.
  destruct mo as [fd [maps lazy mat] io fs proc lm tm]. unfold grant_model, with_mmap_backing, vm_add_lazy.
  destruct (mmap_noreserve_b flags); cbn; repeat split; reflexivity.
Qed.
Lemma nonvm_same_commit : forall flags a n na mo, nonvm_same mo (commit_model flags a n na mo).
Proof.
  intros. pose proof (commit_model_nonvm flags a n na mo) as (?&?&?&?&?&?). unfold nonvm_same. rewrite commit_model_vmmaps.
  repeat split; try assumption.
Qed.
Lemma nonvm_same_munmap : forall a n mo, nonvm_same mo (munmap_model a n mo).
Proof.
  intros. rewrite munmap_model_eqL. pose proof (munmap_modelL_nonvm a n mo) as (?&?&?&?&?&?). unfold nonvm_same.
  rewrite munmap_modelL_vmmaps. repeat split; try assumption.
Qed.
(* [comment removed for export] *)
Lemma nonvm_same_atop : forall mo mo', nonvm_same mo mo' -> alloc_top (m_vmmaps mo') = alloc_top (m_vmmaps mo).
Proof. intros mo mo' (_&_&_&_&_&_&E). exact E. Qed.
Scheme kc__4 := Elimination for Corelib.Init.Logic.or Sort Prop.

(* [comment removed for export] *)
Lemma free_vs_mapped : forall (res maps : list (word * word)) (a n B K : Z),
  region_free (res ++ maps) (wz a) (wz n) = true -> 0 < a -> 0 < n -> a + n <= 2^64 ->
  0 <= B -> B < 2^64 -> 0 < K ->
  (forall x : word, B <= bv_unsigned x < B + K -> in_rangesb x maps = true) ->
  a + n <= B \/ B + K <= a.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.region_free); constr:(@Corelib.Init.Datatypes.app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.wz); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.and); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.in_rangesb); constr:(@Stdlib.ZArith.BinInt.Z.le_gt_cases); constr:(@Corelib.Init.Logic.or); constr:(@kc__4); constr:(@Corelib.Init.Logic.or_introl); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.or_intror); constr:(@Corelib.Init.Logic.False_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.wa); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.wa_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.region_free_not_in); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.region_free_app_r); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Logic.eq_ind); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.unsigned_lit); constr:(@Stdlib.micromega.Tauto.EQ); constr:(@Stdlib.micromega.Tauto.TT); constr:(@Stdlib.micromega.Tauto.isBool); constr:(@Stdlib.micromega.Tauto.FF); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.I)|] [|@x; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__arith; @__sat4; @__sat3; @H; @__x4; @__p1; @__sat5; @z3; @H3; @z; @b; @e; @X; @HM; @XU; @EX; @NE2; @o; @NE1; @HK; @HB2; @HB; @AN; @N0; @A0; @FREE; @K; @B; @n; @a; @maps; @res|] "#*6#E$E#N#p#o#q###'#x#$#i#&#P#8#V#(#%$2#6#9#:#<#=#>#T#7$6#)#4#;$=#v#3#2#E#,#1#5#0#.#M$7#-#/#c#?#C$E#H#Z#+#^$1$:$?$@#*#A$C#B#D$##`#K#J#I#R#Q#Y#b#d#g#f#h#l#n#w#y#z#|#}#{#a#~$.$-$3$8$9$'$&$<$;#@$B$D$A$F#W#U#[#O#X$+#s#r#m$)#_$*#\$%#]$/$5#L$0$>$(#S#j#u#t#e#k$$$,$4A$'%$(%$)%$*&$+%$,&$-'$.*$/+$0&$1%$2%$3%$4%$5%$6%$7*$8$$9$$:)$;%$<$$='$>%$?&$@%$A%$B$$C&$D*4S94#4#4#4#4#USP#USQ#VSR##USA#WSS$PH8L8QWST%$#&M#S)$OH'S,PUSB3USB/VSU$##&##OP$S,%$OS,/4G#S4#'S4SC$%#%%#1JS7&M#S)k##%#k#$;#'S8S;VSD#S4#$S4$S4%-$#'S<S8##S;$S;$-$#'S7S<##S8#-S7-$#j##'#'S5S7##S<#-S5VSVs##B$Os#$#Os#$$Os#$k##$#k##&##Os#)WSWs#*s#)Jj##S=#j#%%##Os#+k##S=#k#%(#VSXOs#0<SY#m##0UJ#USZKUSAK=CQ=CL9C$J#US[CUS\C:CS9:Cs#M;C$#US]S9:C#)C%S0#*)EDDF#IUS^D++EDDF$#$VS_,F<MS)VS`GQ&M#S)m$%#WSaCOJXSbGQ$#l#&*)#l#'65#l#(;:#j#)C#j#*C#j#+C#'GJ##Q'JQ##Lk##%#k#)C#k#*C#k#+C#XGS1S-S6Hl#,,$#l#-s#*s#6#l#.s#2s#/#l#-s#<s#7#WScs#?s#>#j#/s#E#U#Gj##s#K#$S8s#IVSDs#NS5$S5s#O-s#E##s#MS2$S2s#N-$#'S1S2##S5#s#MS1-$#j##'#'S-S1##S2'S2S5##S-XGNS6S#Hl#,s#%=#l#-s#Cs#O#l#.s#Ks#H#l#-s#Us#P#WSd*(#j#//#U#Gj##6#$S1s#]-/-0S-S2>#<s$-G0S6S1>#&s$0G#0S#S->#0S*S6&Cs$##j#$s$5#7S#S-$S#S-&C)S-%$##S-S#&C,S#%$#-&#USeS9VSfC#5SE5#5#5#5#2C#?C)#2C)2CSE(C$#(C&#.#R2C,2C.(C#((C%#(C-#.#R2C1(C)-(C$#(C2#.#R552C#(C#1.#R,K#s#{,K(#,K.#,K5#=CHUSgC9C$Q#9C#Js$#:Cs$i)Cs#|S+#*s$#EDDF#I)Cs$#S:%*s$%EDDF#I3s$&EDDF%#ZShs$'EDDFS,)Cs$'S:s$&*s$)EDDF#I3s$*EDDF%#@s$+EDDF'#;Cs$*s$')C.S+#*s$.EDDF#IVSFCs$gWSiC#s$s)C'S0#*s$2EDDF#IVSFCO)C#S+s$/*s$5EDDF#I)C%S+s$4*s$7EDDF#I)C'S0s$7*s$9EDDF#I)Cs$9S+,*s$;EDDF#I3s$<EDDF%#+s$=EDDF(s$5#+s$>EDDF+s$6#+s$?EDDF/s$7#+s$@EDDF4s$8#+s$AEDDF8s$9#l#&#s$8s$2l#'s#%s$D#l#(s#*s$I#j#)C#j#*C#j#+C#j#0C#j#1S3#$JL&CGL%$#&CGJ%H#-%#'QL$H#'LH##s%-$OP$Ps%/%s%.#k##%#k##&#k##(#k##+#k##.#k#)C#k#*C#k#+C#k#0C#k#1S3##S%S&^G#S%S.S&HPS8S6S#S*l#,<%#l#2s$ks$w#l#-s$ss$p#l#2s$}s$x#l#3s#xC#l#4s#vs#o#VSjs#|#ZSks%Ps#|s#y#JG/s%RJ&C#s$#8S*8S#YSlS$N$#S1YSmN%$Q#/s%X&/s%YQ#$#/s%[('&#$&#%&#1LS$&M#S/k##%#VSGs%bN/s%c#/s%dH#G#'G%$%#%%#1PS.&M#S/k##%#j#5C#7NS#$NS#0NS#&C#S#%%##S#N&C&N%$#-&#0S$S*.s$)R,K#s%;)Cs%1S+s#d*s%7EDDF#I)Cs%5S0s#f*s%9EDDF#I)Cs#eS+s%9*s%;EDDF#I+s%<EDDF#s%4s#^+s%=EDDFs#ds%5#+s%>EDDF's%6#+s%?EDDF*s%7#l#&#s%6s%0l#'s%Cs%B#l#(/s%G#j#)C#j#*C#j#+C#$Qs%|#s%.s%}$OL#OH$Hs&$%$#k##&#k##'#k##)#k##+#k#)C#k#*C#k#+C#[GS&S'S(S6S*NS$l#,1$#l#2s%\s%h#l#-s%ds%a#l#2s%ns%i#l#3s#'C#l#4s#1s#)#VSHN#6Cs#=s#4GN#/s&CL#N#VSGs&ES*/s&F#'N#$'#%'#1HS%&M#S/k##%#/s&MP#S%#'S%G$%#%%#1S,S&&M#S/k##%#j#5C#7S$S*$S$S*&Cs#@S*%$##S*S$&Cs#CS$%$#-&#0S%N(Cs$ps$s.#R,K#s&$9Cs&#Js$_;Cs%zs%{)C#S0s$O*s%~EDDF#I+s&#EDDFs#Fs%ws$D+s&$EDDF$s%x#l#&#s%ws%ql#')s&'#l#(+s&,#j#)C#j#*C#'JG##s&a$OJ#OL$Ls&d%$#k##s#F#k##'#k##)#k#)C#k#*C#YGS>S(NS$S%l#,/$#l#2s&>s&J#l#-s&Fs&C#l#2s&Ps&K#l#3AC#l#4s#*s###VSHN#6Cs#{s#-GN##S$s#{'S$N$s#}#%%#k###s#y#S.G'S.S%$G#%%#1SIS'&M#S/k##%#j#5C#6Cs#C#Gs#2L#S%s#3'S%S$$s#5#%%#k###s#BUS7S,/s'9S,#S$#$$7%$#&M1S)k##$#/s'?SI1S4S>&M#S)k##7#j#5C#0S&S%6C($G#P#S%$$%5%$#1SCS(&M#S)k##%#0S(S&#S(#'S(S'$%#%%#&MJS/k##$#j#6M#7S'S.$S'S.0S'S.&C#S.%%##S.S'&C&S'%$#-&#?Cs%{s%n(C#s%s(Cs%j#.#R.%R,K#s'%,Ks#a#,Ks$K#,K'#)Cs&}S:s&~*s'$EDDF#I3s'%EDDFs%\#)Cs'%S0s%c*s''EDDF#I)Cs'&S:s%e*s')EDDF#I3s'*EDDF%#@s'+EDDF(#;Cs'+s'')Cs%jS+#*s'.EDDF#I)Cs'.S0s'-*s'0EDDF#I)Cs'/S+'*s'2EDDF#I3s'3EDDF%#+s'4EDDFs%]s',#+s'5EDDF)s'-#+s'6EDDF-s'.#l#&#s'-s''l#'s%vs'9#l#(9s'>#j#)C#j#*C#j#+C#j#0C#j#1S3#&CJG%H##GL&CJL%$#-&#'JL$H##LH'LP$H#%%#k##s()#k##(#k##+#k#)C#k#*C#k#+C#k#0C#k#1S3#$S?SJ\G#S?SnHSJPS2S$l#,9%#l#2s']s'i#l#-s'es'b#l#2s'os'j#l#3s#RC#l#4s#Ks#C#UG#6Ms#Xs#NQS)##S's#L'S'S&$s#N#%%#&MS)S/k##$#7S(S&$S(S&&Cs#^S&%$##S&S(&Cs#aS(%$#-&#0S>S'(Cs&ds&i(Cs&_#.#R(Cs&ks&l(Cs&b#.#R?Cs&ws&d(C#s&k.#R(C%s&q.#R(Cs&v$.#R(Cs&x(.#R(Cs&ws&r(Cs&n#.#R,K(s((,K$#,K(#,K+#,K.#,K1#,K5#,K9#)Cs()S+s&g*s(+EDDF#I3s(,EDDF#s#a@s(-EDDF#s#fYSos(.EDDSKYSps(/EDDSKZSqs(0EDD$#+s(1EDDFs#\s()#+s(2EDDF#s(*s#[+s(3EDDF(s(+#l#&#s(*s($l#'s&ss(6#l#(/s(;#j#)C#j#*C#j#+C#j#0C#j#1S3#$GL%#s#Y-#s#\#JQ$Qs#Y%$#k###s#?'QH$P##HP'HS,$P#%%#k##s&S#k##(#k##+#k##0#k#)C#k#*C#k#+C#k#0C#k#1S3##SLSM]G#SLS?HSMPS,S#S(l#,;%#l#2s(\s(h#l#-s(ds(a#l#2s(ns(i#l#3s#KC#l#4s#Ts#M#UG#nM#$#6S3G#%#S=#S@j#7M#6MS)#SrS/GVSNS@Gl#/$S@#l#8(s#]#l#8s#cs#]#l#9s$bs$\#l#9s$ps$j#l#8s$ws$r#l#8s%*s%%#l#8s%is%_#l#8s&Us&K#l#:s&\s&Z#l#;s($s'}#l#$s(&s)P#VSNs()#j#<s(+#U#Gj##s(A#ZSOs(Cs(Bs(<s(/#Gl#=s(Gs(E#j#>s(I#U#Gj##s)8#ZSOs):s)9s)3s(M#Gl#=s)@s)=#j#9s)C#j#?s)M#j#@s)O#j#As)Q#j#Bs)S#j#Cs)Y#j#Ds)Z#j#Es)\#j#FC#j#GC#j#HC#j#IC#j#Js)f#j#Ks)g##"). Qed.

