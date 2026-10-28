(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BAllocSim BMmapSim BReach BazyRestrict BazyLedger BazySR BazyNodes.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma asegs_find_segment_none_high : forall a n, 1 <= n -> 7241728 <= a -> find_segment asegs a n = None.
Proof.
  intros a n Hn Ha. unfold asegs, RefMemImage.Ref.loaded_segments. cbn -[Z.leb Z.add Z.of_N].
  cbn [Z.of_N seg_base seg_size RefMemImage.RefMemImage_segment_000 RefMemImage.RefMemImage_segment_001 RefMemImage.RefMemImage_segment_002 RefMemImage.RefMemImage_segment_003
       AsanUbsan.AsanUbsan_segment_000 AsanUbsan.AsanUbsan_segment_001
       AsanUbsan.AsanUbsan_segment_002 AsanUbsan.AsanUbsan_segment_003].
  destruct (Z.leb_spec 65536 a); destruct (Z.leb_spec (a + n) (65536 + 528384)); cbn [andb]; try (exfalso; lia).
  destruct (Z.leb_spec 593920 a); destruct (Z.leb_spec (a + n) (593920 + 970752)); cbn [andb]; try (exfalso; lia).
  destruct (Z.leb_spec 1564672 a); destruct (Z.leb_spec (a + n) (1564672 + 32768)); cbn [andb]; try (exfalso; lia).
  destruct (Z.leb_spec 1597440 a); destruct (Z.leb_spec (a + n) (1597440 + 5644288)); cbn [andb]; try (exfalso; lia).
  reflexivity.
Qed.

Lemma asegs_ro_addr_false_high : forall x : word, 7241728 <= bv_unsigned x -> ro_addr asegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite asegs_find_segment_none_high by lia. reflexivity. Qed.

Section Zfill.
  Variables (a n : word) (m : word -> option byte).
  Hypothesis NW : bv_unsigned a + bv_unsigned n <= 2^64.
  Hypothesis HI : 7241728 <= bv_unsigned a.

  Lemma zfill_in : forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> zfill a n m x = Some (Z_to_bv 8 0).
  Proof.
    intros x Hx. unfold zfill, BAllocSim.zmem.
    rewrite (proj2 (Z.leb_le _ _) (proj1 Hx)). rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hx)). reflexivity.
  Qed.

  Lemma zfill_munch : munch [(bv_unsigned a, bv_unsigned a + bv_unsigned n)] m (zfill a n m).
  Proof. intros x Hx. cbn [outside fst snd] in Hx. apply zfill_out. lia. Qed.

  Lemma zfill_wmono : wmono asegs m (zfill a n m).
  Proof.
    intros x Hx. unfold wview in *. unfold zfill, BAllocSim.zmem in *.
    destruct (Z.leb (bv_unsigned a) (bv_unsigned x) && Z.ltb (bv_unsigned x) (bv_unsigned a + bv_unsigned n))%bool; [discriminate| exact Hx].
  Qed.

  Lemma zfill_mem_inv : mem_inv asegs m -> mem_inv asegs (zfill a n m).
  Proof.
    intros MI x b Hx. unfold zfill, BAllocSim.zmem in Hx.
    destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned a + bv_unsigned n));
      cbn [andb] in Hx; try exact (MI x b Hx).
    apply asegs_ro_addr_false_high. lia.
  Qed.

  Lemma zfill_stk : stk asegs (zfill a n m) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
  Proof.
    pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 n).
    split; [lia|]. split; [exact NW|]. intros x Hx.
    assert (E : zfill a n m (wa x) = Some (Z_to_bv 8 0)) by (apply zfill_in; rewrite wa_unsigned by lia; lia).
    split.
    - unfold wview. rewrite E. discriminate.
    - exists (Z_to_bv 8 0). unfold mrd. rewrite E. reflexivity.
  Qed.
End Zfill.

Section Unfill.
  Variables (a n : word) (m : word -> option byte).

  Lemma unfill_munch : munch [(bv_unsigned a, bv_unsigned a + bv_unsigned n)] m (unfill a n m).
  Proof. intros x Hx. cbn [outside fst snd] in Hx. apply unfill_out. lia. Qed.

  Lemma unfill_mem_inv : mem_inv asegs m -> mem_inv asegs (unfill a n m).
  Proof.
    intros MI x b Hx. unfold unfill in Hx.
    destruct (Z.leb (bv_unsigned a) (bv_unsigned x) && Z.ltb (bv_unsigned x) (bv_unsigned a + bv_unsigned n))%bool; [discriminate| exact (MI x b Hx)].
  Qed.
End Unfill.

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

Definition owin (L S : list (word * word)) (W : word * word) (m : word -> option byte) : word -> option byte :=
  fun a => if zin_rangeb (bv_unsigned a) W && hiddenb L S a then Some (Z_to_bv 8 0) else m a.

Lemma open_window_MS : forall L S Zr W msF mo R F pc fc rv m,
  lzok asegs L S Zr (mkCfg msF mo) ->
  restrict L S msF = MS R F pc fc rv m (seg_rom asegs) ->
  (forall a, zin_rangeb (bv_unsigned a) W = true -> in_rangesb a Zr = true) ->
  eager_used mo + pages_total (W :: S) * page_size <= vm_limit (m_vmmaps mo) ->
  lzok asegs L (W :: S) Zr (mkCfg msF mo) /\ restrict L (W :: S) msF = MS R F pc fc rv (owin L S W m) (seg_rom asegs).
Proof.
  intros L S Zr W msF mo R F pc fc rv m OK VIS HW BUD.
  destruct (lzok_open_window asegs L S Zr W msF mo OK HW BUD) as [OK' E]. split; [exact OK'|]. rewrite E, VIS. reflexivity.
Qed.

Section Owin.
  Variables (L S : list (word * word)) (lo n : Z).
  Hypothesis LO0 : 7241728 <= lo. Hypothesis HI0 : lo + n <= 2^64. Hypothesis N0 : 0 < n.
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

  Hypothesis WL : forall x : word, lo <= bv_unsigned x < lo + n -> in_rangesb x L = true.
  Hypothesis SV : forall x : word, lo <= bv_unsigned x < lo + n -> in_rangesb x S = true -> wview asegs m x <> None.

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

Lemma ecall_aa368 : fetch_word asegs (Z_to_bv 64 0xcc570) = Some ECALLW.
Proof. vm_compute. reflexivity. Qed.

Lemma wz_ne0 : forall z, 0 < z < 2^64 -> wz z <> Z_to_bv 64 0.
Proof. intros z Hz E. apply (f_equal bv_unsigned) in E. unfold wz in E. rewrite !unsigned_lit in E by lia. lia. Qed.

Lemma nooverlap_cons_free : forall maps (a n : word),
  region_free maps a n = true -> nooverlap maps -> nooverlap ((a, n) :: maps).
Proof.
  intros maps a n RF NO. split; [| exact NO]. intros [b s] IN.
  pose proof (BRefNodes.region_free_In maps a n b s RF IN). unfold BazyLedger.hi, BazyLedger.lo. cbn [fst snd]. lia.
Qed.

Lemma map_contains_cons : forall maps (e : word * word) (lo n : word),
  map_contains maps lo n = true -> map_contains (e :: maps) lo n = true.
Proof. intros maps e lo n H. unfold map_contains in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.

Lemma entries_nowrap_cons' : forall maps (e : word * word), entry_nowrap e -> entries_nowrap maps -> entries_nowrap (e :: maps).
Proof. intros maps e He H x [<-|IN]; [exact He| exact (H x IN)]. Qed.

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

Lemma nonvm_same_atop : forall mo mo', nonvm_same mo mo' -> alloc_top (m_vmmaps mo') = alloc_top (m_vmmaps mo).
Proof. intros mo mo' (_&_&_&_&_&_&E). exact E. Qed.

Lemma free_vs_mapped : forall (res maps : list (word * word)) (a n B K : Z),
  region_free (res ++ maps) (wz a) (wz n) = true -> 0 < a -> 0 < n -> a + n <= 2^64 ->
  0 <= B -> B < 2^64 -> 0 < K ->
  (forall x : word, B <= bv_unsigned x < B + K -> in_rangesb x maps = true) ->
  a + n <= B \/ B + K <= a.
Proof.
  intros res maps a n B K FREE A0 N0 AN HB HB2 HK HM.
  destruct (Z.le_gt_cases (a + n) B) as [|NE1]; [left; lia|]. destruct (Z.le_gt_cases (B + K) a) as [|NE2]; [right; lia|]. exfalso.
  remember (wa (Z.max a B)) as x eqn:EX. assert (XU : bv_unsigned x = Z.max a B) by (subst x; apply wa_unsigned; lia).
  pose proof (region_free_not_in _ _ _ x (region_free_app_r _ _ _ _ FREE)) as X.
  unfold wz in X. rewrite (unsigned_lit a), (unsigned_lit n), XU in X by lia.
  specialize (HM x). rewrite XU in HM. rewrite HM in X by lia. specialize (X ltac:(lia)). discriminate X.
Qed.

