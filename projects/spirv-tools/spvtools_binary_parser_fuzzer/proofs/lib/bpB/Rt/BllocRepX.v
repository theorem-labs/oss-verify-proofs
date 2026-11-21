(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the ledger invariant's entries_nonzero conjunct; the reserved ledger now holds the launch's vDSO/vvar pair: the kernel invariant split into the image half and the launch's reserved pair, with the room the pair costs). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BapGrid.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BazyNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel BazyRestrict BazyLedger BazySR Bap04.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsDepotInv BecGap.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition ALIBCPGSZ : Z := 0x6e5b18.
Definition AGOT_SSP  : Z := 0x185ed0.
Definition ASSPGUARD : Z := 0x6e5898.

Definition ALOWSH_SZ : Z := 0x10000000.

Definition AHSB : Z := 0x2008fff7000.
Lemma AHSB_eq : AHSB = sh AHI_LO.
Proof. reflexivity. Qed.

Lemma sh_ceiling_range : 0x10006fef8000 <= sh aceil <= 0x10007fef8000.
Proof. acb. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia. Qed.
Lemma sh_ceiling_lt_AHI_LO : sh aceil < AHI_LO.
Proof. pose proof sh_ceiling_range. unfold AHI_LO. lia. Qed.

Definition ehigh (e : word * word) : bool := AHI_LO <? BKInv.ehi e.
Definition hcnt (E : list (word * word)) : Z := zlen (List.filter ehigh E).
Definition hlen (E : list (word * word)) : Z := zsum (map (fun e => bv_unsigned (snd e)) (List.filter ehigh E)).
Definition schigh (sc : schunk) : bool := AHI_LO <? sc_map_beg sc + sc_map_size sc.
Definition hsec (st : astate) : list schunk := List.filter schigh (as_sec st).
Definition AHC0 : Z := 32.
Definition AHL0 : Z := 2 ^ 38.
Definition ASECMAX : Z := 2 ^ 32 + 2 ^ 14.

Lemma hcnt_nil : hcnt [] = 0. Proof. reflexivity. Qed.
Lemma hlen_nil : hlen [] = 0. Proof. reflexivity. Qed.
Lemma hcnt_cons : forall e E, hcnt (e :: E) = (if ehigh e then 1 else 0) + hcnt E.
Proof. intros e E. unfold hcnt, zlen. cbn [List.filter]. destruct (ehigh e); cbn [length]; lia. Qed.
Lemma hlen_cons : forall e E, hlen (e :: E) = (if ehigh e then bv_unsigned (snd e) else 0) + hlen E.
Proof. intros e E. unfold hlen. cbn [List.filter]. destruct (ehigh e); cbn [map zsum]; lia. Qed.
Lemma hcnt_nonneg : forall E, 0 <= hcnt E. Proof. intros E. unfold hcnt, zlen. lia. Qed.
Lemma hlen_nonneg : forall E, 0 <= hlen E.
Proof. intros E. induction E as [|e E IH]; [rewrite hlen_nil; lia|]. rewrite hlen_cons. pose proof (bv_unsigned_in_range _ (snd e)). destruct (ehigh e); lia. Qed.

Lemma hcnt_cons_ge : forall e E, hcnt E <= hcnt (e :: E).
Proof. intros e E. rewrite hcnt_cons. destruct (ehigh e); lia. Qed.
Lemma hlen_cons_ge : forall e E, hlen E <= hlen (e :: E).
Proof. intros e E. rewrite hlen_cons. pose proof (bv_unsigned_in_range _ (snd e)). destruct (ehigh e); lia. Qed.
Lemma hcnt_app : forall E1 E2, hcnt (E1 ++ E2) = hcnt E1 + hcnt E2.
Proof. intros E1 E2. unfold hcnt, zlen. rewrite filter_app, length_app. lia. Qed.
Lemma hlen_app : forall E1 E2, hlen (E1 ++ E2) = hlen E1 + hlen E2.
Proof. intros E1 E2. unfold hlen. rewrite filter_app, map_app, zsum_app. reflexivity. Qed.
Lemma hcnt_low_cons : forall e E, BKInv.ehi e <= AHI_LO -> hcnt (e :: E) = hcnt E.
Proof. intros e E H. rewrite hcnt_cons. unfold ehigh. destruct (Z.ltb_spec AHI_LO (BKInv.ehi e)); lia. Qed.
Lemma hlen_low_cons : forall e E, BKInv.ehi e <= AHI_LO -> hlen (e :: E) = hlen E.
Proof. intros e E H. rewrite hlen_cons. unfold ehigh. destruct (Z.ltb_spec AHI_LO (BKInv.ehi e)); lia. Qed.
Lemma hcnt_high_cons : forall e E, AHI_LO < BKInv.ehi e -> hcnt (e :: E) = 1 + hcnt E.
Proof. intros e E H. rewrite hcnt_cons. unfold ehigh. destruct (Z.ltb_spec AHI_LO (BKInv.ehi e)); lia. Qed.
Lemma hlen_high_cons : forall e E, AHI_LO < BKInv.ehi e -> hlen (e :: E) = bv_unsigned (snd e) + hlen E.
Proof. intros e E H. rewrite hlen_cons. unfold ehigh. destruct (Z.ltb_spec AHI_LO (BKInv.ehi e)); lia. Qed.
Lemma hcnt_low : forall E, Forall (fun e => BKInv.ehi e <= AHI_LO) E -> hcnt E = 0.
Proof. intros E H. induction H as [|e E He H IH]; [reflexivity|]. rewrite hcnt_low_cons by exact He. exact IH. Qed.
Lemma hlen_low : forall E, Forall (fun e => BKInv.ehi e <= AHI_LO) E -> hlen E = 0.
Proof. intros E H. induction H as [|e E He H IH]; [reflexivity|]. rewrite hlen_low_cons by exact He. exact IH. Qed.
Lemma hcnt_le_len : forall E, hcnt E <= zlen E.
Proof. intros E. induction E as [|e E IH]; [rewrite hcnt_nil; unfold zlen; cbn; lia|]. rewrite hcnt_cons. unfold zlen in *. cbn [length]. destruct (ehigh e); lia. Qed.
Lemma hlen_le_total : forall E, hlen E <= zsum (map (fun e => bv_unsigned (snd e)) E).
Proof.
  intros E. induction E as [|e E IH]; [rewrite hlen_nil; cbn; lia|]. rewrite hlen_cons. cbn [map zsum].
  pose proof (bv_unsigned_in_range _ (snd e)). destruct (ehigh e); lia.
Qed.

Lemma hcnt_map_remove_le : forall E lo, hcnt (map_remove E lo) <= hcnt E.
Proof.
  intros E lo. unfold map_remove. induction E as [|e E IH]; [cbn; lia|]. cbn [List.filter].
  destruct (negb (bv_eqb (fst e) lo)); [rewrite !hcnt_cons; destruct (ehigh e); lia| pose proof (hcnt_cons_ge e E); lia].
Qed.
Lemma hlen_map_remove_le : forall E lo, hlen (map_remove E lo) <= hlen E.
Proof.
  intros E lo. unfold map_remove. induction E as [|e E IH]; [cbn; lia|]. cbn [List.filter].
  destruct (negb (bv_eqb (fst e) lo)); [rewrite !hlen_cons; destruct (ehigh e); lia| pose proof (hlen_cons_ge e E); lia].
Qed.
Lemma hcnt_map_remove_in : forall E e, In e E -> AHI_LO < BKInv.ehi e -> hcnt (map_remove E (fst e)) <= hcnt E - 1.
Proof.
  intros E e IN H. unfold map_remove. induction E as [|e0 E IH]; [destruct IN|]. cbn [List.filter].
  destruct IN as [->|IN].
  - rewrite bv_eqb_refl. cbn [negb]. rewrite (hcnt_high_cons e E H). pose proof (hcnt_map_remove_le E (fst e)) as L. unfold map_remove in L. lia.
  - specialize (IH IN). destruct (negb (bv_eqb (fst e0) (fst e))); [rewrite !hcnt_cons; destruct (ehigh e0); lia| pose proof (hcnt_cons_ge e0 E); lia].
Qed.
Lemma hlen_map_remove_in : forall E e, In e E -> AHI_LO < BKInv.ehi e -> hlen (map_remove E (fst e)) <= hlen E - bv_unsigned (snd e).
Proof.
  intros E e IN H. unfold map_remove. induction E as [|e0 E IH]; [destruct IN|]. cbn [List.filter].
  destruct IN as [->|IN].
  - rewrite bv_eqb_refl. cbn [negb]. rewrite (hlen_high_cons e E H). pose proof (hlen_map_remove_le E (fst e)) as L. unfold map_remove in L. lia.
  - specialize (IH IN). destruct (negb (bv_eqb (fst e0) (fst e))); [rewrite !hlen_cons; destruct (ehigh e0); lia| pose proof (hlen_cons_ge e0 E); lia].
Qed.

Lemma hsec_nil_st : forall st, as_sec st = [] -> hsec st = [].
Proof. intros st E. unfold hsec. rewrite E. reflexivity. Qed.
Lemma zlen_filter_app {A} : forall (f : A -> bool) l1 l2, zlen (List.filter f (l1 ++ l2)) = zlen (List.filter f l1) + zlen (List.filter f l2).
Proof. intros f l1 l2. unfold zlen. rewrite filter_app, length_app. lia. Qed.

Lemma zsum_size_filter_app : forall (f : schunk -> bool) l1 l2,
  zsum (map sc_map_size (List.filter f (l1 ++ l2))) = zsum (map sc_map_size (List.filter f l1)) + zsum (map sc_map_size (List.filter f l2)).
Proof. intros f l1 l2. rewrite filter_app, map_app, zsum_app. reflexivity. Qed.

Lemma ehigh_wz : forall a n, 0 <= a < 2^64 -> 0 <= n < 2^64 -> ehigh (wz a, wz n) = schigh (mkSC a n 0).
Proof. intros a n Ha Hn. unfold ehigh, schigh, BKInv.ehi, wz. cbn [fst snd sc_map_beg sc_map_size]. rewrite !unsigned_lit by lia. reflexivity. Qed.

Section X.
  Variable s : ast.
  Let st := a_st s.

  Definition awin_vis (m : mem) : Prop :=
    forall x : word, in_rangesb x (a_S s) = true -> wview asegs m x <> None.

  Definition flagsx_rep (m : mem) : Prop :=
       rw_cells asegs m ALIBCPGSZ [C8 (wz 4096)]
    /\ rw_cells asegs m AGOT_SSP [C8 (wz ASSPGUARD)]
    /\ (exists g : word, rw_cells asegs m ASSPGUARD [C8 g])
    /\ rw_cells asegs m (ACFLAGS + 219) [C1 (b8 1)]
    /\ (exists b : byte, rw_cells asegs m (ACFLAGS + 244) [C1 b]).

  Definition AREPX (m : mem) : Prop := AREP s m /\ awin_vis m /\ flagsx_rep m.

  (* LPS 727298f3: [akernel] is [akernel_pre /\ akernel_resx].  [akernel_pre] is the former
     invariant, in order, with only its first conjunct's list changed: that bound held of
     [vm_reserved h] when the ledger was the image's reservations alone, and is false now that
     [State.init_model] appends the launch's vDSO/vvar pair, which hangs off the mmap base and not
     off the image.  The bound keeps its text over the image's reservations; [akernel_resx]
     carries the pair.  An abbreviation, so that a hypothesis of the former conjunction is still
     syntactically one (as in boost-json/fuzz_parse's and boost-beast/http_request's ports). *)
  #[local] Notation akernel_pre mo :=
    ((let h := m_vmmaps mo in

       (forall e, In e (segments_reserved asegs) -> bv_unsigned (fst e) + bv_unsigned (snd e) <= AIMG_TOP)
    /\
       (vm_limit h = target_alloc_limit /\ alloc_top h = hceil)
    /\
       (forall x : word,
          (a_thr s <= bv_unsigned x < a_thr s + kPageSize \/ a_ctx s <= bv_unsigned x < a_ctx s + 160
           \/ a_sb s <= bv_unsigned x < a_sb s + kSpaceSize + kPageSize \/ a_pa s <= bv_unsigned x < a_pa s + kPtrArrayReserve
           \/ a_fsb s <= bv_unsigned x < a_fsb s + AFS_SIZE
           \/ sh AHI_LO <= bv_unsigned x < AHI_LO) ->
          in_rangesb x (vm_maps h) = true)
    /\
       (forall (a n : word) (c : Z), 0 <= c < kNumClasses -> RB s c <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= RB s c + kRegionSize ->
          map_contains (vm_maps h) a n = true)
    /\ (forall a n : word, a_pa s <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= a_pa s + kPtrArrayReserve ->
          map_contains (vm_maps h) a n = true)
    /\ (forall a n : word, sh AHI_LO <= bv_unsigned a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= sh aceil ->
          map_contains (vm_maps h) a n = true)
    /\
       (forall x : word, a_sb s <= bv_unsigned x < a_sb s + kSpaceSize + kPageSize -> in_rangesb x (a_Zr s) = false)
    /\ (forall x : word, a_pa s <= bv_unsigned x < a_pa s + kPtrArrayReserve -> in_rangesb x (a_Zr s) = false)
    /\ (forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x (a_Zr s) = true /\ in_rangesb x (a_L s) = true)
    /\
       (forall x : word, in_rangesb x (vm_noaccess h) = true -> in_rangesb x (vm_maps h) = true)
    /\ (forall sc (x : word), In sc (as_sec st) -> sc_map_beg sc <= bv_unsigned x < sc_map_beg sc + sc_map_size sc ->
          in_rangesb x (vm_noaccess h) = false)
    /\
       (forall sc, In sc (as_sec st) -> In (wz (sc_map_beg sc), wz (sc_map_size sc)) (vm_maps h))
    /\
       (forall x : word, ALOWSH_LO <= bv_unsigned x < AHI_LO -> in_rangesb x (vm_maps h) = true)
    /\ (forall a n : word, sh AIMG_TOP <= bv_unsigned a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO ->
          map_contains (vm_maps h) a n = true)
    /\ (forall x : word, sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO -> in_rangesb x (a_Zr s) = true /\ in_rangesb x (a_L s) = true)
    /\
       (forall x : word, AIMG_LO <= bv_unsigned x < AIMG_TOP -> in_rangesb x (vm_reserved h) = true)
    /\
       (hcnt (vm_maps h) <= AHC0 + zlen (hsec st) /\ hlen (vm_maps h) <= AHL0 + zsum (map sc_map_size (hsec st))
        /\ (forall sc, In sc (as_sec st) -> 0 <= sc_map_size sc <= ASECMAX))
    /\
       (forall a n : word, (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil)
                           \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
          region_free (vm_noaccess h) a n = true))) (only parsing).

  (* The launch's extra reserved intervals ([BothPlanSound.co_res]): the ledger is the image's
     reservations followed by them; each is nonempty, starts a page above [AHI_LO], where every
     window below the allocator's spaces ends, and lies apart from the primary space and from the
     pointer array (both are mapped when the main phase starts, and every mapping is apart from
     the ledger: [co_mres]); there are at most two, of at most 81920 bytes together
     ([State.vdso_len_bounds]).  No step of the main phase changes the ledger or the two bases, so
     the conjunct carries over unchanged ([akernel_resx_same]). *)
  Definition akernel_resx (mo : Model) : Prop :=
    let h := m_vmmaps mo in
    exists rx : list (word * word),
      vm_reserved h = segments_reserved asegs ++ rx
      /\ (forall e, In e rx ->
            0 < bv_unsigned (snd e) /\ AHI_LO + 4096 <= bv_unsigned (fst e)
            /\ (bv_unsigned (fst e) + bv_unsigned (snd e) <= a_sb s \/ a_sb s + kSpaceSize <= bv_unsigned (fst e))
            /\ (bv_unsigned (fst e) + bv_unsigned (snd e) <= a_pa s \/ a_pa s + kPtrArrayReserve <= bv_unsigned (fst e)))
      /\ (length rx <= 2)%nat
      /\ zsum (map (fun e => bv_unsigned (snd e)) rx) <= 81920.

  Definition akernel (mo : Model) : Prop := akernel_pre mo /\ akernel_resx mo.
  (* The former conjunction as a constant: the result type of the recorded proofs that build
     exactly that conjunction ([BS_InstMainK.akernel_main_pre], [BG_MallocLarge3.amodelx_after_pre]). *)
  Definition akernel_pre_d (mo : Model) : Prop := akernel_pre mo.

  Definition AMODELX (mo : Model) : Prop := AMODEL s mo /\ akernel mo.
  (* [AMODELX] with the former kernel conjunction only (see [akernel_pre_d]). *)
  Definition AMODELX_pre (mo : Model) : Prop := AMODEL s mo /\ akernel_pre_d mo.

  Section Derived.
    Variable mo : Model.
    Hypothesis AKfull : akernel mo.
    (* LPS 727298f3: [AK] keeps naming the former conjunction, so the projections below read as
       before; only the lemmas that need the launch's reserved intervals use [AKfull]. *)
    #[local] Notation AK := (proj1 AKfull) (only parsing).
    Let h := m_vmmaps mo.

    Lemma ak_resx : akernel_resx mo.
    Proof. exact (proj2 AKfull). Qed.

    (* LPS 727298f3: a window above the image that ends below the launch's reserved pair (which
       starts a page above [AHI_LO]) misses the whole ledger. *)
    Lemma ak_resf : forall a k : word, AIMG_TOP <= bv_unsigned a ->
      bv_unsigned a + bv_unsigned k <= AHI_LO + 4096 -> region_free (vm_reserved h) a k = true.
    Proof.
      intros a k Ha Hk. destruct ak_resx as [rx [Hr [Hok _]]]. destruct AK as (K1 & _).
      fold h in Hr. rewrite Hr. apply region_free_introZ. intros e sz He.
      apply in_app_or in He as [He|He].
      - specialize (K1 (e, sz) He). cbn [fst snd] in K1. pose proof (bv_unsigned_in_range _ k). right. lia.
      - pose proof (Hok (e, sz) He) as (_ & HK & _). cbn [fst] in HK. left. lia.
    Qed.
    (* LPS 727298f3: the allocator's [RESF] premise ([BllocRep.RESF_pre]): a window inside the
       primary allocator's space misses the image's reservations (they end below [AHI_LO]) and the
       launch's pair (which lies apart from the space). *)
    Lemma ak_resf_hi : forall a k : word, RESF_pre (a_sb s) a k -> region_free (vm_reserved h) a k = true.
    Proof.
      intros a k (Ha & Hs1 & Hs2).
      destruct ak_resx as [rx [Hr [Hok _]]]. destruct AK as (K1 & _).
      fold h in Hr. rewrite Hr. apply region_free_introZ. intros e sz He.
      apply in_app_or in He as [Hseg|Hrx].
      - specialize (K1 (e, sz) Hseg). cbn [fst snd] in K1. right. unfold AHI_LO, AIMG_TOP in *. lia.
      - pose proof (Hok (e, sz) Hrx) as (_ & _ & HP & _). cbn [fst snd] in HP.
        destruct HP as [HP|HP]; [right | left]; lia.
    Qed.
    (* LPS 727298f3: the same for a window inside the pointer array, which lies above the image. *)
    Lemma ak_resf_pa : forall a k : word, AIMG_TOP <= bv_unsigned a -> a_pa s <= bv_unsigned a ->
      bv_unsigned a + bv_unsigned k <= a_pa s + kPtrArrayReserve -> region_free (vm_reserved h) a k = true.
    Proof.
      intros a k Ha Hp1 Hp2.
      destruct ak_resx as [rx [Hr [Hok _]]]. destruct AK as (K1 & _).
      fold h in Hr. rewrite Hr. apply region_free_introZ. intros e sz He.
      apply in_app_or in He as [Hseg|Hrx].
      - specialize (K1 (e, sz) Hseg). cbn [fst snd] in K1. right. lia.
      - pose proof (Hok (e, sz) Hrx) as (_ & _ & _ & HP). cbn [fst snd] in HP.
        destruct HP as [HP|HP]; [right | left]; lia.
    Qed.

    Lemma ak_hcov : hcnt (vm_maps h) <= AHC0 + zlen (hsec st) /\ hlen (vm_maps h) <= AHL0 + zsum (map sc_map_size (hsec st))
                    /\ (forall sc, In sc (as_sec st) -> 0 <= sc_map_size sc <= ASECMAX).
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K10 & _). exact K10. Qed.

    Lemma ak_limit : vm_limit h = target_alloc_limit.
    Proof. destruct AK as (_ & (K2 & _) & _). exact K2. Qed.

    Lemma ak_atop : alloc_top h = hceil.
    Proof. destruct AK as (_ & (_ & K2) & _). exact K2. Qed.

    Lemma ak_tmaps : forall x : word, a_thr s <= bv_unsigned x < a_thr s + kPageSize -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. destruct AK as (_ & _ & K3 & _). apply K3. tauto. Qed.
    Lemma ak_cmaps : forall x : word, a_ctx s <= bv_unsigned x < a_ctx s + 160 -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. destruct AK as (_ & _ & K3 & _). apply K3. tauto. Qed.
    Lemma ak_sbmaps : forall x : word, a_sb s <= bv_unsigned x < a_sb s + kSpaceSize + kPageSize -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. destruct AK as (_ & _ & K3 & _). apply K3. tauto. Qed.
    Lemma ak_pmaps : forall x : word, a_pa s <= bv_unsigned x < a_pa s + kPtrArrayReserve -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. destruct AK as (_ & _ & K3 & _). apply K3. tauto. Qed.
    Lemma ak_fsmaps : forall x : word, a_fsb s <= bv_unsigned x < a_fsb s + AFS_SIZE -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. destruct AK as (_ & _ & K3 & _). apply K3. tauto. Qed.
    Lemma ak_hsm_full : forall x : word, sh AHI_LO <= bv_unsigned x < AHI_LO -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. destruct AK as (_ & _ & K3 & _). apply K3. tauto. Qed.

    Lemma ak_prim : forall (a n : word) (c : Z), 0 <= c < kNumClasses -> RB s c <= bv_unsigned a ->
      bv_unsigned a + bv_unsigned n <= RB s c + kRegionSize -> map_contains (vm_maps h) a n = true.
    Proof. destruct AK as (_ & _ & _ & K4 & _). exact K4. Qed.
    Lemma ak_pamc : forall a n : word, a_pa s <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= a_pa s + kPtrArrayReserve ->
      map_contains (vm_maps h) a n = true.
    Proof. destruct AK as (_ & _ & _ & _ & K4 & _). exact K4. Qed.
    Lemma ak_hsmc : forall a n : word, sh AHI_LO <= bv_unsigned a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= sh aceil ->
      map_contains (vm_maps h) a n = true.
    Proof. destruct AK as (_ & _ & _ & _ & _ & K4 & _). exact K4. Qed.

    Lemma ak_zr_sb : forall x : word, a_sb s <= bv_unsigned x < a_sb s + kSpaceSize + kPageSize -> in_rangesb x (a_Zr s) = false.
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & K5 & _). exact K5. Qed.
    Lemma ak_zr_pa : forall x : word, a_pa s <= bv_unsigned x < a_pa s + kPtrArrayReserve -> in_rangesb x (a_Zr s) = false.
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & K5 & _). exact K5. Qed.
    Lemma ak_zrsh : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x (a_Zr s) = true.
    Proof. intros x Hx. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & K5 & _). apply (proj1 (K5 x Hx)). Qed.
    Lemma ak_lsh : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x (a_L s) = true.
    Proof. intros x Hx. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & K5 & _). apply (proj2 (K5 x Hx)). Qed.

    Lemma ak_sec_noacc : forall sc (x : word), In sc (as_sec st) -> sc_map_beg sc <= bv_unsigned x < sc_map_beg sc + sc_map_size sc ->
      in_rangesb x (vm_noaccess h) = false.
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K6b & _). exact K6b. Qed.

    Lemma ak_secmaps : forall sc, In sc (as_sec st) -> In (wz (sc_map_beg sc), wz (sc_map_size sc)) (vm_maps h).
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K7 & _). exact K7. Qed.

    Lemma ak_shland : forall x : word, ALOWSH_LO <= bv_unsigned x < AHI_LO -> in_rangesb x (vm_maps h) = true.
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K8a & _). exact K8a. Qed.

    Lemma ak_lsmc : forall a n : word, sh AIMG_TOP <= bv_unsigned a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO ->
      map_contains (vm_maps h) a n = true.
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K8b & _). exact K8b. Qed.
    Lemma ak_zrsl : forall x : word, sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO -> in_rangesb x (a_Zr s) = true.
    Proof. intros x Hx. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K8c & _). apply (proj1 (K8c x Hx)). Qed.
    Lemma ak_lsl : forall x : word, sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO -> in_rangesb x (a_L s) = true.
    Proof. intros x Hx. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K8c & _). apply (proj2 (K8c x Hx)). Qed.
    Lemma ak_imgr : forall x : word, AIMG_LO <= bv_unsigned x < AIMG_TOP -> in_rangesb x (vm_reserved h) = true.
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K9 & _). exact K9. Qed.
    Lemma ak_zrsh2 : forall x : word,
      (sh AHI_LO <= bv_unsigned x < sh aceil \/ sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO) -> in_rangesb x (a_Zr s) = true.
    Proof. intros x [Hx|Hx]; [apply ak_zrsh; exact Hx| apply ak_zrsl; exact Hx]. Qed.

    Lemma ak_shmc2 : forall a n : word, 0 < bv_unsigned n ->
      (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
      map_contains (vm_maps h) a n = true.
    Proof. intros a n Hn [[H1 H2]|[H1 H2]]; [apply ak_hsmc| apply ak_lsmc]; assumption. Qed.
    Lemma ak_shrf2 : forall a n : word,
      (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
      region_free (vm_reserved h) a n = true.
    Proof.
      (* LPS 727298f3: [ak_resf] carries the upper premise the launch's pair costs; both bands end
         below [AHI_LO] ([sh_ceiling_lt_AHI_LO]) *)
      intros a n [[H1 H2]|[H1 H2]]; pose proof sh_ceiling_lt_AHI_LO; apply ak_resf;
        unfold sh, ASHADOW_BASE, AHI_LO, AIMG_TOP, ALOWSH_LO in *; lia.
    Qed.

    Lemma ak_shna : forall a n : word,
      (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
      region_free (vm_noaccess h) a n = true.
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K11). exact K11. Qed.

  End Derived.

  Lemma akernel_mat : forall mo mo', akernel mo -> same_but_materialized mo mo' -> akernel mo'.
  Proof. intros mo mo' AK SB. unfold akernel, akernel_resx in *. rewrite (same_but_materialized_vmmaps _ _ SB). exact AK. Qed.
  Lemma AMODELX_mat : forall mo mo', AMODELX mo -> same_but_materialized mo mo' -> AMODELX mo'.
  Proof. intros mo mo' [A K] SB. split; [eapply AMODEL_mat; eassumption| eapply akernel_mat; eassumption]. Qed.

  Lemma awin_vis_wmono : forall m m', awin_vis m -> wmono asegs m m' -> awin_vis m'.
  Proof. intros m m' V W x Hx. apply W. apply V. exact Hx. Qed.
End X.

(* LPS 727298f3: [akernel_resx] reads the ledger and the two bases only; a step that keeps them
   keeps it. *)
Lemma akernel_resx_same : forall s s' mo mo', a_sb s' = a_sb s -> a_pa s' = a_pa s ->
  vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) -> akernel_resx s mo -> akernel_resx s' mo'.
Proof. intros s s' mo mo' Es Ep Er R. unfold akernel_resx in *. cbv zeta in *. rewrite Es, Ep, Er. exact R. Qed.

(* The ledger's vm_maps entries are nonempty (amaps_in_ledger's last conjunct). *)
Lemma AMODELX_nz : forall s mo, AMODELX s mo -> entries_nonzero (vm_maps (m_vmmaps mo)).
Proof. intros s mo ((A & _ & _) & _). destruct A as (_ & _ & _ & _ & _ & _ & NZ). exact NZ. Qed.

Definition depot_cov (d : depot) (mo : Model) : Prop :=
  forall x : word, (d_nb d <= bv_unsigned x < d_nb d + 16 * 65536 \/ d_sb d <= bv_unsigned x < d_sb d + 8 * 32768) ->
                   in_rangesb x (vm_maps (m_vmmaps mo)) = true.
Lemma depot_cov_mat : forall d mo mo', depot_cov d mo -> same_but_materialized mo mo' -> depot_cov d mo'.
Proof. intros d mo mo' C SB. unfold depot_cov in *. rewrite (same_but_materialized_vmmaps _ _ SB). exact C. Qed.

Definition AGAP (n : Z) (mo : Model) : Prop :=
  let h := m_vmmaps mo in let E := vm_reserved h ++ vm_maps h in
     AHI_LO + cost n AHI_LO E + n <= alloc_top h.

Lemma cost_high_bound : forall n E, 0 < n -> cost n AHI_LO E <= hlen E + hcnt E * (n + 4096).
Proof.
  intros n E Hn. induction E as [|e E IH]; [rewrite cost_nil, hlen_nil, hcnt_nil; lia|].
  rewrite cost_cons, hlen_cons, hcnt_cons. unfold ecost, ehigh.
  destruct (Z.ltb_spec AHI_LO (BKInv.ehi e)) as [H|H].
  - unfold BKInv.ehi, BKInv.elo in *. pose proof (bv_unsigned_in_range _ (fst e)). lia.
  - lia.
Qed.
(* LPS 727298f3: the launch's reserved pair lies above the [AHI_LO] gate, so it is charged: each
   entry costs at most its size plus [n + 4096]. *)
Lemma cost_le_sizes : forall n E, 0 < n ->
  cost n AHI_LO E <= zsum (map (fun e => bv_unsigned (snd e)) E) + Z.of_nat (length E) * (n + 4096).
Proof.
  intros n E Hn. induction E as [|e E IH]; [rewrite cost_nil; cbn; lia|].
  rewrite cost_cons. cbn [map length zsum]. unfold ecost.
  pose proof (bv_unsigned_in_range 64 (snd e)). unfold BKInv.ehi, BKInv.elo.
  rewrite Nat2Z.inj_succ.
  destruct (AHI_LO <? bv_unsigned (fst e) + bv_unsigned (snd e)); lia.
Qed.
(* LPS 727298f3: the room grows by what the launch's pair costs: at most two entries of at most
   81920 bytes together ([akernel_resx]), each charging [n + 4096]. *)
Theorem AGAP_of_akernel : forall s mo n, akernel s mo -> 0 < n ->
  AHI_LO + (AHL0 + zsum (map sc_map_size (hsec (a_st s)))) + (AHC0 + zlen (hsec (a_st s))) * (n + 4096) + n
    + (81920 + 2 * (n + 4096)) <= hceil ->
  AGAP n mo.
Proof.
  intros s mo n AK Hn ROOM. unfold AGAP.
  pose proof AK as ((K1 & (_ & K2) & _) & RX). pose proof (ak_hcov s mo AK) as (C1 & C2 & _).
  rewrite K2, cost_app.
  unfold akernel_resx in RX. cbv zeta in RX. destruct RX as [rx [Hrx [_ [Hcnt Hsz]]]].
  assert (R0seg : cost n AHI_LO (segments_reserved asegs) = 0).
  { assert (L : Forall (fun e => BKInv.ehi e <= AHI_LO) (segments_reserved asegs)).
    { apply Forall_forall. intros e He. specialize (K1 e He). unfold BKInv.ehi, AHI_LO, AIMG_TOP in *. lia. }
    clear - L Hn. induction L as [|e E He L IH]; [apply cost_nil|]. rewrite cost_cons, IH, (ecost_below n AHI_LO e He). reflexivity. }
  assert (R0 : cost n AHI_LO (vm_reserved (m_vmmaps mo)) <= 81920 + 2 * (n + 4096)).
  { rewrite Hrx, cost_app, R0seg. pose proof (cost_le_sizes n rx Hn) as CLS.
    assert (ML : Z.of_nat (length rx) * (n + 4096) <= 2 * (n + 4096)) by (apply Z.mul_le_mono_nonneg_r; lia).
    lia. }
  pose proof (cost_high_bound n (vm_maps (m_vmmaps mo)) Hn) as CB.
  pose proof (hcnt_nonneg (vm_maps (m_vmmaps mo))). pose proof (hlen_nonneg (vm_maps (m_vmmaps mo))).
  assert (M : hcnt (vm_maps (m_vmmaps mo)) * (n + 4096) <= (AHC0 + zlen (hsec (a_st s))) * (n + 4096)) by (apply Z.mul_le_mono_nonneg_r; lia).
  lia.
Qed.

End HCW.

Ltac acb ::=
  let K := fresh "ACEILB" in
  pose proof (conj aceil_facts sh_ceiling_range
              : (0x7fff7f800000 <= aceil <= 0x7fffff800000 /\ aceil mod 4096 = 0 /\ aceil <= hceil < aceil + 4096)
                /\ (0x10006fef8000 <= sh aceil <= 0x10007fef8000)) as K.
