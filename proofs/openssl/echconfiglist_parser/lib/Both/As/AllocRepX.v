(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import GapGrid.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require LazyNodes.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel LazyRestrict LazyLedger LazySR Gap04.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsDepotInv SecGap.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition ALIBCPGSZ : Z := 0xc01f50.   (* [comment removed for export] *)
Definition AGOT_SSP  : Z := 0x5e9798.   (* [comment removed for export] *)
Definition ASSPGUARD : Z := 0xc01cd0.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ALOWSH_SZ : Z := 0x10000000.

(* [comment removed for export] *)
Definition AHSB : Z := 0x2008fff7000.
Lemma AHSB_eq : AHSB = sh AHI_LO.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma sh_ceiling_range : 0x10006fef8000 <= sh aceil <= 0x10007fef8000.
Proof. acb. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia. Qed.
Lemma sh_ceiling_lt_AHI_LO : sh aceil < AHI_LO.
Proof. pose proof sh_ceiling_range. unfold AHI_LO. lia. Qed.

(* [comment removed for export] *)
Definition ehigh (e : word * word) : bool := AHI_LO <? KInv.ehi e.      (* [comment removed for export] *)
Definition hcnt (E : list (word * word)) : Z := zlen (List.filter ehigh E).
Definition hlen (E : list (word * word)) : Z := zsum (map (fun e => bv_unsigned (snd e)) (List.filter ehigh E)).
Definition schigh (sc : schunk) : bool := AHI_LO <? sc_map_beg sc + sc_map_size sc.
Definition hsec (st : astate) : list schunk := List.filter schigh (as_sec st).
Definition AHC0 : Z := 32.            (* [comment removed for export] *)
Definition AHL0 : Z := 2 ^ 38.        (* [comment removed for export] *)
Definition ASECMAX : Z := 2 ^ 32 + 2 ^ 14.   (* [comment removed for export] *)

Lemma hcnt_nil : hcnt [] = 0. Proof. reflexivity. Qed.
Lemma hlen_nil : hlen [] = 0. Proof. reflexivity. Qed.
Lemma hcnt_cons : forall e E, hcnt (e :: E) = (if ehigh e then 1 else 0) + hcnt E.
Proof. intros e E. unfold hcnt, zlen. cbn [List.filter]. destruct (ehigh e); cbn [length]; lia. Qed.
Lemma hlen_cons : forall e E, hlen (e :: E) = (if ehigh e then bv_unsigned (snd e) else 0) + hlen E.
Proof. intros e E. unfold hlen. cbn [List.filter]. destruct (ehigh e); cbn [map zsum]; lia. Qed.
Lemma hcnt_nonneg : forall E, 0 <= hcnt E. Proof. intros E. unfold hcnt, zlen. lia. Qed.
Lemma hlen_nonneg : forall E, 0 <= hlen E.
Proof. intros E. induction E as [|e E IH]; [rewrite hlen_nil; lia|]. rewrite hlen_cons. pose proof (bv_unsigned_in_range _ (snd e)). destruct (ehigh e); lia. Qed.
Lemma hcnt_cons_le : forall e E, hcnt (e :: E) <= 1 + hcnt E.
Proof. intros e E. rewrite hcnt_cons. destruct (ehigh e); lia. Qed.
Lemma hlen_cons_le : forall e E, hlen (e :: E) <= bv_unsigned (snd e) + hlen E.
Proof. intros e E. rewrite hlen_cons. pose proof (bv_unsigned_in_range _ (snd e)). destruct (ehigh e); lia. Qed.
Lemma hcnt_cons_ge : forall e E, hcnt E <= hcnt (e :: E).
Proof. intros e E. rewrite hcnt_cons. destruct (ehigh e); lia. Qed.
Lemma hlen_cons_ge : forall e E, hlen E <= hlen (e :: E).
Proof. intros e E. rewrite hlen_cons. pose proof (bv_unsigned_in_range _ (snd e)). destruct (ehigh e); lia. Qed.
Lemma hcnt_app : forall E1 E2, hcnt (E1 ++ E2) = hcnt E1 + hcnt E2.
Proof. intros E1 E2. unfold hcnt, zlen. rewrite filter_app, length_app. lia. Qed.
Lemma hlen_app : forall E1 E2, hlen (E1 ++ E2) = hlen E1 + hlen E2.
Proof. intros E1 E2. unfold hlen. rewrite filter_app, map_app, zsum_app. reflexivity. Qed.
Lemma hcnt_low_cons : forall e E, KInv.ehi e <= AHI_LO -> hcnt (e :: E) = hcnt E.
Proof. intros e E H. rewrite hcnt_cons. unfold ehigh. destruct (Z.ltb_spec AHI_LO (KInv.ehi e)); lia. Qed.
Lemma hlen_low_cons : forall e E, KInv.ehi e <= AHI_LO -> hlen (e :: E) = hlen E.
Proof. intros e E H. rewrite hlen_cons. unfold ehigh. destruct (Z.ltb_spec AHI_LO (KInv.ehi e)); lia. Qed.
Lemma hcnt_high_cons : forall e E, AHI_LO < KInv.ehi e -> hcnt (e :: E) = 1 + hcnt E.
Proof. intros e E H. rewrite hcnt_cons. unfold ehigh. destruct (Z.ltb_spec AHI_LO (KInv.ehi e)); lia. Qed.
Lemma hlen_high_cons : forall e E, AHI_LO < KInv.ehi e -> hlen (e :: E) = bv_unsigned (snd e) + hlen E.
Proof. intros e E H. rewrite hlen_cons. unfold ehigh. destruct (Z.ltb_spec AHI_LO (KInv.ehi e)); lia. Qed.
Lemma hcnt_low : forall E, Forall (fun e => KInv.ehi e <= AHI_LO) E -> hcnt E = 0.
Proof. intros E H. induction H as [|e E He H IH]; [reflexivity|]. rewrite hcnt_low_cons by exact He. exact IH. Qed.
Lemma hlen_low : forall E, Forall (fun e => KInv.ehi e <= AHI_LO) E -> hlen E = 0.
Proof. intros E H. induction H as [|e E He H IH]; [reflexivity|]. rewrite hlen_low_cons by exact He. exact IH. Qed.
Lemma hcnt_le_len : forall E, hcnt E <= zlen E.
Proof. intros E. induction E as [|e E IH]; [rewrite hcnt_nil; unfold zlen; cbn; lia|]. rewrite hcnt_cons. unfold zlen in *. cbn [length]. destruct (ehigh e); lia. Qed.
Lemma hlen_le_total : forall E, hlen E <= zsum (map (fun e => bv_unsigned (snd e)) E).
Proof.
  intros E. induction E as [|e E IH]; [rewrite hlen_nil; cbn; lia|]. rewrite hlen_cons. cbn [map zsum].
  pose proof (bv_unsigned_in_range _ (snd e)). destruct (ehigh e); lia.
Qed.
(* [comment removed for export] *)
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
Lemma hcnt_map_remove_in : forall E e, In e E -> AHI_LO < KInv.ehi e -> hcnt (map_remove E (fst e)) <= hcnt E - 1.
Proof.
  intros E e IN H. unfold map_remove. induction E as [|e0 E IH]; [destruct IN|]. cbn [List.filter].
  destruct IN as [->|IN].
  - rewrite bv_eqb_refl. cbn [negb]. rewrite (hcnt_high_cons e E H). pose proof (hcnt_map_remove_le E (fst e)) as L. unfold map_remove in L. lia.
  - specialize (IH IN). destruct (negb (bv_eqb (fst e0) (fst e))); [rewrite !hcnt_cons; destruct (ehigh e0); lia| pose proof (hcnt_cons_ge e0 E); lia].
Qed.
Lemma hlen_map_remove_in : forall E e, In e E -> AHI_LO < KInv.ehi e -> hlen (map_remove E (fst e)) <= hlen E - bv_unsigned (snd e).
Proof.
  intros E e IN H. unfold map_remove. induction E as [|e0 E IH]; [destruct IN|]. cbn [List.filter].
  destruct IN as [->|IN].
  - rewrite bv_eqb_refl. cbn [negb]. rewrite (hlen_high_cons e E H). pose proof (hlen_map_remove_le E (fst e)) as L. unfold map_remove in L. lia.
  - specialize (IH IN). destruct (negb (bv_eqb (fst e0) (fst e))); [rewrite !hlen_cons; destruct (ehigh e0); lia| pose proof (hlen_cons_ge e0 E); lia].
Qed.
(* [comment removed for export] *)
Lemma hsec_nil_st : forall st, as_sec st = [] -> hsec st = [].
Proof. intros st E. unfold hsec. rewrite E. reflexivity. Qed.
Lemma zlen_filter_app {A} : forall (f : A -> bool) l1 l2, zlen (List.filter f (l1 ++ l2)) = zlen (List.filter f l1) + zlen (List.filter f l2).
Proof. intros f l1 l2. unfold zlen. rewrite filter_app, length_app. lia. Qed.
Lemma zlen_filter_cons {A} : forall (f : A -> bool) x l, zlen (List.filter f (x :: l)) = (if f x then 1 else 0) + zlen (List.filter f l).
Proof. intros f x l. unfold zlen. cbn [List.filter]. destruct (f x); cbn [length]; lia. Qed.
Lemma zlen_filter_nil {A} : forall (f : A -> bool), zlen (List.filter f (@nil A)) = 0. Proof. reflexivity. Qed.
Lemma zsum_size_filter_app : forall (f : schunk -> bool) l1 l2,
  zsum (map sc_map_size (List.filter f (l1 ++ l2))) = zsum (map sc_map_size (List.filter f l1)) + zsum (map sc_map_size (List.filter f l2)).
Proof. intros f l1 l2. rewrite filter_app, map_app, zsum_app. reflexivity. Qed.
Lemma zsum_size_filter_cons : forall (f : schunk -> bool) x l,
  zsum (map sc_map_size (List.filter f (x :: l))) = (if f x then sc_map_size x else 0) + zsum (map sc_map_size (List.filter f l)).
Proof. intros f x l. cbn [List.filter]. destruct (f x); cbn [map zsum]; lia. Qed.
Lemma schigh_iff : forall sc, schigh sc = true <-> AHI_LO < sc_map_beg sc + sc_map_size sc.
Proof. intros sc. unfold schigh. rewrite Z.ltb_lt. tauto. Qed.
Lemma ehigh_wz : forall a n, 0 <= a < 2^64 -> 0 <= n < 2^64 -> ehigh (wz a, wz n) = schigh (mkSC a n 0).
Proof. intros a n Ha Hn. unfold ehigh, schigh, KInv.ehi, wz. cbn [fst snd sc_map_beg sc_map_size]. rewrite !unsigned_lit by lia. reflexivity. Qed.
End HCW.

Section X.
  Context {HCEIL : HeapCeil}.
  Variable s : ast.
  Let st := a_st s.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition awin_vis (m : mem) : Prop :=
    forall x : word, in_rangesb x (a_S s) = true -> wview asegs m x <> None.

  (* [comment removed for export] *)
  Definition flagsx_rep (m : mem) : Prop :=
       rw_cells asegs m ALIBCPGSZ [C8 (wz 4096)]
    /\ rw_cells asegs m AGOT_SSP [C8 (wz ASSPGUARD)]
    /\ (exists g : word, rw_cells asegs m ASSPGUARD [C8 g])
    /\ rw_cells asegs m (ACFLAGS + 219) [C1 (b8 1)]
    /\ (exists b : byte, rw_cells asegs m (ACFLAGS + 244) [C1 b]).

  Definition AREPX (m : mem) : Prop := AREP s m /\ awin_vis m /\ flagsx_rep m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition akernel (mo : Model) : Prop :=
    let h := m_vmmaps mo in
       (* [comment removed for export] *)
       (forall e, In e (vm_reserved h) -> bv_unsigned (fst e) + bv_unsigned (snd e) <= AIMG_TOP)
    /\ (* [comment removed for export] *)
       (vm_limit h = target_alloc_limit /\ alloc_top h = hceil)
    /\ (* [comment removed for export] *)
       (forall x : word,
          (a_thr s <= bv_unsigned x < a_thr s + kPageSize \/ a_ctx s <= bv_unsigned x < a_ctx s + 160
           \/ a_sb s <= bv_unsigned x < a_sb s + kSpaceSize + kPageSize \/ a_pa s <= bv_unsigned x < a_pa s + kPtrArrayReserve
           \/ a_fsb s <= bv_unsigned x < a_fsb s + AFS_SIZE
           \/ sh AHI_LO <= bv_unsigned x < AHI_LO) ->               (* [comment removed for export] *)
          in_rangesb x (vm_maps h) = true)
    /\ (* [comment removed for export] *)
       (forall (a n : word) (c : Z), 0 <= c < kNumClasses -> RB s c <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= RB s c + kRegionSize ->
          map_contains (vm_maps h) a n = true)
    /\ (forall a n : word, a_pa s <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= a_pa s + kPtrArrayReserve ->
          map_contains (vm_maps h) a n = true)
    /\ (forall a n : word, sh AHI_LO <= bv_unsigned a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= sh aceil ->
          map_contains (vm_maps h) a n = true)
    /\ (* [comment removed for export] *)
       (forall x : word, a_sb s <= bv_unsigned x < a_sb s + kSpaceSize + kPageSize -> in_rangesb x (a_Zr s) = false)
    /\ (forall x : word, a_pa s <= bv_unsigned x < a_pa s + kPtrArrayReserve -> in_rangesb x (a_Zr s) = false)
    /\ (forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x (a_Zr s) = true /\ in_rangesb x (a_L s) = true)
    /\ (* [comment removed for export] *)
       (forall x : word, in_rangesb x (vm_noaccess h) = true -> in_rangesb x (vm_maps h) = true)
    /\ (forall sc (x : word), In sc (as_sec st) -> sc_map_beg sc <= bv_unsigned x < sc_map_beg sc + sc_map_size sc ->
          in_rangesb x (vm_noaccess h) = false)
    /\ (* [comment removed for export] *)
       (forall sc, In sc (as_sec st) -> In (wz (sc_map_beg sc), wz (sc_map_size sc)) (vm_maps h))
    /\ (* [comment removed for export] *)
       (forall x : word, ALOWSH_LO <= bv_unsigned x < AHI_LO -> in_rangesb x (vm_maps h) = true)
    /\ (forall a n : word, sh AIMG_TOP <= bv_unsigned a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO ->
          map_contains (vm_maps h) a n = true)
    /\ (forall x : word, sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO -> in_rangesb x (a_Zr s) = true /\ in_rangesb x (a_L s) = true)
    /\ (* [comment removed for export] *)
       (forall x : word, AIMG_LO <= bv_unsigned x < AIMG_TOP -> in_rangesb x (vm_reserved h) = true)
    /\ (* [comment removed for export] *)
       (hcnt (vm_maps h) <= AHC0 + zlen (hsec st) /\ hlen (vm_maps h) <= AHL0 + zsum (map sc_map_size (hsec st))
        /\ (forall sc, In sc (as_sec st) -> 0 <= sc_map_size sc <= ASECMAX))
    /\ (* [comment removed for export] *)
       (forall a n : word, (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil)
                           \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
          region_free (vm_noaccess h) a n = true).

  Definition AMODELX (mo : Model) : Prop := AMODEL s mo /\ akernel mo.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Derived.
    Variable mo : Model.
    Hypothesis AK : akernel mo.
    Let h := m_vmmaps mo.

    Lemma ak_resf : forall a k : word, AIMG_TOP <= bv_unsigned a -> region_free (vm_reserved h) a k = true.
    Proof.
      intros a k Ha. destruct AK as (K1 & _). apply region_free_introZ. intros e sz He.
      specialize (K1 (e, sz) He). cbn [fst snd] in K1. pose proof (bv_unsigned_in_range _ k). right. lia.
    Qed.
    Lemma ak_resf_hi : forall a k : word, AHI_LO <= bv_unsigned a -> region_free (vm_reserved h) a k = true.
    Proof. intros a k Ha. apply ak_resf. unfold AHI_LO, AIMG_TOP in *. lia. Qed.
    Lemma ak_resf_sh : forall a k : word, sh AHI_LO <= bv_unsigned a -> region_free (vm_reserved h) a k = true.
    Proof. intros a k Ha. apply ak_resf. unfold sh, ASHADOW_BASE, AHI_LO, AIMG_TOP in *. lia. Qed.
    (* [comment removed for export] *)
    Lemma ak_hcov : hcnt (vm_maps h) <= AHC0 + zlen (hsec st) /\ hlen (vm_maps h) <= AHL0 + zsum (map sc_map_size (hsec st))
                    /\ (forall sc, In sc (as_sec st) -> 0 <= sc_map_size sc <= ASECMAX).
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K10 & _). exact K10. Qed.

    Lemma ak_limit : vm_limit h = target_alloc_limit.
    Proof. destruct AK as (_ & (K2 & _) & _). exact K2. Qed.
    (* [comment removed for export] *)
    Lemma ak_atop : alloc_top h = hceil.
    Proof. destruct AK as (_ & (_ & K2) & _). exact K2. Qed.
    Lemma ak_atop_ge_aceil : aceil <= alloc_top h.
    Proof. rewrite ak_atop. exact aceil_le_hceil. Qed.
    (* [comment removed for export] *)
    Lemma ak_grant_below_aceil : forall a len, a mod 4096 = 0 -> len mod 4096 = 0 -> a + len <= alloc_top h -> a + len <= aceil.
    Proof. intros a len Ha Hl Hb. rewrite ak_atop in Hb. exact (grant_below_aceil a len Ha Hl Hb). Qed.

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
    Lemma ak_hsm : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. apply ak_hsm_full. pose proof sh_ceiling_lt_AHI_LO. lia. Qed.

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
    Lemma ak_noacc_maps : forall x : word, in_rangesb x (vm_noaccess h) = true -> in_rangesb x (vm_maps h) = true.
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K6a & _). exact K6a. Qed.
    (* [comment removed for export] *)
    Lemma ak_sec_noacc : forall sc (x : word), In sc (as_sec st) -> sc_map_beg sc <= bv_unsigned x < sc_map_beg sc + sc_map_size sc ->
      in_rangesb x (vm_noaccess h) = false.
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K6b & _). exact K6b. Qed.
    (* [comment removed for export] *)
    Lemma ak_free_noacc : forall (a n x : word), region_free (vm_maps h) a n = true ->
      bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> in_rangesb x (vm_noaccess h) = false.
    Proof.
      intros a n x FR Hx. destruct (in_rangesb x (vm_noaccess h)) eqn:E; [| reflexivity]. exfalso.
      pose proof (ak_noacc_maps x E) as M. rewrite (LazyNodes.region_free_not_in _ a n x FR Hx) in M. discriminate M.
    Qed.
    Lemma ak_secmaps : forall sc, In sc (as_sec st) -> In (wz (sc_map_beg sc), wz (sc_map_size sc)) (vm_maps h).
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K7 & _). exact K7. Qed.

    (* [comment removed for export] *)
    Lemma ak_shland : forall x : word, ALOWSH_LO <= bv_unsigned x < AHI_LO -> in_rangesb x (vm_maps h) = true.
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K8a & _). exact K8a. Qed.
    Lemma ak_lsm : forall x : word, sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO -> in_rangesb x (vm_maps h) = true.
    Proof. intros x Hx. apply ak_shland. unfold sh, ASHADOW_BASE, AIMG_TOP, ALOWSH_LO, AHI_LO in *. lia. Qed.
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
    Lemma ak_lsh2 : forall x : word,
      (sh AHI_LO <= bv_unsigned x < sh aceil \/ sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO) -> in_rangesb x (a_L s) = true.
    Proof. intros x [Hx|Hx]; [apply ak_lsh; exact Hx| apply ak_lsl; exact Hx]. Qed.
    Lemma ak_shm2 : forall x : word,
      (sh AHI_LO <= bv_unsigned x < sh aceil \/ sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO) -> in_rangesb x (vm_maps h) = true.
    Proof. intros x [Hx|Hx]; [apply ak_hsm; exact Hx| apply ak_lsm; exact Hx]. Qed.
    Lemma ak_shmc2 : forall a n : word, 0 < bv_unsigned n ->
      (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
      map_contains (vm_maps h) a n = true.
    Proof. intros a n Hn [[H1 H2]|[H1 H2]]; [apply ak_hsmc| apply ak_lsmc]; assumption. Qed.
    Lemma ak_shrf2 : forall a n : word,
      (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
      region_free (vm_reserved h) a n = true.
    Proof. intros a n [[H1 H2]|[H1 H2]]; apply ak_resf; unfold sh, ASHADOW_BASE, AHI_LO, AIMG_TOP in *; lia. Qed.
    (* [comment removed for export] *)
    Lemma ak_shna : forall a n : word,
      (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
      region_free (vm_noaccess h) a n = true.
    Proof. destruct AK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K11). exact K11. Qed.

    (* [comment removed for export] *)
    Lemma grant_aapp : forall (a : word) (n : Z),
      bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a -> bv_unsigned a + n <= alloc_top h -> n mod 4096 = 0 -> 0xF000 < n ->
      region_free (vm_reserved h ++ vm_maps h) a (wz n) = true -> aapp (bv_unsigned a) n.
    Proof.
      intros a n AL POS TOP NAL BIG FREE.
      assert (CE : bv_unsigned a + n <= aceil).
      { apply ak_grant_below_aceil; [| exact NAL| exact TOP]. unfold page_size in AL. exact AL. }
      pose proof aceil_facts as AF.
      assert (NW : bv_unsigned (wz n) = n) by (unfold wz; apply unsigned_lit; lia).
      assert (NOTIN : forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + n ->
                       in_rangesb x (vm_reserved h) = false /\ in_rangesb x (vm_maps h) = false).
      { intros x Hx. pose proof (LazyNodes.region_free_not_in _ a (wz n) x FREE ltac:(rewrite NW; exact Hx)) as NI.
        rewrite in_rangesb_app in NI. apply Bool.orb_false_iff in NI. exact NI. }
      assert (A4096 : 4096 <= bv_unsigned a) by (unfold page_size in AL; Z.div_mod_to_equations; lia).
      destruct (Z.lt_ge_cases (bv_unsigned a) AIMG_TOP) as [LOWIMG|ABOVE].
      - exfalso. destruct (Z.lt_ge_cases (bv_unsigned a) AIMG_LO) as [BELOW|INIMG].
        + destruct (NOTIN (wz AIMG_LO)) as [R _]; [unfold wz; rewrite unsigned_lit by (unfold AIMG_LO; lia); unfold AIMG_LO in *; lia|].
          rewrite (ak_imgr (wz AIMG_LO)) in R; [discriminate|]. unfold wz; rewrite unsigned_lit by (unfold AIMG_LO; lia). unfold AIMG_LO, AIMG_TOP; lia.
        + destruct (NOTIN a) as [R _]; [lia|]. rewrite (ak_imgr a) in R; [discriminate| lia].
      - destruct (Z.le_gt_cases (bv_unsigned a + n) ALOWSH_LO) as [LO2|NOTLO].
        + left. split; assumption.
        + destruct (Z.lt_ge_cases (bv_unsigned a) AHI_LO) as [INLAND|HI].
          * exfalso. destruct (Z.lt_ge_cases (bv_unsigned a) ALOWSH_LO) as [B|B].
            -- destruct (NOTIN (wz ALOWSH_LO)) as [_ M]; [unfold wz; rewrite unsigned_lit by (unfold ALOWSH_LO; lia); lia|].
               rewrite (ak_shland (wz ALOWSH_LO)) in M; [discriminate|]. unfold wz; rewrite unsigned_lit by (unfold ALOWSH_LO; lia).
               unfold ALOWSH_LO, AHI_LO; lia.
            -- destruct (NOTIN a) as [_ M]; [lia|]. rewrite (ak_shland a) in M; [discriminate| lia].
          * right. split; assumption.
    Qed.
  End Derived.

  (* [comment removed for export] *)
  Lemma akernel_mat : forall mo mo', akernel mo -> same_but_materialized mo mo' -> akernel mo'.
  Proof. intros mo mo' AK SB. unfold akernel in *. rewrite (same_but_materialized_vmmaps _ _ SB). exact AK. Qed.
  Lemma AMODELX_mat : forall mo mo', AMODELX mo -> same_but_materialized mo mo' -> AMODELX mo'.
  Proof. intros mo mo' [A K] SB. split; [eapply AMODEL_mat; eassumption| eapply akernel_mat; eassumption]. Qed.

  (* [comment removed for export] *)
  Lemma awin_vis_wmono : forall m m', awin_vis m -> wmono asegs m m' -> awin_vis m'.
  Proof. intros m m' V W x Hx. apply W. apply V. exact Hx. Qed.
End X.
Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition depot_cov (d : depot) (mo : Model) : Prop :=
  forall x : word, (d_nb d <= bv_unsigned x < d_nb d + 16 * 65536 \/ d_sb d <= bv_unsigned x < d_sb d + 8 * 131072) ->
                   in_rangesb x (vm_maps (m_vmmaps mo)) = true.
Lemma depot_cov_mat : forall d mo mo', depot_cov d mo -> same_but_materialized mo mo' -> depot_cov d mo'.
Proof. intros d mo mo' C SB. unfold depot_cov in *. rewrite (same_but_materialized_vmmaps _ _ SB). exact C. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AGAP (n : Z) (mo : Model) : Prop :=
  let h := m_vmmaps mo in let E := vm_reserved h ++ vm_maps h in
     AHI_LO + cost n AHI_LO E + n <= alloc_top h.
(* [comment removed for export] *)

Lemma AGAP_mat : forall n mo mo', AGAP n mo -> same_but_materialized mo mo' -> AGAP n mo'.
Proof. intros n mo mo' G SB. unfold AGAP in *. rewrite (same_but_materialized_vmmaps _ _ SB). exact G. Qed.
Lemma AGAP_mono : forall n n' mo, n <= n' -> 0 < n -> AGAP n' mo -> AGAP n mo.
Proof.
  intros n n' mo LE POS G2. unfold AGAP in *.
  pose proof (cost_mono_n n n' AHI_LO (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) LE). lia.
Qed.

(* [comment removed for export] *)
Lemma cost_high_bound : forall n E, 0 < n -> cost n AHI_LO E <= hlen E + hcnt E * (n + 4096).
Proof.
  intros n E Hn. induction E as [|e E IH]; [rewrite cost_nil, hlen_nil, hcnt_nil; lia|].
  rewrite cost_cons, hlen_cons, hcnt_cons. unfold ecost, ehigh.
  destruct (Z.ltb_spec AHI_LO (KInv.ehi e)) as [H|H].
  - unfold KInv.ehi, KInv.elo in *. pose proof (bv_unsigned_in_range _ (fst e)). lia.
  - lia.
Qed.
Theorem AGAP_of_akernel : forall s mo n, akernel s mo -> 0 < n ->
  AHI_LO + (AHL0 + zsum (map sc_map_size (hsec (a_st s)))) + (AHC0 + zlen (hsec (a_st s))) * (n + 4096) + n <= hceil ->
  AGAP n mo.
Proof.
  intros s mo n AK Hn ROOM. unfold AGAP.
  pose proof AK as (K1 & (_ & K2) & _). pose proof (ak_hcov s mo AK) as (C1 & C2 & _).
  rewrite K2, cost_app.
  assert (R0 : cost n AHI_LO (vm_reserved (m_vmmaps mo)) = 0).
  { assert (L : Forall (fun e => KInv.ehi e <= AHI_LO) (vm_reserved (m_vmmaps mo))).
    { apply Forall_forall. intros e He. specialize (K1 e He). unfold KInv.ehi, AHI_LO, AIMG_TOP in *. lia. }
    clear - L Hn. induction L as [|e E He L IH]; [apply cost_nil|]. rewrite cost_cons, IH, (ecost_below n AHI_LO e He). reflexivity. }
  pose proof (cost_high_bound n (vm_maps (m_vmmaps mo)) Hn) as CB.
  pose proof (hcnt_nonneg (vm_maps (m_vmmaps mo))). pose proof (hlen_nonneg (vm_maps (m_vmmaps mo))).
  assert (M : hcnt (vm_maps (m_vmmaps mo)) * (n + 4096) <= (AHC0 + zlen (hsec (a_st s))) * (n + 4096)) by (apply Z.mul_le_mono_nonneg_r; lia).
  lia.
Qed.

End HCW.

(* [comment removed for export] *)
Ltac acb ::=
  let K := fresh "ACEILB" in
  pose proof (conj aceil_facts sh_ceiling_range
              : (0x7fff7f800000 <= aceil <= 0x7fffff800000 /\ aceil mod 4096 = 0 /\ aceil <= hceil < aceil + 4096)
                /\ (0x10006fef8000 <= sh aceil <= 0x10007fef8000)) as K.
