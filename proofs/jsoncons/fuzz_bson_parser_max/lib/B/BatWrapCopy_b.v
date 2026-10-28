(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct RefMemcpyLib MemSplit MemsetLib HeapIface HeapIfaceA HeapIfaceABx ArtMem ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatCellEx_b BatPoison_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatInvMalloc_b BatLift_b BatWrapKit_b BatFsInv_b BatFsInvLaws_b BatIfaceLaws_b Ba0RegionPoisoned_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatWrapC_b BatWrapVis_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0AsanMemset_b Ba0AsanMemcpy_b BatWrapC2_b BatWrapRng_b BatWrapMemset_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section WCP.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis AFL : art_alloc_rep_frame_law art_fsg MAPS0 RESV0.
Variable L : asan_layout.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x696000.
Hypothesis HLroimg : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x696000.
Hypothesis HLstimg : forall a, hl_rt_static L a -> 0x10000 <= a < 0x696000.
Hypothesis HLlsan : forall a, rn_tp rn + rn_loff rn <= a < rn_tp rn + rn_loff rn + 4 -> hl_rt_static L a.
#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Hypothesis PRIVZ : forall (G : art_gs art_fsg) LB FF LK A (M Mr : word -> option byte) lazy,
  art_alloc_rep art_fsg rn G LB Mr -> art_fsinv rn (g_fs art_fsg G) FF LK M -> art_client_ok rn LB FF LK A M ->
  live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log art_fsg G)) -> art_kn_ok MAPS0 RESV0 rn -> art_lazy_ok art_fsg rn G A lazy -> art_eager_ok LB A lazy ->
  forall a, art_alloc_zone art_fsg rn G a -> ~ in_block LB a -> art_private L (rn_ar rn) LB FF a.
Hypothesis PRIVF : forall (G : art_gs art_fsg) LB FF LK A (M Mr : word -> option byte) lazy,
  art_alloc_rep art_fsg rn G LB Mr -> art_fsinv rn (g_fs art_fsg G) FF LK M -> art_client_ok rn LB FF LK A M ->
  live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log art_fsg G)) -> art_kn_ok MAPS0 RESV0 rn -> art_lazy_ok art_fsg rn G A lazy -> art_eager_ok LB A lazy ->
  forall a, fs_zone3 rn a -> ~ in_fframe FF a -> art_private L (rn_ar rn) LB FF a.
Hypothesis PRIVCS : forall (G : art_gs art_fsg) LB FF LK A (M Mr : word -> option byte) lazy,
  art_alloc_rep art_fsg rn G LB Mr -> art_fsinv rn (g_fs art_fsg G) FF LK M -> art_client_ok rn LB FF LK A M ->
  live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log art_fsg G)) -> art_kn_ok MAPS0 RESV0 rn -> art_lazy_ok art_fsg rn G A lazy -> art_eager_ok LB A lazy ->
  forall a, cs_zone rn a -> art_private L (rn_ar rn) LB FF a.                      (* [comment removed for export] *)
Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Variable pc0 : word.
Variable FRB : Z.
Hypothesis FRB_rng : 2048 <= FRB <= 2560.
Definition copy_run_spec : Prop :=
  forall (mem0 : word -> option byte) (sp ra : word) (pd ps n s : Z) (bs : list byte) (kS fS lS kD fD lD : Z),
    U sp = s -> fS = Ba0RegionPoisoned_b.SB + ps / 8 -> lS = Ba0RegionPoisoned_b.SB + (ps + n - 1) / 8 ->
    fD = Ba0RegionPoisoned_b.SB + pd / 8 -> lD = Ba0RegionPoisoned_b.SB + (pd + n - 1) / 8 ->
    0 <= n <= 2 ^ 40 -> in_app8 ps n -> in_app8 pd n -> 0x1000000 <= s - FRB /\ s < 2 ^ 64 -> lS + 8 <= s - FRB -> lD + 8 <= s - FRB ->
    (0 < n -> ps + n <= s - FRB \/ s <= ps) -> (0 < n -> pd + n <= s - FRB \/ s <= pd) -> (pd + n <= ps \/ ps + n <= pd) ->
    store_ok ASEGS mem0 (Z_to_bv 64 (s - FRB)) (Z.to_nat FRB) = true -> store_ok ASEGS mem0 (Z_to_bv 64 pd) (Z.to_nat n) = true ->
    rdn ASEGS mem0 (Z_to_bv 64 ps) (Z.to_nat n) = Some bs -> ret_ok ra -> rt_layout_globs mem0 -> mc_icpt_globs mem0 ->
    (0 < n -> forall x : word, fS <= U x < lS -> mem0 x = Some (Z_to_bv 8 0)) -> (0 < n -> mem0 (Z_to_bv 64 lS) = Some (Z_to_bv 8 kS)) ->
    (kS = 0 \/ (ps + n - 1) mod 8 < kS <= 7) ->
    (0 < n <= 64 -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 (fS - fS mod 8)) 8 = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 (lS - lS mod 8)) 8 = Some w1) ->
    (0 < n -> forall x : word, fD <= U x < lD -> mem0 x = Some (Z_to_bv 8 0)) -> (0 < n -> mem0 (Z_to_bv 64 lD) = Some (Z_to_bv 8 kD)) ->
    (kD = 0 \/ (pd + n - 1) mod 8 < kD <= 7) ->
    (0 < n <= 64 -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 (fD - fD mod 8)) 8 = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 (lD - lD mod 8)) 8 = Some w1) ->
    forall regs, getr regs 10 = Z_to_bv 64 pd -> getr regs 11 = Z_to_bv 64 ps -> getr regs 12 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' Mf Mj,
      msteps ASEGS (mkst regs pc0 mem0 (seg_rom ASEGS)) (mkst regs' ra Mf (seg_rom ASEGS))
      /\ getr regs' 10 = Z_to_bv 64 pd /\ keeps_cs regs regs' /\ mem_grows mem0 Mf
      /\ (forall x : word, U x < s - FRB \/ s <= U x -> Mj x = mem0 x)
      /\ (forall x : word, Mf x = wbytes Mj (Z_to_bv 64 pd) bs x).
Hypothesis RUNX : copy_run_spec.

(* [comment removed for export] *)
#[using="HLlo HLhi"] Lemma art_rng_facts0 : forall (G : art_gs art_fsg) LB FF LK A (M : word -> option byte) model sp p n,
  (forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
     0x696000 <= U w /\ U w < rn_HI rn /\ ~ in_block LB (U w) /\ ~ (ar_fs (rn_ar rn) <= U w < ar_fs (rn_ar rn) + FS_BYTES)) ->
  art_client_ok rn LB FF LK A M -> art_fsinv rn (g_fs art_fsg G) FF LK M -> (forall a : word, in_shadow_rw (U a) -> M a <> None) ->
  0 <= p -> 0 <= n <= 2 ^ 40 ->
  (forall i, 0 <= i < n -> hl_img_lo L <= p + i < hl_img_hi L \/ aclient L (rn_ar rn) LB FF sp 2560 (p + i)) -> aacc M p n -> app_rng (rn_ar rn) p n ->
  let Mr0 := mrestrict (bhid A model) M in
  let f := Ba0RegionPoisoned_b.SB + p / 8 in let l := Ba0RegionPoisoned_b.SB + (p + n - 1) / 8 in
  art_vis (bhid A model) p n
  /\ (0 < n -> forall x : word, f <= U x < l -> Mr0 x = Some (Z_to_bv 8 0))
  /\ (exists kL, (0 < n -> Mr0 (Z_to_bv 64 l) = Some (Z_to_bv 8 kL)) /\ (kL = 0 \/ (p + n - 1) mod 8 < kL <= 7))
  /\ (0 < n <= 64 -> exists w0 w1, rdn ASEGS Mr0 (Z_to_bv 64 (f - f mod 8)) 8 = Some w0 /\ rdn ASEGS Mr0 (Z_to_bv 64 (l - l mod 8)) 8 = Some w1)
  /\ l + 8 <= rn_HI rn /\ p + n + 16 <= 2 ^ 47.
Proof.
  intros G LB FF LK A M model sp p n LAZY CLI FS SHDEF Hp Hn CLS AACC APPR Mr0 f l.
  pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
  assert (D47 : p + n + 16 <= 2 ^ 47).
  { destruct APPR as (_ & _ & TOP). destruct (art_cli_facts _ _ _ _ _ _ CLI) as (_ & _ & _ & T16). clear - TOP T16. lia. }
  assert (HSH : l + 8 <= rn_HI rn).
  { unfold l, Ba0RegionPoisoned_b.SB. assert ((p + n - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; clear - D47; lia). change (2 ^ 47 / 8) with 17592186044416 in *. clear - H HI1. lia. }
  destruct (Z_lt_le_dec 0 n) as [Np | Nz].
  - destruct (art_rng_facts rn LB FF LK A M model LAZY CLI L HLlo HLhi (g_fs art_fsg G) FS SHDEF sp 2560 p n Hp Np ltac:(clear - Hn; lia) CLS AACC APPR)
      as (VIS & _ & HZ & (kL & HL & HkL) & HW).
    split; [exact VIS|]. split; [intros _; exact HZ|]. split; [exists kL; split; [intros _; exact HL | exact HkL]|]. split; [intros _; exact HW|]. split; assumption.
  - split; [intros x Hx; exfalso; clear - Hx Nz; lia|]. split; [intros X; exfalso; clear - X Nz; lia|].
    split; [exists 0; split; [intros X; exfalso; clear - X Nz; lia | left; reflexivity]|]. split; [intros X; exfalso; clear - X Nz; lia|]. split; assumption.
Qed.

#[using="Hwx AFL HLsegs HLlo HLhi HLroimg HLstimg HLlsan PRIVZ PRIVF PRIVCS FRB FRB_rng RUNX"] Theorem art_wrap_copy : forall (R : bvmap 5 word) (M : word -> option byte) (model : Model)
    (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (dst src n : Z) (bs : list byte) (K : ShapeAlg.TSet),
  let sp := U (getr R 2) in
  RI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
  getr R 10 = Z_to_bv 64 dst -> getr R 12 = Z_to_bv 64 n -> 0 <= n <= 2 ^ 27 ->
  Hoare.ret_ok (getr R 1) ->
  astack_ok L (rn_ar rn) M 2560 sp ->
  aacc M dst n -> (forall i, 0 <= i < n -> aclientw L (rn_ar rn) LB FF sp 2560 (dst + i)) ->
  (forall i (m : nat), 0 <= i -> i + Z.of_nat m <= n -> store_ok ASEGS M (Z_to_bv 64 (dst + i)) m = true) ->
  K [] -> app_rng (rn_ar rn) dst n ->
  getr R 11 = Z_to_bv 64 src ->
  aacc M src n -> 0 <= src /\ src + n <= 2 ^ 47 -> app_rng (rn_ar rn) src n ->
  (forall i, 0 <= i < n -> hl_img_lo L <= src + i < hl_img_hi L \/ aclient L (rn_ar rn) LB FF sp 2560 (src + i)) ->
  rdn ASEGS M (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->
  (dst + n <= src \/ src + n <= dst) ->
  (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
      getr R' 10 = Z_to_bv 64 dst -> regs_preserved R R' ->
      (forall i, 0 <= i < n -> exists v, (nth_error bs (Z.to_nat i) = Some (Z_to_bv 8 v) /\ 0 <= v < 256) /\ byte_at M' (dst + i) v) ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L (rn_ar rn) LB FF sp 2560 a -> ~ (dst <= a < dst + n) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a, sp - 2560 <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
      model_rt model model' -> MInv A model' ->
      RI LB FF LK cr A M' (vml_of model') ->
      srealizes ASEGS scfg (mkCfg (mkst R' (getr R 1) M' (seg_rom ASEGS)) model') K) ->
  srealizes ASEGS scfg (mkCfg (mkst R pc0 M (seg_rom ASEGS)) model) K.
Proof.
  intros R M model LB FF LK cr A dst src n bs K sp INV Hhalt HMI H10 H12 Hn Hret AST AACC CLW DOK KT0 APPR H11 AACCS (Hs0 & Hs47) APPRS CLSS RDS NOV CONT.
  pose proof (proj1 APPR) as Hd0.
  destruct (art_ri_open MAPS0 RESV0 NOACC0 BASE BUDGET rn LB FF LK cr A M model INV Hhalt HMI) as (G & REPr & FS & B0 & CRED & CLI & KN & LZ & EG).
  set (Mr0 := mrestrict (bhid A model) M) in *.
  destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF). fold sp in S16, SHI, SLE, SWR, SDEF. rewrite HLsegs in SWR.
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
  change (2 ^ 27) with 134217728 in Hn.
  pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
  pose proof REPr as (ROK & STAT & _).
  assert (LAZY : forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
            0x696000 <= U w /\ U w < rn_HI rn /\ ~ in_block LB (U w) /\ ~ (ar_fs (rn_ar rn) <= U w < ar_fs (rn_ar rn) + FS_BYTES)).
  { intros w Hw. destruct LZ as (L1 & _). destruct (art_lazy_zone_bounds art_fsg rn G (U w) ROK (L1 w Hw)) as (B1 & B2).
    split; [lia|]. split; [exact (proj2 B1)|]. split; [|exact B2]. intros (b & Hb & Hr). rewrite (proj2 EG b w Hb Hr) in Hw. discriminate Hw. }
  assert (CLS : forall i, 0 <= i < n -> hl_img_lo L <= dst + i < hl_img_hi L \/ aclient L (rn_ar rn) LB FF sp 2560 (dst + i)).
  { intros i Hi. right. apply aclientw_client. exact (CLW i Hi). }
  assert (OFFW : forall p, (forall i, 0 <= i < n -> hl_img_lo L <= p + i < hl_img_hi L \/ aclient L (rn_ar rn) LB FF sp 2560 (p + i)) ->
                 0 < n -> p + n <= sp - FRB \/ sp <= p).
  { intros p CL Hn0. destruct (art_rng_off_window p n (sp - 2560) sp Hn0 ltac:(lia)) as [X | X]; [|left; clear - X FRB_rng; lia | right; exact X].
    intros i Hi. apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 2560 (p + i) ltac:(lia) (CL i Hi)). }
  assert (APPD : (dst + n <= BIGSHADOW_LO \/ BIGSHADOW_HI <= dst)) by exact (proj1 (proj2 APPR)).
  set (FP := fun x => sp - FRB <= x < sp \/ dst <= x < dst + n).
  pose proof (rdn_length _ _ _ _ _ RDS) as LEN.
  assert (LENZ : Z.of_nat (length bs) = n) by (rewrite LEN, Z2Nat.id by (clear - Hn; lia); reflexivity).
  destruct (art_rng_facts0 G LB FF LK A M model sp dst n LAZY CLI FS (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0) Hd0 ltac:(clear - Hn; lia) CLS AACC APPR)
    as (VISD & HZD & (kD & HLD & HkD) & HWD & HSHD & D47).
  destruct (art_rng_facts0 G LB FF LK A M model sp src n LAZY CLI FS (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0) Hs0 ltac:(clear - Hn; lia) CLSS AACCS APPRS)
    as (VISS & HZS & (kS & HLS & HkS) & HWS & HSHS & S47).
  apply (art_wrap_pure2 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx AFL K R pc0 M model G LB FF LK cr A FP
           (fun R' pc1 Mr' => pc1 = getr R 1 /\ getr R' 10 = Z_to_bv 64 dst /\ keeps_cs R R'
                              /\ (forall i, 0 <= i < n -> Mr' (Z_to_bv 64 (dst + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))))
           REPr FS B0 CRED CLI KN LZ EG).
  - (* [comment removed for export] *)
    assert (W0 : wrA Mr0 (sp - 2560) 2560).
    { apply (art_stack_wr art_fsg rn G A (m_vm_lazy model) M sp 2560 ROK LZ ltac:(lia) ltac:(lia) ltac:(lia)). exact SWR. }
    assert (HOK : store_ok ASEGS Mr0 (Z_to_bv 64 (sp - FRB)) (Z.to_nat FRB) = true).
    { replace (sp - FRB) with (sp - 2560 + (2560 - FRB)) by ring. apply W0; [clear - FRB_rng; lia | rewrite Z2Nat.id by (clear - FRB_rng; lia); clear - FRB_rng; lia]. }
    destruct STAT as (_ & LAY & _ & _ & _ & _ & _ & S8).
    assert (HGL : rt_layout_globs Mr0).
    { destruct LAY as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _). unfold rt_layout_globs. repeat split; [lit_cell A1 | lit_cell A2 | lit_cell A3 | lit_cell A4 | lit_cell A5 | lit_cell A6 | lit_cell A7 | lit_cell A8]. }
    assert (C1 : cellA Mr0 0x138028 8 0x140919) by conj_find S8.
    assert (C2 : cellA Mr0 0x140919 1 1) by conj_find S8.
    assert (C3 : cellA Mr0 0x1394c8 8 0x129900) by conj_find S8.
    assert (HIC : mc_icpt_globs Mr0).
    { unfold mc_icpt_globs. repeat split; [lit_cell C1 | rewrite <- le1_one; lit_cell C2 | lit_cell C3]. }
    assert (HDST : store_ok ASEGS Mr0 (Z_to_bv 64 dst) (Z.to_nat n) = true).
    { apply (art_rng_store_ok A M model dst (Z.to_nat n) Hd0 ltac:(rewrite Z2Nat.id by (clear - Hn; lia); clear - D47 Hn; lia)).
      - rewrite Z2Nat.id by (clear - Hn; lia). exact VISD.
      - pose proof (DOK 0 (Z.to_nat n) ltac:(lia) ltac:(rewrite Z2Nat.id by (clear - Hn; lia); lia)) as X. rewrite Z.add_0_r in X. exact X. }
    assert (HSRC : rdn ASEGS Mr0 (Z_to_bv 64 src) (Z.to_nat n) = Some bs).
    { apply (art_rng_rdn A M model src (Z.to_nat n) bs Hs0 ltac:(rewrite Z2Nat.id by (clear - Hn; lia); clear - S47 Hn; lia)); [|exact RDS].
      rewrite Z2Nat.id by (clear - Hn; lia). exact VISS. }
    assert (HSs : 0x1000000 <= sp - FRB /\ sp < 2 ^ 64) by (clear - SHI SLE STOP HI1 FRB_rng; lia).
    destruct (RUNX Mr0 (getr R 2) (getr R 1) dst src n sp bs kS _ _ kD _ _ eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(clear - Hn; lia)
                (art_rng_app8 rn LB FF LK A M CLI src n Hs0 ltac:(clear - Hn; lia) APPRS) (art_rng_app8 rn LB FF LK A M CLI dst n Hd0 ltac:(clear - Hn; lia) APPR)
                HSs ltac:(clear - HSHS SHI FRB_rng; lia) ltac:(clear - HSHD SHI FRB_rng; lia) (OFFW src CLSS) (OFFW dst CLS) NOV HOK HDST HSRC Hret HGL HIC
                HZS HLS HkS HWS HZD HLD HkD HWD R H10 H11 H12 eq_refl eq_refl)
      as (R' & Mf & Mj & RUN & Q10 & KCS & GRr & OA & PW).
    assert (FRr : forall x : word, ~ FP (U x) -> Mf x = Mr0 x).
    { intros x Hx. unfold FP in Hx. pose proof (u64_range x) as Rx. rewrite PW.
      assert (E1 : wbytes Mj (Z_to_bv 64 dst) bs x = Mj x).
      { destruct (Z_lt_le_dec (U x) dst) as [Lt | Ge].
        - apply wbytes_below; [rewrite LENZ, art_u_lit by (clear - Hd0 D47 Hn; lia); clear - D47 Hd0 Hn; lia | rewrite art_u_lit by (clear - Hd0 D47 Hn; lia); exact Lt].
        - apply wbytes_above. rewrite LENZ, art_u_lit by (clear - Hd0 D47 Hn; lia). clear - Hx Ge. lia. }
      rewrite E1. apply OA. clear - Hx. lia. }
    exists R', (getr R 1), Mf. split; [exact RUN|]. split; [exact GRr|]. split; [exact FRr|].
    split.
    { pose proof REPr as (_ & _ & (_ & _ & _ & _ & _ & _ & _ & CL) & _).
      assert (GEOL : 0x10000 <= rn_tp rn + rn_loff rn /\ rn_tp rn + rn_loff rn + 4 <= 0x696000).
      { pose proof ROK as ROK'. rok_open ROK'. geo_open GEO. clear - Hloff Hloff' Hloff'' Htpd G1 G2 Espb G4. lia. }
      apply (BatAllocG_b.cell_agree Mr0 Mf); [| clear - GEOL; lia | cbn; clear - GEOL; lia | exact CL].
      intros x Hx. cbn in Hx. apply FRr. unfold FP. intros [X | X]; [clear - X Hx GEOL SHI HI1 FRB_rng; lia|].
      apply (art_clientw_not_static rn LB FF LK A M CLI L (g_fs art_fsg G) FS HLstimg sp 2560 (U x)).
      - replace (U x) with (dst + (U x - dst)) by ring. apply CLW. clear - X. lia.
      - unfold BIGSHADOW_LO. left. clear - Hx GEOL. lia.
      - apply HLlsan. clear - Hx. lia. }
    split; [reflexivity|]. split; [exact Q10|]. split; [exact KCS|].
    intros i Hi. rewrite PW. rewrite (wbytes_inside _ Mj (Z_to_bv 64 dst) (Z_to_bv 64 (dst + i))).
    + rewrite !art_u_lit by (clear - Hd0 D47 Hi; lia). f_equal. f_equal. f_equal. ring.
    + rewrite LENZ, art_u_lit by (clear - Hd0 D47 Hn; lia). clear - D47 Hd0 Hn. lia.
    + rewrite LENZ, !art_u_lit by (clear - Hd0 D47 Hi; lia). clear - Hi. lia.
  - (* [comment removed for export] *)
    intros x [Hx | Hx] Z.
    + exfalso. pose proof (art_zone_below MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 (or_introl Z)). clear - H Hx SHI FRB_rng. lia.
    + destruct (in_block_dec LB x) as [IB | NB]; [exact IB | exfalso].
      apply (art_clientw_not_private rn LB FF LK A M CLI L (g_fs art_fsg G) FS HLroimg sp 2560 x).
      * replace x with (dst + (x - dst)) by ring. apply CLW. clear - Hx. lia.
      * unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - APPD Hx. lia.
      * exact (PRIVZ G LB FF LK A M Mr0 (m_vm_lazy model) REPr FS CLI (bi_live _ _ _ _ _ _ _ _ _ _ _ B0) KN LZ EG x Z NB).
  - (* [comment removed for export] *)
    intros x [Hx | Hx] Z3.
    + exfalso. pose proof (art_fs_zone3_below rn G LB _ x REPr Z3). clear - H Hx SHI FRB_rng. lia.
    + destruct (in_fframe_dec FF x) as [IB | NB]; [exact IB | exfalso].
      apply (art_clientw_not_private rn LB FF LK A M CLI L (g_fs art_fsg G) FS HLroimg sp 2560 x).
      * replace x with (dst + (x - dst)) by ring. apply CLW. clear - Hx. lia.
      * unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - APPD Hx. lia.
      * exact (PRIVF G LB FF LK A M Mr0 (m_vm_lazy model) REPr FS CLI (bi_live _ _ _ _ _ _ _ _ _ _ _ B0) KN LZ EG x Z3 NB).
  - (* [comment removed for export] *)
    intros x [Hx | Hx] Zc.
    + pose proof (art_cs_zone_below rn G LB FF LK M Mr0 x REPr FS Zc). clear - H Hx SHI FRB_rng. lia.
    + apply (art_clientw_not_private rn LB FF LK A M CLI L (g_fs art_fsg G) FS HLroimg sp 2560 x).
      * replace x with (dst + (x - dst)) by ring. apply CLW. clear - Hx. lia.
      * unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - APPD Hx. lia.
      * exact (PRIVCS G LB FF LK A M Mr0 (m_vm_lazy model) REPr FS CLI (bi_live _ _ _ _ _ _ _ _ _ _ _ B0) KN LZ EG x Zc).
  - (* [comment removed for export] *)
    intros b x Hb Hx [X | X].
    + pose proof (art_block_shadow_below rn LB FF LK A M b x CLI Hb Hx). clear - H X SHI HI1 FRB_rng. lia.
    + pose proof (art_block_shadow_below rn LB FF LK A M b x CLI Hb Hx) as B1. pose proof CLI as (CB & _). destruct (CB b Hb) as (K1 & _).
      unfold in_shadow_of in Hx. pose proof (art_S_lo (fst b) ltac:(clear - K1; lia)) as B2. unfold BIGSHADOW_LO, BIGSHADOW_HI in APPD. clear - APPD X B1 B2 Hx. lia.
  - (* [comment removed for export] *)
    intros R' pc1 Mr' M1 model' (Epc & Q10 & KCS & BYTES) RI' GROW FR1 VIS1 HID RT MI'. subst pc1.
    apply (CONT R' M1 model' Q10 (keeps_cs_preserved R R' KCS)); [ | | | exact RT | exact MI' | exact RI'].
    + intros i Hi. exists (U (nth (Z.to_nat i) bs (Z_to_bv 8 0))). split; [split|].
      * rewrite Z_to_bv_bv_unsigned. apply nth_error_nth'. rewrite LEN. clear - Hi. lia.
      * pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))) as Rg. unfold bv_modulus in Rg. change (2 ^ Z.of_N 8) with 256 in Rg. exact Rg.
      * unfold byte_at. rewrite Z_to_bv_bv_unsigned. rewrite (VIS1 _ (VISD (Z_to_bv 64 (dst + i)) ltac:(rewrite art_u_lit by (clear - Hd0 D47 Hi; lia); clear - Hi; lia))). exact (BYTES i Hi).
    + intros a Ra Ha ND. apply FR1. rewrite art_u_lit by exact Ra. unfold FP. intros [X | X]; [|exact (ND X)].
      apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 2560 a ltac:(clear - SHI; lia) (or_intror Ha)). clear - X FRB_rng. lia.
    + intros a Ha. apply GROW.
      assert (WM : wrA M (sp - 2560) 2560) by (intros d k Hd Hk; apply SWR; assumption).
      pose proof (art_wr_wview ASEGS M (sp - 2560) 2560 ltac:(clear - SHI HI1; lia) ltac:(clear - SLE STOP; lia) WM (Z_to_bv 64 a)) as V. rewrite art_u_lit in V by (clear - Ha SHI HI1 SLE STOP; lia). specialize (V ltac:(clear - Ha; lia)).
      rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Ha SHI HI1 SLE STOP; lia); right; clear - Ha SHI HI1; lia). exact V.
Qed.
End WCP.
