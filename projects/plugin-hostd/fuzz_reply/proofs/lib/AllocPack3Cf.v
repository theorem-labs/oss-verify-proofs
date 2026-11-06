(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YN03.v, with its module paths and module names changed; 426 of its 462 lines of code are new or changed and 500 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocCut.v, with its module paths and module names changed; 305 of its 381 lines of code are new or changed and 386 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YM06 YM06_cf YM05 YM02 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YO0i YO0f YO0g YO0q YO0x YO0d YO0e YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO04 YO16 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK1j YO10 YO0s YO0u YO15 YN03 YN2b YN33.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0d_cf YO03_cf YO0n_cf YH02 YN09 PlaceCap PlaceCapW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0o YO09 YL00 YL0g YI06 YI16 YI14 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocSI AllocGS AllocFree AllocMalloc AllocRealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocMB AllocMallocMB AllocFreeMB AllocReallocMB AllocSlots.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocMallocPath AllocFreePath AllocBound.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocPack AllocPackRoom AllocPackFree AllocReallocOK.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocPackMalloc AllocPackCut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Contract AllocCut AllocForm SlotAgree ZAllocator AllocCf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocPackGSF AllocPackGSFm AllocPackGSFr AllocPackMapB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocUnif AllocRoomW AllocReallocRoom AllocReallocCf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocPack3 AllocPack3Room AllocPack3Cut ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.Q Require Import YW02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.Q Require YT02_cf YT00_cf.
Import ListNotations.
Local Open Scope Z_scope.

(* The cut-free (crealizes) allocator contracts in the pack3 resource form: ContractT's rt contracts with
   SR -> SRcf and the room room_pack3 -> room_cf_pack3 (room_pack3, the run's peak under the budget, and the slot
   count under the placement policy's window cap).  The form carries GSF beside res_ok_pack3: the peak needs
   map_bytes <= MAPB + ubytes, which needs the small classes' group map lengths (GSF). *)

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Definition pack3_cf_formT : ResFormT := {|
  rt_R := pbound3; rt_ok := fun A b => res_ok_pack3 A b /\ GSF A; rt_room := room_pack3;
  rt_malloc := pb3_malloc; rt_free := pb3_free; rt_realloc := pb3_realloc |}.

Lemma pack3_cf_ok_pack3 : forall A b, rt_ok pack3_cf_formT A b -> res_ok_pack3 A b.
Proof. intros A b H. exact (proj1 H). Qed.

Lemma pack3_cf_ok_init : forall b, res_ok_pack3 init_state b -> rt_ok pack3_cf_formT init_state b.
Proof. intros b H. exact (conj H GSF_init). Qed.

(* The pack form's LIVE2c at the pack3 caps folded into one list (NF3 caps mc = NF (pk3_cm caps mc)). *)
Definition LIVE3c (caps mc : list Z) (bytes : Z) : Z := LIVE2c (pk3_cm caps mc) bytes.

Definition room_cf_pack3 (md : Model) (b : pbound3) (n : Z) : Prop :=
  room_pack3 b n /\ LIVE3c (p3_cap b) (p3_mcap b) (p3_bytes b + n) + NONHEAP_CF <= vm_limit (m_vmmaps md) /\
  SLOTS2 (GALL3 (p3_cap b) (p3_mcap b)) (GMAP3 (p3_cap b) (p3_mcap b)) + 5 + KRES <=
    slot_capW (RQ2 (GALL3 (p3_cap b) (p3_mcap b)) n + PGSZ).

(* AllocPackMapB.map_bytes_cf at the folded caps: PKC3 is PKC at pk3_cm, and the band-48 count comes from UPB3. *)
Theorem map_bytes_cf3 : forall s caps mc L M, WF s -> SI s -> GS s -> GSF s -> PKS [] s -> PKC3 [] caps mc s ->
  UPB3 s L M -> length caps = 49%nat -> length L = 49%nat -> (forall k, 0 <= k < 49 -> 0 <= znth k L <= znth k caps) ->
  map_bytes s <= MAPB (pk3_cm caps mc) + ubytes s.
Proof.
  intros s caps mc L M HW HS HG HF HP HC HU _ _ HB. apply PKC3_cm in HC.
  unfold map_bytes. rewrite rsum_idx.
  match goal with |- zsum ?c ?l <= _ => assert (Hl : zsum c l <= zsum (mb_w s) (pk_tgt s nestF)) end.
  { apply (ac_wsum pk_tdec (pk_RR s)).
    - apply seq_NoDup.
    - intros x Hx. unfold pk_tgt in Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_map_iff in Hx as (y & <- & Hy);
        unfold mb_w; cbn [fst snd].
      + destruct (mb_sw_small s nestF y Hy) as (c & Hc & ->). exact (mb_GLEN_nonneg c Hc).
      + unfold pk_ub48 in Hy. apply filter_In in Hy as [Hy _]. pose proof (ub_nonneg s HW y Hy). unfold PGSZ. lia.
    - intros k _. cbv beta.
      destruct (nth_error (st_regions s) k) as [rg|] eqn:Hr; cbv beta iota; [|left; lia].
      unfold f_mapb. destruct (rg_live rg && is_map rg) eqn:E; cbv beta iota; [right|left; lia].
      apply andb_true_iff in E as [Lv Mp].
      assert (Kd : rg_kind rg = RkMap) by (unfold is_map in Mp; destruct (rg_kind rg); try discriminate; reflexivity).
      pose proof HS as (OM & _). destruct (OM k rg Hr Kd Lv) as (g & ag & U & Mpos & Pk).
      pose proof (inv_groups HW g ag U) as (_ & _ & _ & _ & Gmp & _).
      destruct (Gmp Mpos) as (r & rg' & Em & Hr' & _ & _ & Len & _).
      rewrite Em in Pk. cbn in Pk. subst r. unfold region_of in Hr'. rewrite Hr in Hr'. injection Hr' as <-.
      rewrite Len.
      pose proof HP as (_ & _ & _ & P4).
      destruct (pk_tgt_ex s nestF g ag HW HP U (fun Hc => P4 g ag U (proj2 Hc) Mpos)) as (x & Hx & Rx).
      exists x. split; [exact Hx|]. split; [exists g, ag; split; [exact U|]; split; [rewrite Em; reflexivity | exact Rx]|].
      destruct Rx as (a & Ua & Hm). rewrite (usedX_fun _ _ _ _ _ Ua U) in Hm.
      destruct (HG g ag U Mpos) as [_ G63].
      unfold mb_w. destruct x as [p [n|]]; cbn [fst snd] in Hm |- *.
      + destruct Hm as (E63 & _ & fr & F & ->). pose proof (G63 E63 fr F). unfold PGSZ in *. lia.
      + destruct Hm as (Ep & C). subst p. unfold mb_sw.
        assert (EM : MTX [] s g = Some (MUsed ag)) by exact U. rewrite EM.
        exact (mb_glen s g ag HW HF HP U Mpos C).
    - intros k k' x _ _ (g & a & U & Pk & R1) (g' & a' & U' & Pk' & R2).
      pose proof (pk_RT_inj s g g' x R1 R2) as <-. rewrite (usedX_fun _ _ _ _ _ U U') in Pk. congruence. }
  pose proof (mb_wsum s (pk3_cm caps mc) HC) as Hw.
  assert (Hsub : zsum snd (pk_ub48 s) <= ubytes s).
  { change (ubytes s) with (zsum snd (user_blocks s)). unfold pk_ub48. apply pk_zsum_filter.
    intros b Hb. exact (ub_nonneg s HW b Hb). }
  pose proof (pk3_b48 s caps mc L M HU HB) as Hb.
  unfold MAPB. unfold PGSZ in *. lia.
Qed.

(* The memory a malloc call may hold at its peak, under the budget. *)
Lemma room_cf_pack3_peak : forall A b n md, WF A -> res_ok_pack3 A b -> GSF A -> room_cf_pack3 md b n ->
  LIVE_UB A + 3 * PGSZ + area A + Z.max MMAX (page_round (n + IB + UNIT)) <= vm_limit (m_vmmaps md).
Proof using.
  intros A b n md HW (HII & HSI & HGS & HNL & HNR & (MB1 & MB2) & HPK & HPC & HUP & HMS & Hub & HlL & HlC & HlM & Hbd & Hby & Hh) HG
    [(Hn & Hcap & Hmc & C1 & C2 & C3 & C4) [Hlim _]].
  assert (Hbd' : forall k, 0 <= k < 49 -> 0 <= znth k (p3_live b) <= znth k (p3_cap b)) by (intros k Hk; exact (proj1 (Hbd k Hk))).
  pose proof (map_bytes_cf3 A (p3_cap b) (p3_mcap b) (p3_live b) (p3_mis b) HW HSI HGS HG HPK HPC HUP HlC HlL Hbd') as T7.
  pose proof (nareas_hand A HII) as NA1.
  destruct (shift_small A (GALL3 (p3_cap b) (p3_mcap b)) HII Hh C4) as [SH1 SH2].
  pose proof HII as (_ & Hsh & _ & _ & Hrt & _).
  assert (HD : hand A / METAS_PER_AREA <= GALL3 (p3_cap b) (p3_mcap b) / METAS_PER_AREA).
  { apply Z.div_le_mono; [unfold METAS_PER_AREA; lia | exact Hh]. }
  assert (BK : brk_bytes A / PGSZ <= nareas A + 1).
  { apply Z.div_le_upper_bound; [unfold PGSZ; lia|]. unfold PGSZ in *. lia. }
  pose proof (page_round_ge (n + IB + UNIT)) as PR. pose proof (page_round_lt (n + IB + UNIT)) as PR'.
  assert (MX0 : 0 < MMAX) by (unfold MMAX; reflexivity).
  assert (AR : area A <= AREA2 (GALL3 (p3_cap b) (p3_mcap b))) by (unfold area, AREA2; unfold PGSZ in *; lia).
  unfold LIVE3c, LIVE2c, NONHEAP_CF in Hlim. rewrite <- GALL3_eq in Hlim. unfold RQ2, MG_REQ in C3.
  unfold LIVE_UB. rewrite Hrt. unfold AREA2, NA2 in *. unfold PGSZ, MMAX, IB, UNIT in *. lia.
Qed.

(* The slot count under the window cap: the instance's cap fact rides in room_cf_pack3 (its third conjunct). *)
Lemma pack3_slotW : forall A b n md, WF A -> res_ok_pack3 A b -> room_cf_pack3 md b n ->
  SLOT_UB A + 5 + KRES <= slot_capW (Z.max (Z.max MMAX (page_round (n + IB + UNIT) + PGSZ)) (area A)).
Proof.
  intros A b n md HW (HII & HSI & HGS & HNL & HNR & (MB1 & MB2) & HPK & HPC & HUP & HMS & Hub & HlL & HlC & HlM & Hbd & Hby & Hh)
    [(Hn & Hcap & Hmc & C1 & C2 & C3 & C4) [_ HW2]].
  assert (Hbd' : forall k, 0 <= k < 49 -> 0 <= znth k (p3_live b) <= znth k (p3_cap b)) by (intros k Hk; exact (proj1 (Hbd k Hk))).
  pose proof (mapped_pack3 A (p3_cap b) (p3_mcap b) (p3_live b) (p3_mis b) HW HSI HPK HPC HUP HlC HlL Hbd') as T4.
  pose proof (nareas_hand A HII) as NA1.
  destruct (shift_small A (GALL3 (p3_cap b) (p3_mcap b)) HII Hh C4) as [SH1 SH2].
  pose proof HII as (_ & Hsh & _ & _ & Hrt & _).
  assert (HD : hand A / METAS_PER_AREA <= GALL3 (p3_cap b) (p3_mcap b) / METAS_PER_AREA).
  { apply Z.div_le_mono; [unfold METAS_PER_AREA; lia | exact Hh]. }
  assert (BK : brk_bytes A / PGSZ <= nareas A + 1).
  { apply Z.div_le_upper_bound; [unfold PGSZ; lia|]. unfold PGSZ in *. lia. }
  pose proof (page_round_ge (n + IB + UNIT)) as PR.
  assert (MX0 : 0 < MMAX) by (unfold MMAX; reflexivity).
  assert (AR : area A <= AREA2 (GALL3 (p3_cap b) (p3_mcap b))) by (unfold area, AREA2; unfold PGSZ in *; lia).
  assert (SU : SLOT_UB A <= SLOTS2 (GALL3 (p3_cap b) (p3_mcap b)) (GMAP3 (p3_cap b) (p3_mcap b)))
    by (unfold SLOT_UB, SLOTS2, NA2; lia).
  assert (RQ : Z.max (Z.max MMAX (page_round (n + IB + UNIT) + PGSZ)) (area A) <= RQ2 (GALL3 (p3_cap b) (p3_mcap b)) n + PGSZ).
  { unfold RQ2. pose proof (Z.le_max_l (Z.max MMAX (page_round (n + IB + UNIT))) (AREA2 (GALL3 (p3_cap b) (p3_mcap b)))).
    pose proof (Z.le_max_r (Z.max MMAX (page_round (n + IB + UNIT))) (AREA2 (GALL3 (p3_cap b) (p3_mcap b)))).
    pose proof (Z.le_max_l MMAX (page_round (n + IB + UNIT))). pose proof (Z.le_max_r MMAX (page_round (n + IB + UNIT))).
    apply Z.max_lub; [apply Z.max_lub|]; unfold PGSZ in *; lia. }
  pose proof (slot_capW_anti (Z.max (Z.max MMAX (page_round (n + IB + UNIT) + PGSZ)) (area A))
    (RQ2 (GALL3 (p3_cap b) (p3_mcap b)) n + PGSZ) ltac:(lia)) as SC.
  lia.
Qed.

Section W.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition pack3_malloc_contract_cf : Prop :=
  forall L A regs mem md n b,
    call_pre B MR L A regs mem md -> ro_agree segs mem -> getr regs 10 = Z_to_bv 64 n ->
    rt_ok pack3_cf_formT A b -> room_cf_pack3 md b n ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md)
      (malloc_ret_rt B API pack3_cf_formT ALLOC_STACK L A regs mem md n b).

Definition pack3_free_contract_cf : Prop :=
  forall L A regs mem md p n b,
    call_pre B MR L A regs mem md -> ro_agree segs mem ->
    In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
    rt_ok pack3_cf_formT A b ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md',
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post B MR L A regs mem md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' regs' mem' md' /\
         (exists b1 b2, blocks L A = b1 ++ (ptr_addr L p, n) :: b2 /\ blocks L' A' = b1 ++ b2) /\
         blocks_kept B L A mem mem' (fun a => a = ptr_addr L p) /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         (forall q k, In (q, k) (user_blocks A) -> q <> p -> In (q, k) (user_blocks A')) /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         rt_ok pack3_cf_formT A' (rt_free pack3_cf_formT b n p)).

(* free (NULL) touches no allocator state: the form-independent contract. *)
Definition pack3_free_null_contract_cf : Prop := free_null_contract_cf B.

(* ContractT.realloc_contract_rt's post, with the new block's resource fact as a predicate of the block. *)
Definition realloc_post_rtcf (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (p : sptr) (k n : Z) (old : list byte) (P : sptr -> astate -> Prop) (c' : config) : Prop :=
  exists L' A' regs' mem' md' res,
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    call_post_k B MR REALLOC_STACK L A regs mem md (fun a => ptr_addr L p <= a < ptr_addr L p + k) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 res /\ res <> 0 /\ res mod 16 = 0 /\ fresh_block B res n /\
    (exists b1 b2 c1 c2, blocks L A = b1 ++ (ptr_addr L p, k) :: b2 /\ blocks L' A' = c1 ++ (res, n) :: c2 /\
       c1 ++ c2 = b1 ++ b2) /\
    blocks_kept B L A mem mem' (fun a => a = ptr_addr L p) /\
    ro_agree segs mem' /\ guard_kept B mem mem' /\
    (forall q k', In (q, k') (user_blocks A) -> q <> p -> In (q, k') (user_blocks A')) /\
    (forall i, 0 <= i < Z.min k n -> mbyte segs mem' (res + i) = nth_error old (Z.to_nat i)) /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    exists q, In (q, n) (user_blocks A') /\ ptr_addr L' q = res /\ P q A'.

Definition pack3_realloc_contract_cf (pc : Z) : Prop :=
  forall L A regs mem md p k n old b,
    call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem -> In (p, k) (user_blocks A) ->
    getr regs 10 = Z_to_bv 64 (ptr_addr L p) -> getr regs 11 = Z_to_bv 64 n ->
    (forall i, 0 <= i < k -> mbyte segs mem (ptr_addr L p + i) = nth_error old (Z.to_nat i)) ->
    Z.of_nat (length old) = k ->
    rt_ok pack3_cf_formT A b -> room_cf_pack3 md b n ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (realloc_post_rtcf L A regs mem md p k n old
         (fun q A' => rt_ok pack3_cf_formT A' (rt_realloc pack3_cf_formT b k n p q))).

Definition pack3_realloc_null_contract_cf (pc : Z) : Prop :=
  forall L A regs mem md n b,
    call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 <> Z_to_bv 64 (ms_malloc B) ->
    rt_ok pack3_cf_formT A b -> room_cf_pack3 md b n ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (malloc_ret_rt B API pack3_cf_formT REALLOC_STACK L A regs mem md n b).

(* AllocReallocCf.realloc_post_of_leaf with the returned block named. *)
Lemma realloc_rtcf_of_leaf : AllocExtra B MR -> ro_apart_b B = true ->
  forall L A regs mem md p k n old tr q A' c' (P : sptr -> astate -> Prop),
  call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem -> In (p, k) (user_blocks A) ->
  0 <= n ->
  (forall i, 0 <= i < k -> mbyte segs mem (ptr_addr L p + i) = nth_error old (Z.to_nat i)) ->
  cpath04 (realloc (Some p) n A) tr (Some q, A') ->
  realloc_leaf B MR L A regs mem md p k n (Some q, A') c' -> P q A' ->
  realloc_post_rtcf L A regs mem md p k n old P c'.
Proof using.
intros AX HB L A regs mem md p k n old tr q A' c' P Hpre Hro Hin Hn0 Hold Hp HL HP.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof Hpre as (HMR0 & _ & _ & _ & _ & Hsp & _).
destruct HL as (L' & regs' & mem' & md' & -> & Hpost & HM). cbn [fst snd] in *.
destruct HM as (Ha0 & Hnz & (l1 & l2 & m1 & m2 & E1 & E3 & E2) & Hcp).
assert (Hin' : In (q, n) (user_blocks A')) by (rewrite E2; apply in_app_iff; right; left; reflexivity).
assert (Hsub : forall q0 k0, In (q0, k0) (user_blocks A) -> q0 <> p -> In (q0, k0) (user_blocks A')).
{ intros q0 k0 Hq Hne. rewrite E1 in Hq. rewrite E2.
  assert (H12 : In (q0, k0) (l1 ++ l2)).
  { apply in_app_iff in Hq as [Hq|[Hq|Hq]]; apply in_app_iff;
    [left; exact Hq | injection Hq as -> _; exfalso; exact (Hne eq_refl) | right; exact Hq]. }
  rewrite <- E3 in H12. apply in_app_iff in H12 as [H12|H12]; apply in_app_iff; [left; exact H12 | right; right; exact H12]. }
pose proof Hpost as (HMR & HW' & _ & _ & Hstab & _ & _ & _ & Hkeep & _).
exists L', A', regs', mem', md', (ptr_addr L' q).
split; [reflexivity|]. split; [exact Hpost|]. split; [exact Ha0|]. split; [exact Hnz|].
split; [exact (mr_blocks_aligned B MR (aa_laws API) _ _ _ _ _ _ HMR Hin')|].
split.
{ destruct (mr_blocks_range B MR (aa_laws API) _ _ _ _ _ _ HMR Hin') as [R1 R2].
split; [exact R1|]. split; [exact R2|]. intros i Hi. exact (ax_blocks_img AX _ _ _ _ _ _ i HMR Hin' Hi). }
split; [exact (blocks_repl L L' A A' p k q n l1 l2 m1 m2 Hstab E1 E3 E2)|].
split.
{ apply (kept_of_post B L A A' mem mem'); [exact Hkeep|]. intros q0 k0 Hq Hg. apply Hsub; [exact Hq|]. intros ->. exact (Hg eq_refl). }
split; [exact (ro_agree_post B MR REALLOC_STACK L A regs mem md _ L' A' regs' mem' md' AX HB Hsp HMR0
(fun a Ha => ex_intro _ p (ex_intro _ k (conj Hin Ha))) Hpost Hro)|].
split; [exact (guard_kept_post B MR L A mem md L' A' mem' md' AX HMR0 HMR)|].
split; [exact Hsub|].
split; [intros i Hi; rewrite Hcp by lia; apply Hold; lia|].
split; [exact (YI04.init_done_of_block A' (q, n) HW' Hin')|].
split; [exact (regions_grow_realloc A p k n tr (Some q) A' HW Hin Hn0 Hp)|].
exists q. split; [exact Hin'|]. split; [reflexivity | exact HP].
Qed.

Theorem pack3_malloc_contract_cf_ok : AllocExtra B MR -> ro_apart_b B = true -> malloc_realizes_cf B MR ->
  pack3_malloc_contract_cf.
Proof using.
intros AX HB HMcf L A regs mem md n b Hpre Hro Hn [HR HG] HRc T HK.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof HRc as [HRm _].
pose proof (room_pack3_n b n HRm) as [Hn62 _].
assert (Hn0 : 0 <= n) by lia.
pose proof (pack3_room4 A b n HW HR HRm) as R4.
assert (Hroom : roomcf (vm_limit (m_vmmaps md)) (malloc n A)).
{ apply roomcf_malloc; [apply malloc_reqs_ok; [exact HW | exact Hn0] | exact (proj1 HR) | exact Hn0 | exact R4 |
    exact (room_cf_pack3_peak A b n md HW HR HG HRc) |].
  intros _. exact (slotW_malloc A n (pack3_slotW A b n md HW HR HRc)). }
pose proof (OK4_malloc n A (malloc_reqs_ok A n HW Hn0) (proj1 HR) Hn0 R4) as [HOK _].
refine (mreal_cf_SRcf B (malloc n A) _ _ (HMcf L A regs mem md n Hpre Hn Hn62)
  (malloc_safe A n HW Hn0) HOK Hroom T _). intros c' Hc'. apply HK. clear HK T.
destruct Hc' as ([r A'] & tr & Hp & HL).
destruct (malloc_pack3_step A b n tr r A' HW HR HRm Hp) as [[p ->] HRA'].
pose proof (malloc_GSF A n tr (Some p) A' HW HG Hn0 (cpath04_yields _ _ _ Hp)) as HG'.
destruct HL as (L' & regs' & mem' & md' & -> & Hpost & Ha0 & Hnz & (l1 & l2 & E1 & E2) & _).
pose proof Hpre as (HMR0 & _ & _ & _ & _ & Hsp & _).
cbn [fst snd] in *.
assert (Hin : In (p, n) (user_blocks A')) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
assert (Hsub : forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')).
{ intros q k Hq. rewrite E2 in Hq. rewrite E1. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff;
[left; exact Hq | right; right; exact Hq]. }
pose proof Hpost as (HMR & HW' & _ & _ & Hstab & _ & _ & _ & Hkeep & _).
pose proof (proj1 (call_post_k_alloc B MR L A regs mem md _ L' A' regs' mem' md') Hpost) as Hpk.
unfold malloc_ret_rt. exists L', A', regs', mem', md', (ptr_addr L' p).
split; [reflexivity|].
split; [exact Hpk|].
split; [exact Ha0|]. split; [exact Hnz|].
split; [exact (mr_blocks_aligned B MR (aa_laws API) _ _ _ _ _ _ HMR Hin)|].
split.
{ destruct (mr_blocks_range B MR (aa_laws API) _ _ _ _ _ _ HMR Hin) as [R1 R2].
split; [exact R1|]. split; [exact R2|]. intros i Hi. exact (ax_blocks_img AX _ _ _ _ _ _ i HMR Hin Hi). }
split; [exact (blocks_add L L' A A' p n l1 l2 Hstab E1 E2)|].
split; [apply (kept_of_post B L A A' mem mem'); [exact Hkeep | intros q k Hq _; exact (Hsub q k Hq)]|].
split; [exact (ro_agree_post B MR ALLOC_STACK L A regs mem md _ L' A' regs' mem' md' AX HB Hsp HMR0
(fun a (F : False) => match F with end) Hpk Hro)|].
split; [exact (guard_kept_post B MR L A mem md L' A' mem' md' AX HMR0 HMR)|].
split; [exact Hsub|].
split; [exact (YI04.init_done_of_block A' (p, n) HW' Hin)|].
split; [exact (regions_grow_malloc A n tr (Some p) A' HW Hn0 Hp)|].
exact (conj HRA' HG').
Qed.

Theorem pack3_free_contract_cf_ok : AllocExtra B MR -> ro_apart_b B = true -> free_realizes_cf B MR ->
  pack3_free_contract_cf.
Proof using.
intros AX HB HFcf L A regs mem md p n b Hpre Hro Hin Hp [HR HG] T HK.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof (free_reqs_ok A p n HW Hin) as RQ.
pose proof (OK4_free (Some p) A RQ (proj1 HR)) as [HOK _].
refine (mreal_cf_SRcf B (free (Some p) A) _ _ (HFcf L A regs mem md p n Hpre Hin Hp)
  (free_safe A p n HW Hin) HOK (r_free (Some p) (vml (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)) A) T _).
intros c' Hc'. apply HK. clear HK T.
destruct Hc' as ([[] A'] & tr & Hcp & HL).
pose proof (free_pack3_step A b p n tr tt A' HW Hin HR Hcp) as HRA'.
pose proof (free_GSF A p tr A' HG (cpath04_yields _ _ _ Hcp)) as HG'.
destruct HL as (L' & regs' & mem' & md' & -> & Hpost & (l1 & l2 & E1 & E2)).
pose proof Hpre as (HMR0 & _ & _ & _ & _ & Hsp & _).
cbn [fst snd] in *.
assert (Hsub : forall q k, In (q, k) (user_blocks A) -> q <> p -> In (q, k) (user_blocks A')).
{ intros q k Hq Hne. rewrite E1 in Hq. rewrite E2. apply in_app_iff in Hq as [Hq|[Hq|Hq]]; apply in_app_iff;
[left; exact Hq | injection Hq as -> _; exfalso; exact (Hne eq_refl) | right; exact Hq]. }
pose proof Hpost as (HMR & _ & _ & _ & Hstab & _ & _ & _ & Hkeep & _).
pose proof (proj1 (call_post_k_alloc B MR L A regs mem md _ L' A' regs' mem' md') Hpost) as Hpk.
exists L', A', regs', mem', md'. split; [reflexivity|]. split; [exact Hpost|].
split; [exact (blocks_del L L' A A' p n l1 l2 Hstab E1 E2)|].
split.
{ apply (kept_of_post B L A A' mem mem'); [exact Hkeep|]. intros q k Hq Hg. apply Hsub; [exact Hq|]. intros ->. exact (Hg eq_refl). }
split; [exact (ro_agree_post B MR ALLOC_STACK L A regs mem md _ L' A' regs' mem' md' AX HB Hsp HMR0
(fun a Ha => ex_intro _ p (ex_intro _ n (conj Hin Ha))) Hpk Hro)|].
split; [exact (guard_kept_post B MR L A mem md L' A' mem' md' AX HMR0 HMR)|].
split; [exact Hsub|].
split; [intros Hd; exact (free_keeps_init_done (Some p) A tr tt A' Hd (cpath04_yields _ _ _ Hcp))|].
split; [exact (regions_grow_free A p n tr A' HW Hin Hcp)|].
exact (conj HRA' HG').
Qed.

Theorem pack3_realloc_contract_cf_ok : AllocExtra B MR -> ro_apart_b B = true -> realloc_realizes_cf B MR ->
  realloc_safe_p -> forall pc, ms_realloc B = Some pc -> pack3_realloc_contract_cf pc.
Proof using.
intros AX HB HRr HS pc Hpc L A regs mem md p k n old b Hpre Hro Hin H10 H11 Hold Hlen [HR HG] HRc T HK.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof HRc as [HRm _].
pose proof (room_pack3_n b n HRm) as [Hn Ov].
assert (Hroom : roomcf (vm_limit (m_vmmaps md)) (realloc (Some p) n A)).
{ apply (roomcf_realloc A p k n _ HW Hin (proj1 HR) Hn (pack3_room4 A b n HW HR HRm) (room_pack3_req b n HRm)).
  - exact (room_cf_pack3_peak A b n md HW HR HG HRc).
  - intros _. exact (pack3_slotW A b n md HW HR HRc). }
refine (mreal_cf_SRcf B (realloc (Some p) n A) _ _ (HRr pc L A regs mem md p k n Hpc Hpre Hin H10 H11 Hn)
  (HS A p k n HW Hin Hn) (realloc_pack3_ok04 A b p k n HW Hin HR HRm) Hroom T _).
intros c' Hc'. apply HK. clear HK T.
destruct Hc' as ([r A'] & tr & Hp & HL).
destruct (realloc_pack3_step A b p k n tr r A' HW Hin HR HRm Hp) as (q & -> & HRA').
pose proof (realloc_GSF A p k n tr (Some q) A' HW Hin HG (proj1 Hn) (cpath04_yields _ _ _ Hp)) as HG'.
exact (realloc_rtcf_of_leaf AX HB L A regs mem md p k n old tr q A' c'
  (fun q0 A0 => rt_ok pack3_cf_formT A0 (rt_realloc pack3_cf_formT b k n p q0))
  Hpre Hro Hin (proj1 Hn) Hold Hp HL (conj HRA' HG')).
Qed.

Theorem pack3_realloc_null_contract_cf_ok : AllocExtra B MR -> ro_apart_b B = true -> realloc_null_realizes_cf B MR ->
  forall pc, ms_realloc B = Some pc -> pack3_realloc_null_contract_cf pc.
Proof using.
intros AX HB HRz pc Hpc L A regs mem md n b Hpre Hro H10 H11 Hra [HR HG] HRc T HK.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
pose proof HRc as [HRm _].
pose proof (room_pack3_n b n HRm) as [Hn Ov].
assert (Hn0 : 0 <= n) by lia.
pose proof (pack3_room4 A b n HW HR HRm) as R4.
assert (Hroom : roomcf (vm_limit (m_vmmaps md)) (realloc None n A)).
{ apply (roomcf_realloc_null A n _ HW (proj1 HR) Hn R4).
  - exact (room_cf_pack3_peak A b n md HW HR HG HRc).
  - intros _. exact (slotW_malloc A n (pack3_slotW A b n md HW HR HRc)). }
pose proof (OK4_malloc n A (malloc_reqs_ok A n HW Hn0) (proj1 HR) Hn0 R4) as [HOK _].
refine (mreal_cf_SRcf B (realloc None n A) _ _ (HRz pc L A regs mem md n Hpc Hpre H10 H11 Hn Hra)
  (malloc_safe A n HW Hn0) HOK Hroom T _).
intros c' Hc'. apply HK. clear HK T.
destruct Hc' as ([r A'] & tr & Hp & HL).
change (realloc None n A) with (malloc n A) in Hp.
destruct (malloc_pack3_step A b n tr r A' HW HR HRm Hp) as [[q ->] HRA'].
pose proof (malloc_GSF A n tr (Some q) A' HW HG Hn0 (cpath04_yields _ _ _ Hp)) as HG'.
destruct (malloc_ret_of_null_leaf B API AX HB L A regs mem md n tr q A' c'
  (fun A1 => rt_ok pack3_cf_formT A1 (rt_malloc pack3_cf_formT b n)) Hpre Hro Hn0 Hp HL (conj HRA' HG'))
  as (L' & regs' & mem' & md' & res & Hall).
unfold malloc_ret_rt. exists L', A', regs', mem', md', res. exact Hall.
Qed.

End W.

Theorem zlib_pack3_malloc_contract_cf {LS : lib_shape} {SH : sink_head} {SK : sink_syms} :
  pack3_malloc_contract_cf src0_msyms zlib_API.
Proof using.
  exact (pack3_malloc_contract_cf_ok src0_msyms zlib_API zlib_allocator_extra ltac:(vm_compute; reflexivity)
    src0_malloc_realizes_cf).
Qed.

Theorem zlib_pack3_free_contract_cf {LS : lib_shape} {SH : sink_head} {SK : sink_syms} :
  pack3_free_contract_cf src0_msyms zlib_API.
Proof using.
  exact (pack3_free_contract_cf_ok src0_msyms zlib_API zlib_allocator_extra ltac:(vm_compute; reflexivity)
    src0_free_realizes_cf).
Qed.

Theorem zlib_pack3_free_null_contract_cf : pack3_free_null_contract_cf src0_msyms.
Proof using. exact src0_free_null_cf. Qed.

Theorem zlib_pack3_realloc_contract_cf {LS : lib_shape} {SH : sink_head} {SK : sink_syms} :
  forall pc, ms_realloc src0_msyms = Some pc -> pack3_realloc_contract_cf src0_msyms zlib_API pc.
Proof using.
  exact (pack3_realloc_contract_cf_ok src0_msyms zlib_API zlib_allocator_extra ltac:(vm_compute; reflexivity)
    (@YT02_cf.src0_realloc_realizes fx rc) realloc_safe).
Qed.

Theorem zlib_pack3_realloc_null_contract_cf {LS : lib_shape} {SH : sink_head} {SK : sink_syms} :
  forall pc, ms_realloc src0_msyms = Some pc -> pack3_realloc_null_contract_cf src0_msyms zlib_API pc.
Proof using.
  exact (pack3_realloc_null_contract_cf_ok src0_msyms zlib_API zlib_allocator_extra ltac:(vm_compute; reflexivity)
    (@YT00_cf.src0_realloc_null_realizes fx rc)).
Qed.

End A.
