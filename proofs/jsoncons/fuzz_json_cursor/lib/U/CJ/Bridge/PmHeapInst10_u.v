(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.

From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatSim StoreOk Scfg ShapeAlg SpinAlg Hoare AgentLib MmapSim AllocSim RefNodes HeapIface.

From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import RunP MState Mem Cells Step Frame Exec ITree Nodes Decode Image Tac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import Prelim STree Malloc MallocCtrl Monad Prog KInv KStep MI_Kit MI_Inv MI_Sim MI_Ledger MI_Contracts.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Agent Require Import MallocHINV_u MallocBlocks_u Malloc_iface_u MallocFacts_A_u MallocFacts_inv2_u F_free_u F_free_spec_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Pm10 Require Import F_syscalls_u RMallocRep_u RMallocTree_u RMalloc_iface_u RMalloc_ifaceP_u RF_malloc_top_u RF_malloc_spec_u RF_free_spec_u RF_aligned_u RF_aligned_spec_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Bridge Require Import BrRegs BrBase BrXfer BrMem KLink BrRes Embed.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Definition KPM : Z := Z.of_nat EVM.
Definition NCMAX : Z := 1000.
Definition K0 : Z := KPM * NCMAX.
Definition POTMAX : Z := POT0 + AMC * NCMAX.
Definition LNMAX : Z := (2 * PGSZ * (POTMAX + AMC)) / NSLOTS.
Definition BOV : Z := GMAX + IB + UNIT + PGSZ + LNMAX + 2 * PGSZ.

Definition B0 : Z := 2^33.
Definition NSEG : Z := 4.
Definition IMG_LO : Z := 0x10000.
Definition IMG_HI : Z := 0xf8000.
Definition RESV : list (word * word) := segments_reserved rsegs.

Lemma RESV_eq : RESV = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x29000); (Z_to_bv 64 0x39000, Z_to_bv 64 0x84000);
                        (Z_to_bv 64 0xbd000, Z_to_bv 64 0x7000); (Z_to_bv 64 0xc4000, Z_to_bv 64 0x34000)].
Proof. vmc_refl. Qed.

Lemma CALLB_le : forall n PA, 0 <= n -> PA <= POTMAX + AMC -> 0 <= CALLB n PA <= n + BOV.
Proof.
  intros n PA Hn HPA. unfold CALLB, BOV, LNMAX.
  pose proof (mmap_len_ge (n + IB + UNIT) ltac:(unfold IB, UNIT; lia)) as H1. unfold mmap_len in H1. rewrite <- round_up_pg_eq in H1.
  assert (2 * PGSZ * PA / NSLOTS <= 2 * PGSZ * (POTMAX + AMC) / NSLOTS).
  { apply Z.div_le_mono; [reflexivity|]. unfold PGSZ. lia. }
  assert (0 <= 2 * PGSZ * (POTMAX + AMC) / NSLOTS) by (apply Z.div_pos; [unfold PGSZ, POTMAX, POT0, AMC, NCMAX, NSLOTS; lia| reflexivity]).
  unfold GMAX, IB, UNIT, PGSZ in *. lia.
Qed.

Section LAYOUT.
Variable sptop : Z.

Definition L0 : heap_layout := {|
  hl_segs := rsegs;
  hl_malloc := RMALLOC_SYM;
  hl_free := RFREE_SYM;
  hl_aligned_alloc := RAA_SYM;
  hl_tp := RATP;
  hl_errno := RERRNO;
  hl_img_lo := IMG_LO;
  hl_img_hi := IMG_HI;
  hl_alloc_static := fun a => RMLOCK <= a < RCTX + 928;
  hl_alloc_ro := fun a =>
       (IMG_LO <= a < 0xbd000)
    \/ (RLIBC <= a < RMLOCK)
    \/ (RCTX + 928 <= a < RCTX + 936)
    \/ (RGOT_SSP <= a < RGOT_SSP + 8)
    \/ (RSSP_GUARD <= a < RSSP_GUARD + 8)
    \/ (RVMLOCK <= a < RVMLOCK + 4)
    \/ (sptop <= a);
  hl_stack := RALIGNED_STACK;
  hl_sptop := sptop;
  hl_k_per_malloc := KPM;
  hl_b_overhead := BOV;
  hl_K0 := K0;
  hl_B0 := B0 |}.

Definition blk_iv (b : block) : Z * Z := (blk_addr b, blk_size b).

Definition hi_heap0 (LB : list (Z * Z)) (cr : credit) (M : word -> option byte) (VM : VmMaps) : Prop :=
  exists (RUNp : RunP) (s : PState) (L : mled) (LBb : list block) (ncalls : Z),
       alloc_ceiling = sptop - 2 ^ 23
    /\ LB = map blk_iv LBb
    /\ RHEAP s LBb M
    /\ creach (ps_m s) L
    /\ Permutation (ld_live L) (map blk_slot LBb)
    /\ KL2 RESV IMG_HI L (ps_brk s) VM
    /\ mem_inv rsegs M
    /\ rauxv_ok M sptop
    /\ (forall a : word, RCTX + 928 <= bv_unsigned a < RCTX + 936 -> M a = None)
    /\ Forall (fun b => 0 < blk_size b /\ forall i, 0 <= i < blk_size b -> M (wa (blk_addr b + i)) <> None) LBb

    /\ 0 <= ncalls /\ KPM * ncalls + fst cr <= K0 /\ 0 <= fst cr /\ 0 <= snd cr
    /\ pot (ps_m s) <= POT0 + AMC * ncalls
    /\ Z.of_nat (length (vm_reserved VM ++ vm_maps VM)) + fst cr <= K0 + NSEG
    /\ Forall (fun p => bv_unsigned (snd p) <= NMAX) (vm_reserved VM ++ vm_maps VM)
    /\ live_bytes (vm_maps VM) + snd cr <= B0.

Definition HI0 : heap_iface := {| hi_heap := hi_heap0 |}.

Definition init_statics0 (M : word -> option byte) : Prop :=
     (forall a : word, 0xf6c08 <= bv_unsigned a < 0xf73f8 -> M a = None)
  /\ rw_cells rsegs M 0xf6a93 [C1 (Z_to_bv 8 0)]
  /\ rw_cells rsegs M 0xf6ac0 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells rsegs M 0xc3a48 [C8 (Z_to_bv 64 0xf6a70)]
  /\ (exists canary : Z, 0 <= canary < 2 ^ 64 /\ rw_cells rsegs M 0xf6a70 [C8 (Z_to_bv 64 canary)])
  /\ (exists (av x3 x4 x5 hw x6 x11 x12 x23 rnd secret : Z),
         rw_cells rsegs M 0xf6a98 [C8 (Z_to_bv 64 av)]
      /\ bytes_at rsegs M av (u64s (map (Z_to_bv 64) [3; x3; 4; x4; 5; x5; 16; hw; 6; x6; 11; x11; 12; x12; 23; x23; 25; rnd; 0; 0]))
      /\ bytes_at rsegs M (rnd + 8) (le8 (Z_to_bv 64 secret))
      /\ sptop <= av /\ av + 160 <= 2 ^ 64 /\ sptop <= rnd + 8 /\ rnd + 16 <= 2 ^ 64
      /\ 0 <= x3 < 2 ^ 64 /\ 0 <= x4 < 2 ^ 64 /\ 0 <= x5 < 2 ^ 64 /\ 0 <= hw < 2 ^ 64 /\ 0 <= x6 < 2 ^ 64
      /\ 0 <= x11 < 2 ^ 64 /\ 0 <= x12 < 2 ^ 64 /\ 0 <= x23 < 2 ^ 64 /\ 0 <= rnd < 2 ^ 64 /\ 0 <= secret < 2 ^ 64)
  /\ mem_inv rsegs M.

Section INST.
Context {RUNp : RunP}.
Hypothesis HCEIL : alloc_ceiling = sptop - 2 ^ 23.

Lemma stack_ok_stk : forall M sp, stack_ok (L0) M sp ->
  stk rsegs M (sp - RALIGNED_STACK) sp /\ alloc_ceiling <= sp - RALIGNED_STACK /\ sp <= sptop /\ 0 <= sp < 2^63.
Proof.
  intros M sp (Hal & Hlo & Hhi & Htop & Hst). cbn [hl_stack hl_sptop hl_segs L0] in *.
  rewrite HCEIL. unfold RALIGNED_STACK, RMALLOC_STACK in *.
  split; [| lia]. split; [lia|]. split; [lia|].
  intros a Ha.
  assert (Hwa : bv_unsigned (wa a) = a) by (unfold wa; apply u64_lit; lia).
  pose proof (Hst (a - (sp - (8192 + 32))) 1%nat ltac:(lia) ltac:(cbn; lia)) as S1.
  replace (sp - (8192 + 32) + (a - (sp - (8192 + 32)))) with a in S1 by lia.
  pose proof (store_ok_all rsegs M 1 (wa a) ltac:(rewrite Hwa; cbn; lia) S1 (wa a) ltac:(rewrite Hwa; cbn; lia)) as W.
  split; [exact W|].
  rewrite ref_wview_overlay in W by (rewrite Hwa; lia). rewrite ref_mrd_overlay by (rewrite Hwa; lia).
  destruct (M (wa a)) as [b|]; [exists b; reflexivity| congruence].
Qed.

Lemma block_ge_4096 : forall s LBb M b,
  RHEAP s LBb M -> In b LBb -> 4096 <= blk_addr b.
Proof.
  intros s LBb M b (st & LB0 & HP & Hst & MR & [HI1 AR]) Hin.
  pose proof (areach_facts_proof _ _ AR) as MF.
  assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hin]).
  destruct (rblock_inside st LB0 M b MF MR IN0) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
  lia.
Qed.

Lemma NoDup_map_transfer : forall {A B C} (f : A -> B) (g : A -> C) (l : list A),
  List.NoDup (map f l) -> (forall x y, In x l -> In y l -> f x <> f y -> g x <> g y) -> List.NoDup (map g l).
Proof.
  intros A B C f g l. induction l as [|a l IH]; intros Hnd Hfg; cbn in *; [constructor|].
  inversion Hnd as [|? ? Hni Hnd']; subst. constructor.
  - intros Hin. apply in_map_iff in Hin as (y & Ey & Hy).
    apply (Hfg a y (or_introl eq_refl) (or_intror Hy)); [| symmetry; exact Ey].
    intros Ef. apply Hni. rewrite Ef. apply in_map. exact Hy.
  - apply IH; [exact Hnd'|]. intros x y Hx Hy. apply Hfg; right; assumption.
Qed.

Lemma lb_remove_filter : forall A n LB, List.NoDup (map fst LB) -> In (A, n) LB ->
  HeapIface.lb_remove A LB = List.filter (fun b => negb (fst b =? A)) LB.
Proof.
  intros A n LB. induction LB as [|b LB IH]; intros Hnd Hin; [destruct Hin|]. cbn.
  cbn in Hnd. inversion Hnd as [|? ? Hni Hnd']; subst.
  destruct (Z.eqb_spec (fst b) A) as [E|NE]; cbn [negb].
  - symmetry. apply List.forallb_filter_id. apply forallb_forall. intros x Hx.
    destruct (Z.eqb_spec (fst x) A) as [Ex|Nx]; [|reflexivity]. exfalso. apply Hni. rewrite E, <- Ex. apply in_map. exact Hx.
  - f_equal. apply IH; [exact Hnd'|]. destruct Hin as [->|Hin]; [cbn in NE; congruence| exact Hin].
Qed.

Lemma hi0_nodup_addr : forall s LBb M,
  RHEAP s LBb M -> Forall (fun b => 0 < blk_size b /\ forall i, 0 <= i < blk_size b -> M (wa (blk_addr b + i)) <> None) LBb ->
  List.NoDup (map blk_addr LBb).
Proof.
  intros s LBb M HR BLK. apply (NoDup_map_transfer blk_id blk_addr LBb (RHEAP_blocks_nodup_proof s LBb M HR)).
  intros x y Hx Hy Hne Ea.
  pose proof (RHEAP_blocks_disjoint_proof s LBb M x y HR Hx Hy Hne) as D.
  pose proof (proj1 (List.Forall_forall _ _) BLK x Hx) as [Sx _]. pose proof (proj1 (List.Forall_forall _ _) BLK y Hy) as [Sy _]. lia.
Qed.

Lemma map_fst_blk_iv : forall LBb, map fst (map blk_iv LBb) = map blk_addr LBb.
Proof. intros. rewrite map_map. reflexivity. Qed.

End INST.

Lemma HI0_wf : heap_blocks_wf L0 HI0.
Proof.
  intros LB cr M VM (RUNp & s & L & LBb & nc & HCEIL & ELB & HR & CR & PL & HK & MI & AUX & REPL & BLK & Hnc & Hk & Hfst & Hsnd & POT & LEN & FA & LIVE).
  pose proof (hi0_nodup_addr s LBb M HR BLK) as ND. rewrite <- map_fst_blk_iv, <- ELB in ND.
  split; [| split; [apply NoDup_ListNoDup; exact ND| split; [exact Hfst| exact Hsnd]]].
  intros b Hb. pose proof Hb as Hb0. rewrite ELB in Hb. apply in_map_iff in Hb as (bb & <- & Hbb). cbn [fst snd blk_iv].
  pose proof (proj1 (List.Forall_forall _ _) BLK bb Hbb) as [Sz Def].
  pose proof (RHEAP_block_range_proof s LBb M bb HR Hbb) as (R1 & R2 & R3 & R4 & R5).
  split; [| split].
  - unfold HeapIface.block_range. cbn [hl_img_lo hl_img_hi hl_sptop L0]. splits.
    + exact (block_ge_4096 s LBb M bb HR Hbb).
    + unfold IMG_LO, IMG_HI. exact R5.
    + exact R2.
    + exact Sz.
    + rewrite <- HCEIL. exact R4.
  - intros i Hi. exact (Def i Hi).
  - intros b' Hb'. rewrite (lb_remove_filter (blk_addr bb) (blk_size bb) LB ND Hb0) in Hb'.
    apply filter_In in Hb' as [Hb' Hne]. rewrite ELB in Hb'. apply in_map_iff in Hb' as (bb' & <- & Hbb'). cbn [fst snd blk_iv] in *.
    destruct (Z.eqb_spec (blk_addr bb') (blk_addr bb)) as [E|NE]; [discriminate|].
    assert (Hid : blk_id bb <> blk_id bb').
    { intros Eid. apply NE. symmetry. f_equal. exact (nodup_map_inj blk_id LBb bb bb' (RHEAP_blocks_nodup_proof s LBb M HR) Hbb Hbb' Eid). }
    pose proof (RHEAP_blocks_disjoint_proof s LBb M bb bb' HR Hbb Hbb' Hid). lia.
Qed.

Lemma HI0_perm : heap_perm HI0.
Proof.
  intros LB LB' cr M VM (RUNp & s & L & LBb & nc & HCEIL & ELB & HR & CR & PL & HK & MI & AUX & REPL & BLK & REST) Hiff Hnd'.
  pose proof (hi0_nodup_addr s LBb M HR BLK) as ND. rewrite <- map_fst_blk_iv, <- ELB in ND.
  apply NoDup_ListNoDup in Hnd'.
  assert (HP : Permutation LB LB').
  { apply Permutation.NoDup_Permutation; [eapply List.NoDup_map_inv; exact ND| eapply List.NoDup_map_inv; exact Hnd'| exact Hiff]. }
  rewrite ELB in HP. apply Permutation_sym in HP.
  destruct (Permutation_map_inv _ _ HP) as (LBb' & -> & HPb).
  exists RUNp, s, L, LBb', nc. splits; try (apply REST).
  - exact HCEIL.
  - reflexivity.
  - eapply RHEAP_perm; [exact HR| exact HPb].
  - exact CR.
  - eapply Permutation_trans; [exact PL|]. apply Permutation_map. exact HPb.
  - exact HK.
  - exact MI.
  - exact AUX.
  - exact REPL.
  - apply List.Forall_forall. intros b Hb. apply (proj1 (List.Forall_forall _ _) BLK).
    eapply Permutation_in; [apply Permutation_sym; exact HPb| exact Hb].
Qed.

Section INST2.
Context {RUNp : RunP}.
Hypothesis HCEIL : alloc_ceiling = sptop - 2 ^ 23.

Lemma errno_byte : forall m i, 0 <= i < 4 ->
  (exists b, mrd rsegs m (wa (RERRNO + i)) = Some b) /\ wview rsegs m (wa (RERRNO + i)) <> None.
Proof.
  intros m i Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  unfold mrd, wview, RERRNO.
  destruct E as [-> |[-> |[-> | ->]]]; cbn [Z.add];
    (destruct (m (wa _)) as [b|]; [split; [exists b; reflexivity| discriminate]|]);
    (split; [eexists; vm_compute; reflexivity| vm_compute; discriminate]).
Qed.

Lemma errno_cell_any : forall m, exists v, rw_cells rsegs m RERRNO [C4 v].
Proof.
  intros m.
  destruct (proj1 (errno_byte m 0 ltac:(lia))) as [b0 E0]. destruct (proj1 (errno_byte m 1 ltac:(lia))) as [b1 E1].
  destruct (proj1 (errno_byte m 2 ltac:(lia))) as [b2 E2]. destruct (proj1 (errno_byte m 3 ltac:(lia))) as [b3 E3].
  destruct (le4_of_bytes b0 b1 b2 b3) as [v Ev]. exists v.
  split; [split; [exact (conj I I)|]|].
  - cbn [cells_bytes cbytes]. rewrite Ev. cbn [app]. split; [unfold RERRNO; lia|]. split; [unfold RERRNO; cbn; lia|].
    intros i Hi. cbn [length] in Hi.
    destruct i as [|[|[|[|i]]]]; cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ]; try lia.
    + rewrite Z.add_0_r in E0 |- *. rewrite <- (Z.add_0_r RERRNO). exact E0.
    + exact E1. + exact E2. + exact E3.
  - split; [unfold RERRNO; lia|]. split; [unfold RERRNO; cbn; lia|]. intros i Hi. apply (proj2 (errno_byte m i ltac:(cbn in Hi; lia))).
Qed.

Lemma ref_ro_addr_true : forall x : word, ro_addr rsegs x = true -> IMG_LO <= bv_unsigned x < 0xbd000.
Proof.
  intros x H. unfold ro_addr in H. unfold IMG_LO.
  pose proof (bv_unsigned_in_range 64 x) as R.
  set (z := bv_unsigned x) in *.
  unfold rsegs, Ubsan.Ubsan_loaded_segments in H. cbn [find_segment] in H.
  replace (Z.of_N (seg_base Ubsan_segment_000)) with 65536%Z in H by vmc_refl.
  replace (Z.of_N (seg_size Ubsan_segment_000)) with 167936%Z in H by vmc_refl.
  replace (Z.of_N (seg_base Ubsan_segment_001)) with 233472%Z in H by vmc_refl.
  replace (Z.of_N (seg_size Ubsan_segment_001)) with 540672%Z in H by vmc_refl.
  replace (Z.of_N (seg_base Ubsan_segment_002)) with 774144%Z in H by vmc_refl.
  replace (Z.of_N (seg_size Ubsan_segment_002)) with 28672%Z in H by vmc_refl.
  replace (Z.of_N (seg_base Ubsan_segment_003)) with 802816%Z in H by vmc_refl.
  replace (Z.of_N (seg_size Ubsan_segment_003)) with 212992%Z in H by vmc_refl.
  destruct (Z.leb_spec0 65536 z); destruct (Z.leb_spec0 (z + 1) (65536 + 167936)); cbn [andb] in H; try lia.
  all: destruct (Z.leb_spec0 233472 z); destruct (Z.leb_spec0 (z + 1) (233472 + 540672)); cbn [andb] in H; try lia.
  all: destruct (Z.leb_spec0 774144 z); destruct (Z.leb_spec0 (z + 1) (774144 + 28672)); cbn [andb] in H; try lia.
  all: try (replace (seg_writable Ubsan_segment_002) with true in H by vmc_refl; discriminate).
  all: destruct (Z.leb_spec0 802816 z); destruct (Z.leb_spec0 (z + 1) (802816 + 212992)); cbn [andb] in H; try lia.
  all: try (replace (seg_writable Ubsan_segment_003) with true in H by vmc_refl; discriminate).
  all: try discriminate.
Qed.

Lemma outside_iff : forall W z, outside W z <-> (forall iv, In iv W -> ~ (fst iv <= z < snd iv)).
Proof.
  induction W as [|[lo hi] W IH]; intros z; cbn [outside].
  - split; [intros _ iv []| intros; exact I].
  - rewrite IH. split.
    + intros [H1 H2] iv [<-|Hin]; [exact H1| apply H2; exact Hin].
    + intros H. split; [apply (H (lo, hi)); left; reflexivity| intros iv Hin; apply H; right; exact Hin].
Qed.

Definition client_img_ivs : list ivl := [(0xbd000, 0xc3a48); (0xc3a50, 0xf6a70); (0xf6a78, 0xf6a90); (0xf6fb8, 0xf73f4); (0xf73f8, 0xf8000)].
Definition frameW (LBb : list block) : list ivl :=
  (alloc_ceiling, sptop) :: client_img_ivs ++ map (fun b => (blk_addr b, blk_addr b + blk_size b)) LBb.

Lemma outside_frameW_private : forall LBb z, alloc_ceiling <= sptop ->
  outside (frameW LBb) z -> alloc_private (L0) (map blk_iv LBb) z.
Proof.
  intros LBb z Hsp H0. pose proof (proj1 (outside_iff _ _) H0) as H. clear H0.
  assert (O1 : ~ (alloc_ceiling <= z < sptop)) by (apply (H (alloc_ceiling, sptop)); left; reflexivity).
  assert (O2 : ~ (0xbd000 <= z < 0xc3a48)) by (apply (H (0xbd000, 0xc3a48)); right; left; reflexivity).
  assert (O3 : ~ (0xc3a50 <= z < 0xf6a70)) by (apply (H (0xc3a50, 0xf6a70)); do 2 right; left; reflexivity).
  assert (O4 : ~ (0xf6a78 <= z < 0xf6a90)) by (apply (H (0xf6a78, 0xf6a90)); do 3 right; left; reflexivity).
  assert (O5 : ~ (0xf6fb8 <= z < 0xf73f4)) by (apply (H (0xf6fb8, 0xf73f4)); do 4 right; left; reflexivity).
  assert (O6 : ~ (0xf73f8 <= z < 0xf8000)) by (apply (H (0xf73f8, 0xf8000)); do 5 right; left; reflexivity).
  assert (OB : forall b, In b LBb -> ~ (blk_addr b <= z < blk_addr b + blk_size b)).
  { intros b Hb. apply (H (blk_addr b, blk_addr b + blk_size b)). do 6 right. apply in_map_iff. exists b. auto. }
  unfold alloc_private. cbn [hl_alloc_ro hl_img_lo hl_img_hi hl_alloc_static hl_sptop L0].
  unfold IMG_LO, IMG_HI, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD in *. rewrite HCEIL in *.
  destruct (Z_le_gt_dec sptop z) as [Hs|Hs]; [right; lia|].
  destruct (Z_le_gt_dec 0x10000 z) as [I1|I1]; [destruct (Z_lt_ge_dec z 0xbd000) as [I2|I2]; [right; lia|]|].
  all: destruct (Z_le_gt_dec 0xf6a90 z) as [J1|J1]; [destruct (Z_lt_ge_dec z 0xf6c08) as [J2|J2]; [right; lia|]|].
  all: destruct (Z_le_gt_dec 0xf6fb0 z) as [K1|K1]; [destruct (Z_lt_ge_dec z 0xf6fb8) as [K2|K2]; [right; lia|]|].
  all: destruct (Z_le_gt_dec 0xc3a48 z) as [G1|G1]; [destruct (Z_lt_ge_dec z 0xc3a50) as [G2|G2]; [right; lia|]|].
  all: destruct (Z_le_gt_dec 0xf6a70 z) as [U1|U1]; [destruct (Z_lt_ge_dec z 0xf6a78) as [U2|U2]; [right; lia|]|].
  all: destruct (Z_le_gt_dec 0xf73f4 z) as [V1|V1]; [destruct (Z_lt_ge_dec z 0xf73f8) as [V2|V2]; [right; lia|]|].
  all: left; split; [lia|]; split; [intros (b & Hb & Hr); apply in_map_iff in Hb as (bb & <- & Hbb); cbn [fst snd blk_iv] in Hr; exact (OB bb Hbb Hr)| lia].
Qed.

Lemma frameW_client : forall LBb, Forall (rclient_write_ok LBb) (frameW LBb).
Proof.
  intros LBb. unfold frameW. constructor; [left; cbn; lia|]. apply Forall_app. split.
  - unfold client_img_ivs, rclient_write_ok, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP.
    repeat (apply Forall_cons; [cbn [fst snd]; right; left; lia|]). apply Forall_nil.
  - apply List.Forall_forall. intros iv Hin. apply in_map_iff in Hin as (b & <- & Hb). right; right. exists b. cbn [fst snd]. split; [exact Hb| lia].
Qed.

End INST2.

Lemma HI0_frame : heap_frame L0 HI0.
Proof.
  intros LB cr M M' VM (RUNp & s & L & LBb & nc & HCEIL & ELB & HR & CR & PL & HK & MI & AUX & REPL & BLK & REST) Hpriv Hmono.
  pose proof AUX as (av & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & rnd & CELL & BY1 & BY2 & Bc & Bav & Hav & Brnd & Hrnd & X3 & X4 & X5 & XHW & X6 & X11 & X12 & X23 & Xr).
  assert (WM : wmono rsegs M M') by (apply wmono_of_grows; exact Hmono).
  assert (AG : forall a, 0 <= a < 2^64 -> alloc_private L0 LB a -> M' (wa a) = M (wa a)).
  { intros a Ha Hp. unfold wa. apply Hpriv; assumption. }
  assert (MU : munch (frameW LBb) M M').
  { intros x Hout. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
    rewrite <- (Z_to_bv_bv_unsigned x). apply Hpriv; [lia|]. rewrite ELB. apply outside_frameW_private; [exact HCEIL| exact Bc| exact Hout]. }
  exists RUNp, s, L, LBb, nc. splits; try (apply REST).
  - exact HCEIL.
  - exact ELB.
  - eapply RHEAP_frame_proof; [exact HR| exact MU| exact WM| apply frameW_client].
  - exact CR.
  - exact PL.
  - exact HK.
  - intros a b Ha. destruct (ro_addr rsegs a) eqn:E; [|reflexivity]. exfalso.
    pose proof (ref_ro_addr_true a E) as Hro. pose proof (bv_unsigned_in_range 64 a) as R. unfold bv_modulus in R.
    rewrite <- (Z_to_bv_bv_unsigned a) in Ha. rewrite Hpriv in Ha; [| lia| right; cbn; left; exact Hro].
    rewrite Z_to_bv_bv_unsigned in Ha. pose proof (MI a b Ha). congruence.
  - exists av, x3, x4, x5, hw, x6, x11, x12, x23, rnd. splits; try assumption; try lia.
    + eapply rw_cells_agree; [exact CELL| | exact WM]. intros a Ha. cbn in Ha. apply AG; [unfold RAUXV_CELL in Ha; lia|].
      right. cbn. unfold RAUXV_CELL, RLIBC, RMLOCK in *. lia.
    + eapply bytes_at_agree; [exact BY1|]. intros a Ha. pose proof (bytes_at_bound _ _ _ _ BY1). apply AG; [lia|]. right. cbn. lia.
    + eapply bytes_at_agree; [exact BY2|]. intros a Ha. pose proof (bytes_at_bound _ _ _ _ BY2). apply AG; [lia|]. right. cbn. lia.
  - intros a Ha. pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra.
    rewrite <- (Z_to_bv_bv_unsigned a). rewrite Hpriv; [| lia| right; cbn; unfold RCTX in *; lia].
    rewrite Z_to_bv_bv_unsigned. apply REPL. exact Ha.
  - apply List.Forall_forall. intros b Hb. pose proof (proj1 (List.Forall_forall _ _) BLK b Hb) as [Sz Def].
    split; [exact Sz|]. intros i Hi. apply Hmono. apply Def. exact Hi.
Qed.

Section INST3.
Context {RUNp : RunP}.
Hypothesis HCEIL : alloc_ceiling = sptop - 2 ^ 23.

Lemma RHEAP_slots_nodup : forall s LB m, RHEAP s LB m -> List.NoDup (map blk_slot LB).
Proof.
  intros s LB m (st & LB0 & HP & _ & _ & [_ AR]). eapply NoDup_map_perm; [exact HP|].
  exact (mf_nodup _ _ (areach_facts_proof _ _ AR)).
Qed.

Lemma map_blk_iv_lbrm : forall LBb blk A,
  (forall b', In b' LBb -> aptr_eqb (blk_slot b') (blk_slot blk) = (blk_addr b' =? A)) ->
  map blk_iv (lbrm LBb blk) = List.filter (fun b => negb (fst b =? A)) (map blk_iv LBb).
Proof.
  induction LBb as [|b l IH]; intros blk A HE; [reflexivity|].
  unfold lbrm. rewrite filter_cons. fold (lbrm l blk). cbn [map List.filter fst blk_iv].
  rewrite <- (HE b (or_introl eq_refl)).
  destruct (decide _) as [Y|N].
  - destruct (aptr_eqb (blk_slot b) (blk_slot blk)); [destruct Y|]. cbn [negb map]. f_equal. apply IH. intros b' Hb'. apply HE. right. exact Hb'.
  - destruct (aptr_eqb (blk_slot b) (blk_slot blk)); [| exfalso; apply N; exact I]. cbn [negb]. apply IH. intros b' Hb'. apply HE. right. exact Hb'.
Qed.

Lemma lb_remove_corr : forall LBb p A n,
  List.NoDup (map blk_slot LBb) -> List.NoDup (map blk_addr LBb) -> In (p, A, n) LBb ->
  HeapIface.lb_remove A (map blk_iv LBb) = map blk_iv (lbrm LBb (p, A, n)).
Proof.
  intros LBb p A n NDs NDa Hin.
  rewrite (lb_remove_filter A n (map blk_iv LBb)); [| rewrite map_fst_blk_iv; exact NDa| apply in_map_iff; exists (p, A, n); split; [reflexivity| exact Hin]].
  symmetry. apply map_blk_iv_lbrm. intros b' Hb'. change (blk_slot (p, A, n)) with (fst p).
  destruct (aptr_eqb_spec (blk_slot b') (fst p)) as [E|NE]; destruct (Z.eqb_spec (blk_addr b') A) as [E'|NE']; try reflexivity; exfalso.
  - apply NE'. pose proof (nodup_map_inj blk_slot LBb b' (p, A, n) NDs Hb' Hin E) as ->. reflexivity.
  - apply NE. pose proof (nodup_map_inj blk_addr LBb b' (p, A, n) NDa Hb' Hin E') as ->. reflexivity.
Qed.

Lemma ret_pc_jalr : forall ra : word, ret_pc ra = jalr_tgt ra 0.
Proof.
  intros ra. apply bv_eq. unfold ret_pc, jalr_tgt, jalr_tgtZ.
  rewrite bv_and_unsigned, bv_not_unsigned, !Z_to_bv_unsigned.
  change (bv_wrap 64 1) with 1%Z. change (Z.lnot 1) with (-2)%Z. rewrite Z.add_0_r.
  rewrite <- (bv_wrap_small 64 (bv_unsigned ra)) at 1 by apply bv_unsigned_in_range. apply Z_land_m2_wrap.
Qed.

Lemma ret_pc_ok : forall ra : word, ret_ok ra -> ret_pc ra = ra.
Proof. intros ra H. rewrite ret_pc_jalr. exact H. Qed.

Lemma regs_preserved_canon : forall (R R' : bvmap 5 word) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  regs_eqv (mkR (getr R (Z_to_bv 5 1)) (getr R (Z_to_bv 5 2)) (getr R (Z_to_bv 5 3)) (getr R (Z_to_bv 5 4)) t0 t1 t2
                (getr R (Z_to_bv 5 8)) (getr R (Z_to_bv 5 9)) a0 a1 a2 a3 a4 a5 a6 a7
                (getr R (Z_to_bv 5 18)) (getr R (Z_to_bv 5 19)) (getr R (Z_to_bv 5 20)) (getr R (Z_to_bv 5 21)) (getr R (Z_to_bv 5 22))
                (getr R (Z_to_bv 5 23)) (getr R (Z_to_bv 5 24)) (getr R (Z_to_bv 5 25)) (getr R (Z_to_bv 5 26)) (getr R (Z_to_bv 5 27))
                t3 t4 t5 t6) R' ->
  regs_preserved R R'.
Proof.
  intros R R' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HE r Hr.
  rewrite <- (getr_eqv _ _ r HE).
  unfold callee_saved_idx in Hr.
  assert (Er : exists k, In k callee_saved_idx /\ r = Z_to_bv 5 k).
  { exists (bv_unsigned r). split; [exact Hr| symmetry; apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range]. }
  destruct Er as (k & Hk & ->). unfold callee_saved_idx in Hk. cbn [In] in Hk.
  repeat (destruct Hk as [<-|Hk]; [unfold getr; cbn; reflexivity|]). destruct Hk.
Qed.

Lemma heap_pres_core_of_cj : forall LBb' (sp : Z) m m',
  rheap_pres LBb' sp m m' -> rdeep_pres (sp - RALIGNED_STACK) m m' -> rimg_pres m m' ->
  stk rsegs m' (sp - RALIGNED_STACK) sp -> alloc_ceiling <= sp - RALIGNED_STACK ->
  heap_pres_core L0 (map blk_iv LBb') sp m m'.
Proof.
  intros LBb' sp m m' HP HD HI ST LO. pose_ceil. unfold RALIGNED_STACK, RMALLOC_STACK in *. rewrite HCEIL in LO.
  split; cbn [hl_stack hl_img_lo hl_img_hi hl_alloc_static hl_errno hl_sptop L0]; unfold RALIGNED_STACK, RMALLOC_STACK.
  - intros a Ha CA NE. change (Z_to_bv 64 a) with (wa a).
    destruct CA as [(b & Hb & Hr)|[[Hhi Hns]|[Himg Hnst]]].
    + apply in_map_iff in Hb as (bb & <- & Hbb). cbn [fst snd blk_iv] in Hr.
      apply (proj1 (HP a Ha ltac:(right; right; exists bb; split; [exact Hbb| exact Hr]))).
    + cbn [hl_sptop L0] in Hhi. destruct (Z_le_gt_dec sp a) as [Hs|Hs].
      * apply (proj1 (HP a Ha ltac:(left; exact Hs))).
      * apply HD. rewrite HCEIL. lia.
    + unfold in_errno in NE. cbn [hl_errno L0] in NE. unfold IMG_LO, IMG_HI, RMLOCK, RCTX, RERRNO in *.
      apply HI; [exact Himg| intros X; apply Hnst; cbn [hl_alloc_static L0]; unfold RMLOCK, RCTX in *; lia| unfold RERRNO; exact NE].
  - intros a Ha. destruct ST as (_ & Hsp & S). destruct (S a ltac:(lia)) as [W _].
    rewrite ref_wview_overlay in W by (unfold wa; rewrite u64_lit; lia). exact W.
Qed.

Lemma map_blk_slot_lbrm : forall LBb blk,
  map blk_slot (lbrm LBb blk) = filter (fun c => negb (aptr_eqb c (blk_slot blk))) (map blk_slot LBb).
Proof.
  induction LBb as [|b l IH]; intros blk; [reflexivity|].
  unfold lbrm. cbn [map]. rewrite !filter_cons. fold (lbrm l blk).
  destruct (decide _) as [Y|N]; [cbn [map]; f_equal; apply IH| apply IH].
Qed.

Lemma filter_keep_all : forall c (l : list aptr), ~ In c l ->
  filter (fun y => negb (aptr_eqb y c)) l = l.
Proof.
  intros c l. induction l as [|z l IH]; intros Hni; [reflexivity|]. rewrite filter_cons.
  destruct (aptr_eqb_spec z c) as [->|NE]; [exfalso; apply Hni; left; reflexivity|].
  destruct (decide _) as [Y|N]; [| exfalso; apply N; exact I].
  f_equal. apply IH. intros H; apply Hni; right; exact H.
Qed.

Lemma ap_remove_filter : forall c l, List.NoDup l -> In c l ->
  ap_remove c l = filter (fun y => negb (aptr_eqb y c)) l.
Proof.
  intros c l. induction l as [|y l IH]; intros ND Hin; [destruct Hin|]. cbn [ap_remove]. rewrite filter_cons.
  inversion ND as [|? ? Hni ND']; subst.
  destruct (aptr_eqb_spec y c) as [->|NE].
  - destruct (decide _) as [Y|N]; [destruct Y|]. symmetry. apply filter_keep_all. exact Hni.
  - destruct (decide _) as [Y|N]; [| exfalso; apply N; exact I].
    f_equal. apply IH; [exact ND'|]. destruct Hin as [->|Hin]; [congruence| exact Hin].
Qed.

Lemma bv5_lit : forall k, 0 <= k < 32 -> forall H, Z_to_bv 5 k = @BV 5 k H.
Proof. intros k Hk H. apply bv_eq. rewrite Z_to_bv_unsigned. cbn [bv_unsigned]. unfold bv_wrap, bv_modulus. rewrite Z.mod_small; [reflexivity|]. cbn. lia. Qed.

Lemma implM_mupd_only_inv : forall {St} (f : St -> St) (s : St) (Q : unit -> St -> machine_state -> Prop) ms,
  implM rsegs (mupd f) s Q ms -> evt rsegs (Q tt (f s)) ms.
Proof. intros St f s Q ms H. exact H. Qed.

End INST3.

Section DELIVERABLES.
Variable SCFG : SpuriousCfg.
Hypothesis HALLOC : sc_alloc SCFG = false.
Hypothesis MBND : forall R : RunP, @model_bounds R.

Lemma HI0_free : free_spec L0 SCFG HI0.
Proof.
  intros fx R M model LB cr A n K HH Hh Hl Hm HinLB R10 R4 RET SOK HK0 CONT.
  cbn [hi_heap HI0 hl_tp hl_free hl_segs L0] in *.
  rewrite <- (bv5_lit 10 ltac:(lia)) in R10. rewrite <- (bv5_lit 4 ltac:(lia)) in R4. rewrite <- (bv5_lit 1 ltac:(lia)) in RET, CONT.
  rewrite <- (bv5_lit 2 ltac:(lia)) in SOK, CONT.
  destruct HH as (RUNp & s & L & LBb & nc & HCEIL & ELB & HR & CR & PL & HKL & MI & AUX & REPL & BLK & Hnc & Hk & Hfst & Hsnd & POT & LEN & FA & LIVE).
  pose proof (hi0_nodup_addr s LBb M HR BLK) as NDa. pose proof (RHEAP_slots_nodup s LBb M HR) as NDs.

  rewrite ELB in HinLB. apply in_map_iff in HinLB as (bb & Ebb & Hbb).
  destruct bb as [[p A'] n']. unfold blk_iv, blk_addr, blk_size in Ebb. cbn [fst snd] in Ebb. injection Ebb as -> ->.

  destruct (stack_ok_stk HCEIL M _ SOK) as (STK & LO & SPT & SPR). set (sp := bv_unsigned (getr R (Z_to_bv 5 2))) in *.
  destruct (errno_cell_any M) as [errv ERR].
  assert (ERR' : rw_cells rsegs M (bv_unsigned (getr R (Z_to_bv 5 4)) + -164) [C4 errv]).
  { rewrite R4. replace (bv_unsigned (Z_to_bv 64 RATP) + -164) with RERRNO by vmc_refl. exact ERR. }

  pose proof (rfree_spec_proof (getr R (Z_to_bv 5 1)) (getr R (Z_to_bv 5 2)) (getr R (Z_to_bv 5 3)) (getr R (Z_to_bv 5 4))
                (getr R (Z_to_bv 5 5)) (getr R (Z_to_bv 5 6)) (getr R (Z_to_bv 5 7)) (getr R (Z_to_bv 5 8)) (getr R (Z_to_bv 5 9))
                (getr R (Z_to_bv 5 10)) (getr R (Z_to_bv 5 11)) (getr R (Z_to_bv 5 12)) (getr R (Z_to_bv 5 13)) (getr R (Z_to_bv 5 14))
                (getr R (Z_to_bv 5 15)) (getr R (Z_to_bv 5 16)) (getr R (Z_to_bv 5 17)) (getr R (Z_to_bv 5 18)) (getr R (Z_to_bv 5 19))
                (getr R (Z_to_bv 5 20)) (getr R (Z_to_bv 5 21)) (getr R (Z_to_bv 5 22)) (getr R (Z_to_bv 5 23)) (getr R (Z_to_bv 5 24))
                (getr R (Z_to_bv 5 25)) (getr R (Z_to_bv 5 26)) (getr R (Z_to_bv 5 27)) (getr R (Z_to_bv 5 28)) (getr R (Z_to_bv 5 29))
                (getr R (Z_to_bv 5 30)) (getr R (Z_to_bv 5 31))
                fp_regs fp_csr M s LBb p A n (sp - RALIGNED_STACK) sptop errv
                HR Hbb AUX SPT STK LO ltac:(unfold RFREE_STACK, RALIGNED_STACK, RMALLOC_STACK; lia)
                ERR' MI R4 R10) as IMPL.
  change (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with (canon_regs R) in IMPL.

  apply (implM_eqv_transfer rsegs _ _ _ _ (mkst R (Z_to_bv 64 RFREE_SYM) M (seg_rom rsegs))) in IMPL; [| apply mkst_eqv_canon].

  unfold raw_free in IMPL. apply implM_mget_inv, implM_bind_inv in IMPL.

  assert (LIVEp : In (fst p) (ld_live L)).
  { eapply Permutation_in; [apply Permutation_sym; exact PL|]. apply in_map_iff. exists (p, A, n). split; [reflexivity| exact Hbb]. }
  eapply (embed_free rsegs SCFG RESV IMG_HI _ _ _ _ _ _ s _ _ model model (m_vmmaps model) K
            (cfree_contract_proof _ _ _ CR LIVEp) (mb_free (MBND RUNp) _ _ _ CR LIVEp) IMPL HKL).
  - symmetry. apply with_vmmaps_eta.
  - exact Hh. - exact Hl. - exact Hm.
  - apply vm_shrunk_refl.
  -
    intros cs' s' ms' mo' L' HQ HCP _ HPOT HK' Emo' HS E1 E2 E3.
    cbv beta in HQ. apply implM_mupd_only_inv in HQ. destruct HQ as (ms2 & Hms2 & (ms1 & POST & EQV)).
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Ems1 &
                      MI' & STK' & ERR2 & AUX' & HPRES & HDEEP & HIMG & _ & _ & HR').
    subst ms1. destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems2 REQ].
    assert (Hh' : m_halted mo' = None) by (rewrite Emo', with_vmmaps_halted; exact Hh).
    assert (Hl' : m_vm_lazy mo' = []) by (rewrite Emo', with_vmmaps_lazy'; exact Hl).
    eapply srz_msteps; [exact Hh'| exact Hl'| apply cj_msteps_cat; exact Hms2|].
    rewrite Ems2, (ret_pc_ok _ RET). change (MS ?R' fp_regs ?pc fp_csr None ?mm ?ro) with (mkst R' pc mm ro).

    pose proof (lb_remove_corr LBb p A n NDs NDa Hbb) as ELB'. rewrite <- ELB in ELB'.
    rewrite (lb_remove_lbrm LBb p A n NDs Hbb) in HPRES, HR'.
    assert (SUB : forall b, In b (lbrm LBb (p, A, n)) -> In b LBb).
    { intros b Hb. unfold lbrm in Hb. apply list_elem_of_In, list_elem_of_filter in Hb. apply list_elem_of_In. tauto. }
    apply CONT.
    + eapply regs_preserved_canon. exact REQ.
    + split.
      * rewrite ELB'. apply heap_pres_core_of_cj; assumption.
      * cbn [hl_segs hl_errno L0]. change (Z_to_bv 64 RERRNO) with (wa (RERRNO + Z.of_nat 0)).
        pose proof ERR as [[_ B1] _]. pose proof ERR2 as [[_ B2] _].
        rewrite R4 in B2. replace (bv_unsigned (Z_to_bv 64 RATP) + -164) with RERRNO in B2 by vmc_refl.
        rewrite (bytes_at_rdn rsegs m' RERRNO _ 0 4 B2) by (cbn; lia). rewrite (bytes_at_rdn rsegs M RERRNO _ 0 4 B1) by (cbn; lia). reflexivity.
    + exact Emo'.
    + rewrite ELB'. exists RUNp, (set_m cs' s'), (set_live (ap_remove (fst p) (ld_live L')) L'), (lbrm LBb (p, A, n)), nc.
      destruct HS as (S1 & S2 & S3 & S4 & S5 & S6).
      splits; try assumption.
      * reflexivity.
      * cbn [ps_m set_m]. eapply creach_free; [exact CR| exact LIVEp| exact HCP].
      * cbn [ld_live set_live]. assert (EL : ld_live L' = ld_live L) by (eapply cpath_live; exact HCP). rewrite EL, map_blk_slot_lbrm. change (blk_slot (p, A, n)) with (fst p).
        rewrite ap_remove_filter; [| eapply Permutation.Permutation_NoDup; [apply Permutation_sym; exact PL| exact NDs]| exact LIVEp].
        apply filter_Permutation. exact PL.
      * cbn [ps_brk set_m]. apply KL2_set_live. exact HK'.
      * intros a Ha. pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra.
        rewrite <- (Z_to_bv_bv_unsigned a). change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)).
        rewrite HIMG; [| unfold RCTX in *; lia| unfold RCTX in *; lia| unfold RCTX, RERRNO in *; lia].
        unfold wa. rewrite Z_to_bv_bv_unsigned. apply REPL. exact Ha.
      * apply List.Forall_forall. intros b Hb. pose proof (SUB b Hb) as HbL.
        pose proof (proj1 (List.Forall_forall _ _) BLK b HbL) as [Sz Def]. split; [exact Sz|].
        intros i Hi. pose proof (RHEAP_block_range_proof s LBb M b HR HbL) as (Q1 & _ & _ & Q4 & _). pose proof alloc_ceiling_lt.
        rewrite (proj1 (HPRES (blk_addr b + i) ltac:(lia) ltac:(right; right; exists b; split; [exact Hb| lia]))). apply Def. exact Hi.
      * cbn [ps_m set_m]. lia.
      * rewrite S1, length_app. rewrite length_app in LEN. lia.
      * rewrite S1. apply Forall_app in FA as [FA1 FA2]. apply Forall_app. split; [exact FA1| apply S4; exact FA2].
      * lia.
Qed.

Lemma size_overflows_small : forall n, n <= 2^27 -> size_overflows n = false.
Proof. intros n Hn. unfold size_overflows. apply Z.leb_gt. lia. Qed.

Lemma elen_ok_NMAX : forall n PA a len prot flags, 0 < n <= 2^27 -> PA <= POTMAX + AMC ->
  elen_ok n PA (EMmap a len prot flags) -> is_fixed flags = false -> mmap_len len <= NMAX.
Proof.
  intros n PA a len prot flags Hn HPA HE Hf. cbn [elen_ok] in HE.
  assert (ML : forall l, mmap_len l <= l + 4095).
  { intros l. unfold mmap_len, page_round_up_Z, page_size. pose proof (Z.mul_div_le (l + (4096 - 1)) 4096 ltac:(lia)). lia. }
  replace NMAX with 134283264 by reflexivity. replace (2^27) with 134217728 in Hn by reflexivity.
  unfold POTMAX, POT0, AMC, NCMAX, NSLOTS in HPA.
  destruct HE as [HE|[[_ HE]|[_ HE]]]; [congruence| |].
  - pose proof (ML len). unfold NSLOTS, PGSZ in HE. lia.
  - pose proof (ML (n + IB + UNIT)) as H2. unfold mmap_len in H2. rewrite <- round_up_pg_eq in H2.
    unfold GMAX, IB, UNIT in *. replace (2^20) with 1048576 in HE by reflexivity. lia.
Qed.

Lemma HI0_malloc : malloc_spec L0 SCFG HI0.
Proof.
  intros fx R M model LB cr n K HH Hh Hl Hm R10 Hn HCR R4 RET SOK HK0 CONT.
  cbn [hi_heap HI0 hl_tp hl_malloc hl_segs L0] in *.
  rewrite <- (bv5_lit 10 ltac:(lia)) in R10, CONT. rewrite <- (bv5_lit 4 ltac:(lia)) in R4. rewrite <- (bv5_lit 1 ltac:(lia)) in RET, CONT.
  rewrite <- (bv5_lit 2 ltac:(lia)) in SOK, CONT.
  destruct HCR as [CRK CRB]. cbn [hl_k_per_malloc hl_b_overhead L0 fst snd] in CRK, CRB.
  destruct HH as (RUNp & s & L & LBb & nc & HCEIL & ELB & HR & CR & PL & HKL & MI & AUX & REPL & BLK & Hnc & Hk & Hfst & Hsnd & POT & LEN & FA & LIVE).
  pose proof (hi0_nodup_addr s LBb M HR BLK) as NDa. pose proof (RHEAP_slots_nodup s LBb M HR) as NDs.

  destruct (stack_ok_stk HCEIL M _ SOK) as (STK & LO & SPT & SPR). set (sp := bv_unsigned (getr R (Z_to_bv 5 2))) in *.
  destruct (errno_cell_any M) as [errv ERR].
  assert (ERR' : rw_cells rsegs M (bv_unsigned (getr R (Z_to_bv 5 4)) + -164) [C4 errv]).
  { rewrite R4. replace (bv_unsigned (Z_to_bv 64 RATP) + -164) with RERRNO by vmc_refl. exact ERR. }

  pose proof (rmalloc_spec (getr R (Z_to_bv 5 1)) (getr R (Z_to_bv 5 2)) (getr R (Z_to_bv 5 3)) (getr R (Z_to_bv 5 4))
                (getr R (Z_to_bv 5 5)) (getr R (Z_to_bv 5 6)) (getr R (Z_to_bv 5 7)) (getr R (Z_to_bv 5 8)) (getr R (Z_to_bv 5 9))
                (getr R (Z_to_bv 5 10)) (getr R (Z_to_bv 5 11)) (getr R (Z_to_bv 5 12)) (getr R (Z_to_bv 5 13)) (getr R (Z_to_bv 5 14))
                (getr R (Z_to_bv 5 15)) (getr R (Z_to_bv 5 16)) (getr R (Z_to_bv 5 17)) (getr R (Z_to_bv 5 18)) (getr R (Z_to_bv 5 19))
                (getr R (Z_to_bv 5 20)) (getr R (Z_to_bv 5 21)) (getr R (Z_to_bv 5 22)) (getr R (Z_to_bv 5 23)) (getr R (Z_to_bv 5 24))
                (getr R (Z_to_bv 5 25)) (getr R (Z_to_bv 5 26)) (getr R (Z_to_bv 5 27)) (getr R (Z_to_bv 5 28)) (getr R (Z_to_bv 5 29))
                (getr R (Z_to_bv 5 30)) (getr R (Z_to_bv 5 31))
                fp_regs fp_csr M s LBb n (sp - RALIGNED_STACK) sptop errv
                HR AUX SPT STK LO ltac:(unfold RALIGNED_STACK, RMALLOC_STACK; lia) ERR' MI R4 R10 ltac:(lia)) as IMPL.
  change (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with (canon_regs R) in IMPL.
  apply (implM_eqv_transfer rsegs _ _ _ _ (mkst R (Z_to_bv 64 RMALLOC_SYM) M (seg_rom rsegs))) in IMPL; [| apply mkst_eqv_canon].
  unfold raw_malloc in IMPL. apply implM_mget_inv, implM_bind_inv in IMPL.

  set (cs := ps_m s) in *. set (PA := pot cs + AMC).
  assert (HPA : PA <= POTMAX + AMC).
  { subst PA. unfold POTMAX, POT0, AMC, NCMAX, NSLOTS in *. unfold K0, KPM, NCMAX in Hk. unfold KPM in CRK. change (Z.of_nat EVM) with 8 in Hk, CRK. lia. }
  pose proof (CALLB_le n PA ltac:(lia) HPA) as [CB0 CB1].
  set (CAPK := K0 + NSEG - fst cr + KPM). set (CAPB := B0 - snd cr + (n + BOV)).
  assert (HCAPK : CAPK <= CAPKMAX) by (subst CAPK; unfold K0, NSEG, KPM, NCMAX, CAPKMAX; change (Z.of_nat EVM) with 8; lia).
  assert (HCAPB : CAPB <= CAPBMAX) by (subst CAPB; unfold CAPBMAX, B0 in *; lia).
  eapply (embed rsegs SCFG HALLOC RESV IMG_HI CAPK CAPB HCAPK HCAPB (cmalloc cs n) L _ (elen_ok n PA) EVM (CALLB n PA) _ s _ _ model model K
            (cmalloc_contract_proof cs L n CR ltac:(lia))
            (mb_malloc (MBND RUNp) cs L n CR ltac:(lia) (size_overflows_small n ltac:(lia)))
            (fun a len prot flags HE Hf => elen_ok_NMAX n PA a len prot flags Hn HPA HE Hf)
            IMPL HKL).
  - symmetry. apply with_vmmaps_eta.
  - exact Hh. - exact Hl. - exact Hm.
  -
    unfold RI. splits.
    + subst CAPK. unfold KPM. change (Z.of_nat EVM) with 8 in *. lia.
    + exact FA.
    + subst CAPB. lia.
    + exact CB0.
    + exact (KL2_init_sp_window _ _ _ _ _ HKL).
  -
    intros [cs' rc] s' ms' mo' L' HQ HCP HPOST [HSOME HPOT] HK' Emo' HRI' E1 E2 E3. cbn [fst snd] in HSOME, HPOT, HPOST.
    destruct rc as [c|]; [| exfalso; apply HSOME; reflexivity]. clear HSOME.
    cbv beta iota in HQ. apply implM_mupd_inv, implM_ret_inv in HQ. destruct HQ as (ms2 & Hms2 & (ms1 & POST & EQV)).
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & Ems1 &
                      MI' & STK' & ERR2 & AUX' & HPRES & HDEEP & HIMG & _ & _ & (A & junk & EA0 & RBR & HR' & UCH & _)).
    subst ms1. destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems2 REQ].
    assert (Hh' : m_halted mo' = None) by (rewrite Emo', with_vmmaps_halted; exact Hh).
    assert (Hl' : m_vm_lazy mo' = []) by (rewrite Emo', with_vmmaps_lazy'; exact Hl).
    eapply srz_msteps; [exact Hh'| exact Hl'| apply cj_msteps_cat; exact Hms2|].
    rewrite Ems2, (ret_pc_ok _ RET). change (MS ?R' fp_regs ?pc fp_csr None ?mm ?ro) with (mkst R' pc mm ro).
    set (pb := (c, fresh_off cs' c n)) in *.
    set (LBb' := (pb, A, n) :: LBb) in *.
    assert (CR' : creach cs' (set_live (c :: ld_live L') L')).
    { exact (creach_malloc cs L n L' cs' (Some c) CR ltac:(lia) HCP). }
    assert (HK'' : KL2 RESV IMG_HI (set_live (c :: ld_live L') L') (ps_brk (set_m cs' s')) (m_vmmaps mo')).
    { cbn [ps_brk set_m]. apply KL2_set_live. exact HK'. }
    assert (HA4 : 4096 <= A).
    { change A with (blk_addr (pb, A, n)). apply (block_ge_4096 (set_m cs' s') LBb' m' (pb, A, n) HR'). left. reflexivity. }
    pose proof RBR as (B1 & B2 & B3 & B4 & B5). pose proof alloc_ceiling_lt as ACL.
    assert (DEF : forall i, 0 <= i < n -> m' (wa (A + i)) <> None).
    { intros i Hi. destruct UCH as [[WF BA] _]. cbn [cells_wf cell_wf] in WF. destruct WF as [Hlen _].
      destruct BA as (_ & _ & BA). cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
      specialize (BA (Z.to_nat i) ltac:(rewrite Hlen; lia)). rewrite Z2Nat.id in BA by lia.
      rewrite ref_mrd_overlay in BA by (unfold wa; rewrite u64_lit by lia; clear - B5 Hi; lia).
      rewrite BA. destruct (nth_error _ _) eqn:En; [discriminate|]. exfalso. apply nth_error_None in En. cbn in En. lia. }
    apply (CONT (ms_regs ms2) m' mo' A).
    + rewrite <- (getr_eqv _ _ _ REQ). unfold getr. cbn. exact EA0.
    + eapply regs_preserved_canon. exact REQ.
    + unfold HeapIface.block_range. cbn [hl_img_lo hl_img_hi hl_sptop L0]. unfold IMG_LO, IMG_HI. splits; [exact HA4| exact B5| exact B2| lia| rewrite HCEIL in B4; lia].
    + intros b Hb. rewrite ELB in Hb. apply in_map_iff in Hb as (bb & <- & Hbb). cbn [fst snd blk_iv].
      assert (Hid : blk_id (pb, A, n) <> blk_id bb).
      { pose proof (RHEAP_blocks_nodup_proof _ _ _ HR') as ND'. cbn [map] in ND'. inversion ND' as [|? ? Hni _]; subst.
        intros E. apply Hni. rewrite E. apply in_map. exact Hbb. }
      pose proof (RHEAP_blocks_disjoint_proof _ _ _ (pb, A, n) bb HR' ltac:(left; reflexivity) ltac:(right; exact Hbb) Hid) as D.
      cbn [blk_addr blk_size fst snd] in D. lia.
    + intros i Hi. change (Z_to_bv 64 (A + i)) with (wa (A + i)). apply DEF. exact Hi.
    + rewrite ELB. apply heap_pres_core_of_cj; assumption.
    + exact Emo'.
    + exists RUNp, (set_m cs' s'), (set_live (c :: ld_live L') L'), LBb', (nc + 1).
      destruct HRI' as (Q1 & Q2 & Q3 & Q4 & Q6).
      unfold debit. cbn [fst snd hl_k_per_malloc hl_b_overhead L0].
      splits; try assumption.
      * rewrite ELB. reflexivity.
      * cbn [ld_live set_live]. assert (EL : ld_live L' = ld_live L) by (eapply cpath_live; exact HCP). rewrite EL.
        subst LBb' pb. cbn [map blk_slot fst]. apply perm_skip. exact PL.
      * intros a Ha. pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra.
        rewrite <- (Z_to_bv_bv_unsigned a). change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)).
        rewrite HIMG; [| unfold RCTX in *; lia| unfold RCTX in *; lia| unfold RCTX, RERRNO in *; lia].
        unfold wa. rewrite Z_to_bv_bv_unsigned. apply REPL. exact Ha.
      * subst LBb'. constructor.
        -- split; [cbn; lia| cbn [blk_addr blk_size fst snd]; exact DEF].
        -- apply List.Forall_forall. intros b Hb. pose proof (proj1 (List.Forall_forall _ _) BLK b Hb) as [Sz Def]. split; [exact Sz|].
           intros i Hi. pose proof (RHEAP_block_range_proof s LBb M b HR Hb) as (W1 & _ & _ & W4 & _).
           rewrite (proj1 (HPRES (blk_addr b + i) ltac:(lia) ltac:(right; right; exists b; split; [exact Hb| lia]))). apply Def. exact Hi.
      * lia.
      * unfold KPM in *. change (Z.of_nat EVM) with 8 in *. lia.
      * unfold KPM in *. change (Z.of_nat EVM) with 8 in *. lia.
      * lia.
      * cbn [ps_m set_m]. lia.
      * subst CAPK. unfold KPM in *. change (Z.of_nat EVM) with 8 in *. cbn [Z.of_nat] in Q1. lia.
      * subst CAPB. lia.
Qed.

Lemma repl_cells : forall M : word -> option byte,
  (forall a : word, RCTX + 928 <= bv_unsigned a < RCTX + 936 -> M a = None) ->
  rw_cells rsegs M (RCTX + 928) [C4 (wz 0); C4 (wz 0)].
Proof.
  intros M HN.
  assert (HN' : forall i, 0 <= i < 8 -> M (wa (RCTX + 928 + i)) = None).
  { intros i Hi. apply HN. unfold wa, RCTX in *. rewrite u64_lit by lia. lia. }
  pose proof I as RCTXv. unfold RCTX in HN.
  split; [split; [cbn; repeat split; reflexivity|]|].
  - split; [unfold RCTX; lia|]. split; [cbn; unfold RCTX; lia|]. intros i Hi. cbn in Hi. unfold mrd. rewrite HN' by lia.
    do 8 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
  - split; [unfold RCTX; lia|]. split; [cbn; unfold RCTX; lia|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros i Hi. unfold wview. rewrite HN' by lia.
    assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
    destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; discriminate.
Qed.

Lemma HI0_aligned : aligned_alloc16_spec L0 SCFG HI0.
Proof.
  intros fx R M model LB cr n K HH Hh Hl Hm R10 R11 Hn HCR R4 RET SOK HK0 CONT.
  cbn [hi_heap HI0 hl_tp hl_aligned_alloc hl_segs L0] in *.
  rewrite <- (bv5_lit 10 ltac:(lia)) in R10, CONT. rewrite <- (bv5_lit 11 ltac:(lia)) in R11. rewrite <- (bv5_lit 4 ltac:(lia)) in R4. rewrite <- (bv5_lit 1 ltac:(lia)) in RET, CONT.
  rewrite <- (bv5_lit 2 ltac:(lia)) in SOK, CONT.
  destruct HCR as [CRK CRB]. cbn [hl_k_per_malloc hl_b_overhead L0 fst snd] in CRK, CRB.
  destruct HH as (RUNp & s & L & LBb & nc & HCEIL & ELB & HR & CR & PL & HKL & MI & AUX & REPL & BLK & Hnc & Hk & Hfst & Hsnd & POT & LEN & FA & LIVE).
  pose proof (hi0_nodup_addr s LBb M HR BLK) as NDa. pose proof (RHEAP_slots_nodup s LBb M HR) as NDs.

  destruct (stack_ok_stk HCEIL M _ SOK) as (STK & LO & SPT & SPR). set (sp := bv_unsigned (getr R (Z_to_bv 5 2))) in *.
  destruct (errno_cell_any M) as [errv ERR].
  assert (ERR' : rw_cells rsegs M (bv_unsigned (getr R (Z_to_bv 5 4)) + -164) [C4 errv]).
  { rewrite R4. replace (bv_unsigned (Z_to_bv 64 RATP) + -164) with RERRNO by vmc_refl. exact ERR. }
  pose proof (repl_cells M REPL) as REPL'.

  pose proof (raligned_spec (getr R (Z_to_bv 5 1)) (getr R (Z_to_bv 5 2)) (getr R (Z_to_bv 5 3)) (getr R (Z_to_bv 5 4))
                (getr R (Z_to_bv 5 5)) (getr R (Z_to_bv 5 6)) (getr R (Z_to_bv 5 7)) (getr R (Z_to_bv 5 8)) (getr R (Z_to_bv 5 9))
                (getr R (Z_to_bv 5 10)) (getr R (Z_to_bv 5 11)) (getr R (Z_to_bv 5 12)) (getr R (Z_to_bv 5 13)) (getr R (Z_to_bv 5 14))
                (getr R (Z_to_bv 5 15)) (getr R (Z_to_bv 5 16)) (getr R (Z_to_bv 5 17)) (getr R (Z_to_bv 5 18)) (getr R (Z_to_bv 5 19))
                (getr R (Z_to_bv 5 20)) (getr R (Z_to_bv 5 21)) (getr R (Z_to_bv 5 22)) (getr R (Z_to_bv 5 23)) (getr R (Z_to_bv 5 24))
                (getr R (Z_to_bv 5 25)) (getr R (Z_to_bv 5 26)) (getr R (Z_to_bv 5 27)) (getr R (Z_to_bv 5 28)) (getr R (Z_to_bv 5 29))
                (getr R (Z_to_bv 5 30)) (getr R (Z_to_bv 5 31))
                fp_regs fp_csr M s LBb n (sp - RALIGNED_STACK) sptop errv
                HR AUX SPT STK LO ltac:(lia) ERR' MI R4 REPL' R10 R11 ltac:(lia)) as IMPL.
  change (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with (canon_regs R) in IMPL.
  apply (implM_eqv_transfer rsegs _ _ _ _ (mkst R (Z_to_bv 64 RAA_SYM) M (seg_rom rsegs))) in IMPL; [| apply mkst_eqv_canon].
  unfold raw_malloc in IMPL. apply implM_mget_inv, implM_bind_inv in IMPL.

  set (cs := ps_m s) in *. set (PA := pot cs + AMC).
  assert (HPA : PA <= POTMAX + AMC).
  { subst PA. unfold POTMAX, POT0, AMC, NCMAX, NSLOTS in *. unfold K0, KPM, NCMAX in Hk. unfold KPM in CRK. change (Z.of_nat EVM) with 8 in Hk, CRK. lia. }
  pose proof (CALLB_le n PA ltac:(lia) HPA) as [CB0 CB1].
  set (CAPK := K0 + NSEG - fst cr + KPM). set (CAPB := B0 - snd cr + (n + BOV)).
  assert (HCAPK : CAPK <= CAPKMAX) by (subst CAPK; unfold K0, NSEG, KPM, NCMAX, CAPKMAX; change (Z.of_nat EVM) with 8; lia).
  assert (HCAPB : CAPB <= CAPBMAX) by (subst CAPB; unfold CAPBMAX, B0 in *; lia).
  eapply (embed rsegs SCFG HALLOC RESV IMG_HI CAPK CAPB HCAPK HCAPB (cmalloc cs n) L _ (elen_ok n PA) EVM (CALLB n PA) _ s _ _ model model K
            (cmalloc_contract_proof cs L n CR ltac:(lia))
            (mb_malloc (MBND RUNp) cs L n CR ltac:(lia) (size_overflows_small n ltac:(lia)))
            (fun a len prot flags HE Hf => elen_ok_NMAX n PA a len prot flags Hn HPA HE Hf)
            IMPL HKL).
  - symmetry. apply with_vmmaps_eta.
  - exact Hh. - exact Hl. - exact Hm.
  -
    unfold RI. splits.
    + subst CAPK. unfold KPM. change (Z.of_nat EVM) with 8 in *. lia.
    + exact FA.
    + subst CAPB. lia.
    + exact CB0.
    + exact (KL2_init_sp_window _ _ _ _ _ HKL).
  -
    intros [cs' rc] s' ms' mo' L' HQ HCP HPOST [HSOME HPOT] HK' Emo' HRI' E1 E2 E3. cbn [fst snd] in HSOME, HPOT, HPOST.
    destruct rc as [c|]; [| exfalso; apply HSOME; reflexivity]. clear HSOME.
    cbv beta iota in HQ. apply implM_mupd_inv, implM_ret_inv in HQ. destruct HQ as (ms2 & Hms2 & (ms1 & [POST _] & EQV)).
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & Ems1 &
                      MI' & STK' & ERR2 & AUX' & HPRES & HDEEP & HIMG & _ & _ & (A & junk & EA0 & RBR & HR' & UCH & _)).
    subst ms1. destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems2 REQ].
    assert (Hh' : m_halted mo' = None) by (rewrite Emo', with_vmmaps_halted; exact Hh).
    assert (Hl' : m_vm_lazy mo' = []) by (rewrite Emo', with_vmmaps_lazy'; exact Hl).
    eapply srz_msteps; [exact Hh'| exact Hl'| apply cj_msteps_cat; exact Hms2|].
    rewrite Ems2, (ret_pc_ok _ RET). change (MS ?R' fp_regs ?pc fp_csr None ?mm ?ro) with (mkst R' pc mm ro).
    set (pb := (c, fresh_off cs' c n)) in *.
    set (LBb' := (pb, A, n) :: LBb) in *.
    assert (CR' : creach cs' (set_live (c :: ld_live L') L')).
    { exact (creach_malloc cs L n L' cs' (Some c) CR ltac:(lia) HCP). }
    assert (HK'' : KL2 RESV IMG_HI (set_live (c :: ld_live L') L') (ps_brk (set_m cs' s')) (m_vmmaps mo')).
    { cbn [ps_brk set_m]. apply KL2_set_live. exact HK'. }
    assert (HA4 : 4096 <= A).
    { change A with (blk_addr (pb, A, n)). apply (block_ge_4096 (set_m cs' s') LBb' m' (pb, A, n) HR'). left. reflexivity. }
    pose proof RBR as (B1 & B2 & B3 & B4 & B5). pose proof alloc_ceiling_lt as ACL.
    assert (DEF : forall i, 0 <= i < n -> m' (wa (A + i)) <> None).
    { intros i Hi. destruct UCH as [[WF BA] _]. cbn [cells_wf cell_wf] in WF. destruct WF as [Hlen _].
      destruct BA as (_ & _ & BA). cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
      specialize (BA (Z.to_nat i) ltac:(rewrite Hlen; lia)). rewrite Z2Nat.id in BA by lia.
      rewrite ref_mrd_overlay in BA by (unfold wa; rewrite u64_lit by lia; clear - B5 Hi; lia).
      rewrite BA. destruct (nth_error _ _) eqn:En; [discriminate|]. exfalso. apply nth_error_None in En. cbn in En. lia. }
    apply (CONT (ms_regs ms2) m' mo' A).
    + rewrite <- (getr_eqv _ _ _ REQ). unfold getr. cbn. exact EA0.
    + eapply regs_preserved_canon. exact REQ.
    + unfold HeapIface.block_range. cbn [hl_img_lo hl_img_hi hl_sptop L0]. unfold IMG_LO, IMG_HI. splits; [exact HA4| exact B5| exact B2| lia| rewrite HCEIL in B4; lia].
    + intros b Hb. rewrite ELB in Hb. apply in_map_iff in Hb as (bb & <- & Hbb). cbn [fst snd blk_iv].
      assert (Hid : blk_id (pb, A, n) <> blk_id bb).
      { pose proof (RHEAP_blocks_nodup_proof _ _ _ HR') as ND'. cbn [map] in ND'. inversion ND' as [|? ? Hni _]; subst.
        intros E. apply Hni. rewrite E. apply in_map. exact Hbb. }
      pose proof (RHEAP_blocks_disjoint_proof _ _ _ (pb, A, n) bb HR' ltac:(left; reflexivity) ltac:(right; exact Hbb) Hid) as D.
      cbn [blk_addr blk_size fst snd] in D. lia.
    + intros i Hi. change (Z_to_bv 64 (A + i)) with (wa (A + i)). apply DEF. exact Hi.
    + rewrite ELB. apply heap_pres_core_of_cj; assumption.
    + exact Emo'.
    + exists RUNp, (set_m cs' s'), (set_live (c :: ld_live L') L'), LBb', (nc + 1).
      destruct HRI' as (Q1 & Q2 & Q3 & Q4 & Q6).
      unfold debit. cbn [fst snd hl_k_per_malloc hl_b_overhead L0].
      splits; try assumption.
      * rewrite ELB. reflexivity.
      * cbn [ld_live set_live]. assert (EL : ld_live L' = ld_live L) by (eapply cpath_live; exact HCP). rewrite EL.
        subst LBb' pb. cbn [map blk_slot fst]. apply perm_skip. exact PL.
      * intros a Ha. pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra.
        rewrite <- (Z_to_bv_bv_unsigned a). change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)).
        rewrite HIMG; [| unfold RCTX in *; lia| unfold RCTX in *; lia| unfold RCTX, RERRNO in *; lia].
        unfold wa. rewrite Z_to_bv_bv_unsigned. apply REPL. exact Ha.
      * subst LBb'. constructor.
        -- split; [cbn; lia| cbn [blk_addr blk_size fst snd]; exact DEF].
        -- apply List.Forall_forall. intros b Hb. pose proof (proj1 (List.Forall_forall _ _) BLK b Hb) as [Sz Def]. split; [exact Sz|].
           intros i Hi. pose proof (RHEAP_block_range_proof s LBb M b HR Hb) as (W1 & _ & _ & W4 & _).
           rewrite (proj1 (HPRES (blk_addr b + i) ltac:(lia) ltac:(right; right; exists b; split; [exact Hb| lia]))). apply Def. exact Hi.
      * lia.
      * unfold KPM in *. change (Z.of_nat EVM) with 8 in *. lia.
      * unfold KPM in *. change (Z.of_nat EVM) with 8 in *. lia.
      * lia.
      * cbn [ps_m set_m]. lia.
      * subst CAPK. unfold KPM in *. change (Z.of_nat EVM) with 8 in *. cbn [Z.of_nat] in Q1. lia.
      * subst CAPB. lia.
Qed.

Lemma HI0_free_null : free_null_spec L0 SCFG.
Proof.
  intros fx R M model K Hh Hl R10 RET HK0 CONT. cbn [hl_free hl_segs L0] in *.
  rewrite <- (bv5_lit 10 ltac:(lia)) in R10. rewrite <- (bv5_lit 1 ltac:(lia)) in RET, CONT.
  pose proof (rfree_null_spec (getr R (Z_to_bv 5 1)) (getr R (Z_to_bv 5 2)) (getr R (Z_to_bv 5 3)) (getr R (Z_to_bv 5 4))
                (getr R (Z_to_bv 5 5)) (getr R (Z_to_bv 5 6)) (getr R (Z_to_bv 5 7)) (getr R (Z_to_bv 5 8)) (getr R (Z_to_bv 5 9))
                (getr R (Z_to_bv 5 10)) (getr R (Z_to_bv 5 11)) (getr R (Z_to_bv 5 12)) (getr R (Z_to_bv 5 13)) (getr R (Z_to_bv 5 14))
                (getr R (Z_to_bv 5 15)) (getr R (Z_to_bv 5 16)) (getr R (Z_to_bv 5 17)) (getr R (Z_to_bv 5 18)) (getr R (Z_to_bv 5 19))
                (getr R (Z_to_bv 5 20)) (getr R (Z_to_bv 5 21)) (getr R (Z_to_bv 5 22)) (getr R (Z_to_bv 5 23)) (getr R (Z_to_bv 5 24))
                (getr R (Z_to_bv 5 25)) (getr R (Z_to_bv 5 26)) (getr R (Z_to_bv 5 27)) (getr R (Z_to_bv 5 28)) (getr R (Z_to_bv 5 29))
                (getr R (Z_to_bv 5 30)) (getr R (Z_to_bv 5 31))
                fp_regs fp_csr M R10) as EVT.
  change (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with (canon_regs R) in EVT at 2.
  destruct (evt_eqv_transfer rsegs _ _ (mkst R (Z_to_bv 64 RFREE_SYM) M (seg_rom rsegs)) (mkst_eqv_canon R _ M _) EVT)
    as (ms1 & ms1' & -> & EQV & Hms).
  eapply srz_msteps; [exact Hh| exact Hl| exact Hms|].
  destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [-> REQ].
  rewrite (ret_pc_ok _ RET). change (MS ?R' fp_regs ?pc fp_csr None ?mm ?ro) with (mkst R' pc mm ro).
  apply CONT. eapply regs_preserved_canon. exact REQ.
Qed.

Theorem HI0_ok : heap_iface_ok L0 SCFG HI0.
Proof.
  constructor.
  - exact HI0_malloc.
  - exact HI0_aligned.
  - exact HI0_free.
  - exact HI0_free_null.
  - exact HI0_frame.
  - exact HI0_wf.
  - exact HI0_perm.
Qed.

End DELIVERABLES.

Lemma reserved_top_RESV : reserved_top RESV = IMG_HI.
Proof. vmc_refl. Qed.

Theorem HI0_init : forall (M : word -> option byte) (lim : Z) (VM : VmMaps),
  init_statics0 M -> init_vm L0 lim VM -> hi_heap HI0 [] (hl_K0 L0, hl_B0 L0) M VM.
Proof.
  intros M lim VM (NONE & NL & PS & GOT & (canary & Hcan & GUARD)
                   & (av & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & rnd & secret & AUXC & AVL & RND & Bav & Hav & Brnd & Hrnd
                      & X3 & X4 & X5 & XHW & X6 & X11 & X12 & X23 & Xr & Xs) & MI)
         (brk0 & mbase & isp & -> & VB & VMB & VSP & Hisp).
  cbn [hi_heap HI0 hl_K0 hl_B0 hl_segs hl_sptop L0] in *.
  destruct VB as (VB1 & VB2 & VB3). fold RESV in VB1, VB2 |- *. rewrite reserved_top_RESV in VB1, VB2.
  destruct VSP as (SP1 & SP2 & SP3). rewrite Hisp in SP1, SP2, SP3. unfold sp_window_lo in SP1. unfold sp_window_hi in SP2.

  assert (Hrange : CEIL_LO <= sptop - 2 ^ 23 <= CEIL_HI) by (unfold CEIL_LO, CEIL_HI; lia).
  set (R0 := mkRunP (sptop - 2 ^ 23) Hrange secret Xs canary Hcan).
  assert (HCEIL : @alloc_ceiling R0 = sptop - 2 ^ 23) by reflexivity.
  exists R0.
  destruct (@RHEAP_init_proof R0 M (Z_to_bv 64 av) ltac:(intros a Ha; apply NONE; lia) NL AUXC PS GOT GUARD MI) as [HR _].
  exists (ps_init (reservedZ rsegs)), (led_init (reservedZ rsegs)), [], 0.
  assert (ER : reservedZ rsegs = map wwZ RESV) by reflexivity.
  splits.
  - exact HCEIL.
  - reflexivity.
  - exact HR.
  - apply creach_init.
  - apply Permutation_refl.
  - unfold ps_init; cbn [ps_brk].
    constructor; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live led_init].
    + split; [intros e []| constructor].
    + intros e [].
    + exact ER.
    + reflexivity.
    + intros e He. enough (ehi e <= IMG_HI) by lia.
      rewrite RESV_eq in He. unfold ehi.
      destruct He as [<-|[<-|[<-|[<-|[]]]]]; vm_compute; discriminate.
    + rewrite HCEIL. unfold brk_aslr_max, IMG_HI, page_size, PGSZ, CEIL_LO in *. splits; first [lia| exact VB3].
    + intros b l [].
    + intros b l k [].
    + constructor.
    + intros b l H. discriminate.
    + split; reflexivity.
    + rewrite HCEIL, Hisp. lia.
  - exact MI.
  -
    exists av, x3, x4, x5, hw, x6, x11, x12, x23, rnd. unfold RAUXV_CELL, auxv_list, wz. rewrite HCEIL.
    change (@secret_val R0) with secret. splits; first [exact AUXC| exact AVL| exact RND| lia].
  - intros a Ha. apply NONE. unfold RCTX in Ha. lia.
  - constructor.
  - lia.
  - cbn [fst snd]. unfold K0, KPM, NCMAX. change (Z.of_nat EVM) with 8. lia.
  - cbn [fst snd]. unfold K0, KPM, NCMAX. change (Z.of_nat EVM) with 8. lia.
  - cbn [fst snd]. unfold B0. lia.
  - unfold ps_init; cbn [ps_m]. rewrite pot_init. lia.
  - cbn [vm_reserved vm_maps fst snd]. rewrite app_nil_r, RESV_eq. cbn [length]. unfold NSEG. lia.
  - cbn [vm_reserved vm_maps]. rewrite app_nil_r, RESV_eq. unfold NMAX.
    repeat (apply Forall_cons; [cbn [snd]; vm_compute; discriminate|]). apply Forall_nil.
  - cbn [vm_maps live_bytes fst snd]. lia.
Qed.

End LAYOUT.
