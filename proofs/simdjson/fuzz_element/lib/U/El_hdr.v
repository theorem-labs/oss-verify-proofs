(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun STree Malloc Monad Stdio SjModel AtpModel ElModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit F_memcpy Atp_defs Atp_h_defs Atp_h_push Atp_h_find Atp_h_split Atp_h_splitinto El_empl El_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Sj_stage1_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition el_els (D : Z) (d : list Z) : list (Z * Z) :=
  map (pview (D + 10)) (poffs (el_rem d)) ++ repeat (0, 0) (el_P d - length (poffs (el_rem d))).

Definition vec_post (sp0 : Z) (gp s9 s10 s11 : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 ra : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (lo B D : Z) (d : list Z) (init : bool) (m : mem)
    (v : @vec bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 xs0 xs1 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs7 xs8 t3 t4 t5 t6 m' (errv' : word) (A cap : Z) (b : bptr) (jr : list byte)
                    (j0 c8 c16 c24 c32 c40 j48 jel jpa j416 j441 : list byte) (sel : Z),
    ms' = MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 xs0 xs1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5
                  (Z_to_bv 64 (el_action d)) xs7 xs8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3c144) fc None m' (seg_rom usegs)
    /\ v = (cap, Z.of_nat (el_P d), Some b) /\ cap < 2^26
    /\ mem_inv usegs m' /\ stk usegs m' lo sp0 /\ rw_cells usegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' ((b, A, 16 * cap) :: LB) m'
    /\ vrep m' (sp0 + 392) A v (el_els D d) jr
    /\ lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW] m m' /\ sj_statics m' init /\ payload_ok m' LB D d
    /\ rw_cells usegs m' sp0 [CB 8 j0]
    /\ rw_cells usegs m' (sp0 + 8) [CB 8 c8; CB 8 c16; CB 8 c24; CB 8 c32; CB 8 c40]
    /\ rw_cells usegs m' (sp0 + 48) [CB 248 j48]
    /\ rw_cells usegs m' (sp0 + 296) [CB 16 jel]
    /\ rw_cells usegs m' (sp0 + 312) [CB 80 jpa]
    /\ rw_cells usegs m' (sp0 + 416) [CB 4 j416; C4 (Z_to_bv 64 sel)] /\ 0 <= sel < 8 /\ (el_fd_ok d = true -> sel = el_sel d)
    /\ rw_cells usegs m' (sp0 + 424) [C8 (Z_to_bv 64 (if el_fd_ok d then D + zlength d else 0)); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 j441]
    /\ rw_cells usegs m' (sp0 + 448) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma rw_cells_split_at1 : forall m A cs n, rw_cells usegs m A cs ->
  rw_cells usegs m A (firstn n cs) /\ rw_cells usegs m (A + Z.of_nat (cells_size (firstn n cs))) (skipn n cs).
Proof. intros m A cs n H. rewrite <- (firstn_skipn n cs) in H. apply Sj_stage1_kit.rw_cells_app in H. exact H. Qed.

Lemma payload_ok_rem : forall m LB D d, payload_ok m LB D d -> el_fd_ok d = true -> payload_ok m LB (D + 10) (el_rem d).
Proof.
  intros m LB D d (PB & PF & D0 & DN & DL & PIN) FD. pose proof (el_rem_fd d FD) as [ER EL]. rewrite ER in *.
  unfold el_fd_ok, EL_HDR in FD. apply Z.leb_le in FD.
  split; [| split; [| split; [lia| split; [unfold zlength in *; rewrite length_skipn; lia| split; [unfold zlength in *; rewrite length_skipn; lia|]]]]].
  - unfold to_bytes in *. rewrite <- (firstn_skipn 10 d) in PB. rewrite map_app in PB. apply bytes_at_app in PB as [_ PB].
    rewrite length_map, length_firstn in PB. unfold zlength in FD. replace (D + Z.of_nat (Init.Nat.min 10 (length d))) with (D + 10) in PB by lia. exact PB.
  - rewrite <- (firstn_skipn 10 d) in PF. apply Forall_app in PF. tauto.
  - destruct PIN as [E0|(b & Hb & H1 & H2)]; [left; rewrite E0; reflexivity| right]. exists b. split; [exact Hb|].
    unfold zlength in *. rewrite length_skipn. lia.
Qed.

Definition hdr_post (usp : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra : word) (F : bvmap 5 word) (fc : bv 32) (lo D : Z) (d : list Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 xs0 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 c8 c16 c24 c32 c40 j48 jel jpa jv j416 jfd8 j441 : list byte) (sel : Z),
    let sp0 := usp + -528 in
    ms' = MS (mkR ra (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 xs0 s1
                  a0 (Z_to_bv 64 (if el_fd_ok d then zlength d - 10 else 0)) a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 (Z_to_bv 64 (el_action d)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3c114) fc None m' (seg_rom usegs)
    /\ munch [(usp - 528, usp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo sp0
    /\ rw_cells usegs m' sp0 [CB 8 j0]
    /\ rw_cells usegs m' (sp0 + 8) [CB 8 c8; CB 8 c16; CB 8 c24; CB 8 c32; CB 8 c40]
    /\ rw_cells usegs m' (sp0 + 48) [CB 248 j48]
    /\ rw_cells usegs m' (sp0 + 296) [CB 16 jel]
    /\ rw_cells usegs m' (sp0 + 312) [CB 80 jpa]
    /\ rw_cells usegs m' (sp0 + 392) [CB 24 jv]
    /\ rw_cells usegs m' (sp0 + 416) [CB 4 j416; C4 (Z_to_bv 64 sel)] /\ 0 <= sel < 8 /\ (el_fd_ok d = true -> sel = el_sel d)
    /\ rw_cells usegs m' (sp0 + 424) [C8 (Z_to_bv 64 (if el_fd_ok d then D + 10 else 0)); CB 8 jfd8]
    /\ rw_cells usegs m' (sp0 + 440) [C1 (Z_to_bv 8 0); CB 7 j441]
    /\ rw_cells usegs m' (sp0 + 448) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma el_action_byte : forall d b, 0 <= b < 256 -> nth 0 d 0 = b -> d <> [] -> el_action d = Z.land b 31.
Proof.
  intros [|x d] b Hb E NE; [congruence|]. cbn in E |- *. subst x. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma el_sel_byte : forall d b, 0 <= b < 256 -> nth 1 d 0 = b -> (2 <= length d)%nat -> el_sel d = Z.land b 7.
Proof.
  intros [|x [|y d]] b Hb E L; cbn in L; try lia. cbn in E |- *. subst y. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma hdr_spec : forall (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (D : Z) (d : list Z) (lo : Z),
  RHEAP s LB m -> stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 528 -> bv_unsigned sp < 2^63 ->
  mem_inv usegs m -> payload_ok m LB D d ->
  evt usegs (hdr_post (bv_unsigned sp) gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra F fc lo D d m)
    (MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 (zlength d)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 EL_LFTOI) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros HEAP ST CEIL GLO LO SP63 MI PL.
  unfold EL_LFTOI, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (ESP : sp = Z_to_bv 64 (bv_unsigned sp)) by (symmetry; apply Z_to_bv_bv_unsigned).
  set (usp := bv_unsigned sp) in *.
  pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof PL as (PB & PRNG & D0 & DN & DLEN & PIN).
  assert (ZD : zlength d = Z.of_nat (length d)) by reflexivity. pose proof DLEN as DLEN'. change (2^26) with 67108864 in DLEN'.
  assert (LBLEN : length (to_bytes d) = length d) by apply to_bytes_length.
  assert (DR : d = [] \/ D + zlength d <= alloc_ceiling).
  { destruct PIN as [E0|(b0 & Hb & Hb1 & Hb2)]; [left; exact E0| right]. pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & R4 & _).
    unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in R4. lia. }
  pose proof (munch_refl [(usp - 528, usp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  rewrite ESP. hide PB.
  step. carve_frame 528%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 528 junk [] [8; 8;8;8;8;8; 248; 16; 80; 24; 4; 4; 8;8; 1; 7; 8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app] in FR.

  do 10 step. hstep.

  destruct (rw_cells_split_at1 _ _ _ 1%nat FR) as [J0 R1]. cbn [firstn skipn cells_size csize Nat.add] in J0, R1.
  destruct (rw_cells_split_at1 _ _ _ 5%nat R1) as [SCR R2]. cbn [firstn skipn cells_size csize Nat.add] in SCR, R2.
  destruct (rw_cells_split_at1 _ _ _ 1%nat R2) as [J48 R3]. cbn [firstn skipn cells_size csize Nat.add] in J48, R3.
  destruct (rw_cells_split_at1 _ _ _ 1%nat R3) as [JEL R4]. cbn [firstn skipn cells_size csize Nat.add] in JEL, R4.
  destruct (rw_cells_split_at1 _ _ _ 1%nat R4) as [JPA R5]. cbn [firstn skipn cells_size csize Nat.add] in JPA, R5.
  destruct (rw_cells_split_at1 _ _ _ 1%nat R5) as [JV R6]. cbn [firstn skipn cells_size csize Nat.add] in JV, R6.
  destruct (rw_cells_split_at1 _ _ _ 2%nat R6) as [XSEL R7]. cbn [firstn skipn cells_size csize Nat.add] in XSEL, R7.
  destruct (rw_cells_split_at1 _ _ _ 2%nat R7) as [XFD R8]. cbn [firstn skipn cells_size csize Nat.add] in XFD, R8.
  destruct (rw_cells_split_at1 _ _ _ 2%nat R8) as [XPAD SAVE]. cbn [firstn skipn cells_size csize Nat.add] in XPAD, SAVE.
  clear FR R1 R2 R3 R4 R5 R6 R7 R8.
  remember (usp + -528) as sp0 eqn:Esp0.
  replace (sp0 + Z.of_nat 8) with (sp0 + 8) in SCR by lia.
  replace (sp0 + Z.of_nat 8 + Z.of_nat 40) with (sp0 + 48) in J48 by lia.
  replace (sp0 + Z.of_nat 8 + Z.of_nat 40 + Z.of_nat 248) with (sp0 + 296) in JEL by lia.
  replace (sp0 + Z.of_nat 8 + Z.of_nat 40 + Z.of_nat 248 + Z.of_nat 16) with (sp0 + 312) in JPA by lia.
  replace (sp0 + Z.of_nat 8 + Z.of_nat 40 + Z.of_nat 248 + Z.of_nat 16 + Z.of_nat 80) with (sp0 + 392) in JV by lia.
  replace (sp0 + Z.of_nat 8 + Z.of_nat 40 + Z.of_nat 248 + Z.of_nat 16 + Z.of_nat 80 + Z.of_nat 24) with (sp0 + 416) in XSEL by lia.
  replace (sp0 + Z.of_nat 8 + Z.of_nat 40 + Z.of_nat 248 + Z.of_nat 16 + Z.of_nat 80 + Z.of_nat 24 + Z.of_nat 8) with (sp0 + 424) in XFD by lia.
  replace (sp0 + Z.of_nat 8 + Z.of_nat 40 + Z.of_nat 248 + Z.of_nat 16 + Z.of_nat 80 + Z.of_nat 24 + Z.of_nat 8 + Z.of_nat 16) with (sp0 + 440) in XPAD by lia.
  replace (sp0 + Z.of_nat 8 + Z.of_nat 40 + Z.of_nat 248 + Z.of_nat 16 + Z.of_nat 80 + Z.of_nat 24 + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 8) with (sp0 + 448) in SAVE by lia.
  Ltac fin_hdr FDF ACT := anorm; apply evt_done; unfold hdr_post; cbv zeta; rewrite FDF, ACT; do 15 eexists; eexists; do 13 eexists; eexists;
    split; [cbv delta [mkR]; reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
    repeat (split; [first [eassumption | lia | (intros; first [assumption | discriminate])]|]); first [eassumption | lia].
  unhide PB.
  assert (RDX : forall mx, munch [(sp0, usp)] m mx -> forall n : nat, (n < length d)%nat ->
                 ov_read_bytes usegs mx (wa (D + Z.of_nat n)) 1 = Some [Z_to_bv 8 (nth n d 0)]).
  { intros mx MUx n Hn.
    assert (PB0 : bytes_at usegs mx D (to_bytes d)).
    { destruct DR as [E0|DR'].
      - exfalso. rewrite E0 in Hn. cbn in Hn. lia.
      - eapply bytes_at_transport; [exact PB| exact MUx|]. cbn [disjoint_from]. rewrite LBLEN. unfold zlength in DR'. split; [lia| exact I]. }
    rewrite <- (Nat2Z.id n) at 2. apply (zbytes_read1 mx D d (Z.of_nat n)); [exact PB0| unfold zlength; lia]. }
  clear PB.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (RDX mx MU) as RD end.

  zstep. if_cases HK0; zify_cond HK0.
  -
    assert (Ed : d = []) by (destruct d; [reflexivity| exfalso; rewrite ZD in HK0; cbn [length] in HK0; lia]).
    assert (FDF : el_fd_ok d = false) by (rewrite Ed; reflexivity). assert (ACT : el_action d = 0) by (rewrite Ed; reflexivity).
    do 6 hstep.
    destruct (rw_cells_split_at1 _ _ _ 1%nat XFD) as [XFD1 XFD2]. cbn [firstn skipn cells_size csize Nat.add] in XFD1, XFD2.
    destruct (rw_cells_forget _ _ _ _ XFD2) as [jfx XFD3]. cbn [cells_size csize Nat.add] in XFD3.
    pose proof (rw_cells_join _ _ _ _ _ XFD1 XFD3 ltac:(cbn [cells_size csize Nat.add]; lia)) as XFD4. cbn [app] in XFD4.
    clear XFD XFD1 XFD2 XFD3. subst sp0. fin_hdr FDF ACT.
  -
    assert (NE : d <> []) by (intros E0; rewrite E0 in HK0; apply HK0; reflexivity).
    pose proof (RD 0%nat ltac:(rewrite ZD in HK0; lia)) as RD0. rewrite Z.add_0_r in RD0.
    assert (B0 : 0 <= nth 0 d 0 < 256) by (apply Forall_nth_Z; [exact PRNG| rewrite ZD in HK0; lia]).
    assert (ACT : el_action d = Z.land (nth 0 d 0) 31) by (apply el_action_byte; [exact B0| reflexivity| exact NE]).
    hstep.
    zstep. if_cases HG1; zify_cond HG1; [exfalso; destruct DR as [E0|DR']; [exact (NE E0)| lia]|].
    do 3 hstep.
    zstep. if_cases HK1; zify_cond HK1.
    +
      assert (FDF : el_fd_ok d = false) by (unfold el_fd_ok, EL_HDR; apply Z.leb_gt; lia).
      do 4 hstep. subst sp0. fin_hdr FDF ACT.
    +
      do 2 hstep.
      zstep. if_cases HG2; zify_cond HG2; [exfalso; destruct DR as [E0|DR']; [exact (NE E0)| lia]|].
      pose proof (RD 1%nat ltac:(rewrite ZD in HK0, HK1; lia)) as RD1. change (Z.of_nat 1) with 1 in RD1.
      assert (B1 : 0 <= nth 1 d 0 < 256) by (apply Forall_nth_Z; [exact PRNG| rewrite ZD in HK0, HK1; unfold zlength in *; lia]).
      pose proof (land7_range (nth 1 d 0) ltac:(lia)) as SEL7.
      do 5 hstep.
      zstep. if_cases HK2; zify_cond HK2.
      *
        assert (FDF : el_fd_ok d = false) by (unfold el_fd_ok, EL_HDR; apply Z.leb_gt; lia).
        do 3 hstep. rewrite (a_zxb_small (nth 1 d 0)), a_u64_small in XSEL by lia. subst sp0. fin_hdr FDF ACT.
      *
        assert (FDT : el_fd_ok d = true) by (unfold el_fd_ok, EL_HDR; apply Z.leb_le; lia).
        clear RD RD0 RD1. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (RDX mx MU) as RD end.
        do 2 hstep.
        zstep. if_cases HG3; zify_cond HG3; [exfalso; destruct DR as [E0|DR']; [exact (NE E0)| lia]|].
        pose proof (RD 2%nat ltac:(rewrite ZD in HK2; lia)) as RD2. change (Z.of_nat 2) with 2 in RD2. pose proof (RD 3%nat ltac:(rewrite ZD in HK2; lia)) as RD3. change (Z.of_nat 3) with 3 in RD3.
        pose proof (RD 4%nat ltac:(rewrite ZD in HK2; lia)) as RD4. change (Z.of_nat 4) with 4 in RD4. pose proof (RD 5%nat ltac:(rewrite ZD in HK2; lia)) as RD5. change (Z.of_nat 5) with 5 in RD5.
        assert (B2 : forall k, (k < 10)%nat -> 0 <= nth k d 0 < 256) by (intros k Hk; apply Forall_nth_Z; [exact PRNG| rewrite ZD in HK2; unfold zlength in *; lia]).
        pose proof (B2 2%nat ltac:(lia)). pose proof (B2 3%nat ltac:(lia)). pose proof (B2 4%nat ltac:(lia)). pose proof (B2 5%nat ltac:(lia)).
        pose proof (B2 6%nat ltac:(lia)). pose proof (B2 7%nat ltac:(lia)). pose proof (B2 8%nat ltac:(lia)). pose proof (B2 9%nat ltac:(lia)).
        assert (SELD : Z.land (nth 1 d 0) 7 = el_sel d) by (symmetry; apply el_sel_byte; [exact B1| reflexivity| rewrite ZD in HK2; lia]).
        do 10 hstep.
        clear RD RD2 RD3 RD4 RD5. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (RDX mx MU) as RD end.
        pose proof (RD 6%nat ltac:(rewrite ZD in HK2; lia)) as RD6. change (Z.of_nat 6) with 6 in RD6. pose proof (RD 7%nat ltac:(rewrite ZD in HK2; lia)) as RD7. change (Z.of_nat 7) with 7 in RD7.
        pose proof (RD 8%nat ltac:(rewrite ZD in HK2; lia)) as RD8. change (Z.of_nat 8) with 8 in RD8. pose proof (RD 9%nat ltac:(rewrite ZD in HK2; lia)) as RD9. change (Z.of_nat 9) with 9 in RD9.
        do 16 hstep. replace (zlength d + -10) with (zlength d - 10) by lia.
        rewrite (a_zxb_small (nth 1 d 0)), a_u64_small in XSEL by lia. subst sp0. fin_hdr FDT ACT.
Qed.
End WithCeiling0.
