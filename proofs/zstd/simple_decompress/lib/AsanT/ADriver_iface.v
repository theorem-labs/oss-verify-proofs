(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad STree Stdio Driver Adapter AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto AMalloc_iface AProg_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import F_syscalls StdioFiles Stdio_kit MonadF AExit F_module_dtor.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition AMAIN_PC : Z := 0x82588.           (* [comment removed for export] *)
Definition ASTAGE2_RET : Z := 0xb6724.       (* [comment removed for export] *)
Definition AEXIT_PC : Z := 0xb6e24.          (* [comment removed for export] *)
Definition ATARGET_ALLOC_INIT : Z := 0x8284c.
Definition ATARGET_ALLOC_COUNT : Z := 0x82850.
Definition ATARGET_RUN : Z := 0x82858.          (* [comment removed for export] *)
Definition ATRUN_MALLOC_RA : Z := 0x828bc.      (* [comment removed for export] *)
Definition ATRUN_FREE_RA : Z := 0x82950.        (* [comment removed for export] *)
Definition AAEF_GUARD : Z := 0x829b0.           (* [comment removed for export] *)
Definition AEMIT_PRINTF : Z := 0x829e0.
Definition AFUZZ_INIT : Z := 0.               (* [comment removed for export] *)
Definition AGOT_FUZZ_INIT : Z := 0xc7f70.    (* [comment removed for export] *)
Definition AINIT_FLAG : Z := 0x602350.        (* [comment removed for export] *)
Definition AAEF_INCB : Z := 0x602354.         (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AATEXIT : Z := 0x622d00.
Definition AATEXIT_CALL : Z := 0xb6dd0.        (* [comment removed for export] *)
Definition ACOV_HOOK : Z := 0x71fe8.           (* [comment removed for export] *)
Definition AAEF_ARGC : Z := 0xcb8c8.         (* [comment removed for export] *)
Definition AGOT_STDERRP : Z := 0xc7f68.      (* [comment removed for export] *)
Definition ASTDERRP : Z := 0xc7200.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ASTAGE : Z := 0x5f2350.
Definition astage_len_sig : { n : nat | Z.of_nat n = 65536 }.
Proof. exists (Z.to_nat 65536). apply Z2Nat.id. apply Z.leb_le. reflexivity. Qed.
Definition ASTAGE_LEN : nat := proj1_sig astage_len_sig.
Lemma ASTAGE_LEN_Z : Z.of_nat ASTAGE_LEN = 65536.
Proof. exact (proj2_sig astage_len_sig). Qed.
Definition RSTG : region := mkRegion 0x5f2350 0x602350 0x5f2340 0x602380.
(* [comment removed for export] *)
Definition ASTG (m : amem) : Prop := exists sj, rw_cells bsegs m ASTAGE [CB ASTAGE_LEN sj].

(* [comment removed for export] *)
Definition ATARGET_RUN_STACK : Z := 80 + AHARNESS_STACK.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition RFMT : region := mkRegion 0x10000 0x210c0 0x10000 0x210c0.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition rodata_sh0 (m : amem) : Prop :=
  shadow_bytes m (shad 0x10000) (shad 0x210c0) (fun _ => 0) /\ wr_at bsegs m (shad 0x10000) (shad 0x210c0 - shad 0x10000).

Lemma rodata_sh0_rclean : forall m, rodata_sh0 m -> rclean m RFMT.
Proof.
  intros m [SB WR]. unfold rclean, RFMT, shclean; cbn [r_lo r_hi r_rlo r_rhi]. split; [|lia].
  split; [| split; [unfold hull64, KEND; lia| split; [eapply wr_at_sub; [exact WR| rewrite !shad_div; lia| rewrite !shad_div; lia| rewrite !shad_div; lia]
                                               | unfold app_blk, KLOW; lia]]].
  destruct SB as (_ & _ & SB). split; [lia|]. split; [lia|].
  intros G Hlt Hlo Hhi. exists (Z_to_bv 8 0). split.
  - apply SB. rewrite !shad_div. change ASHOFF with 0x7fff8000. lia.
  - left. reflexivity.
Qed.

Lemma rodata_sh0_fmt : forall m A n, rodata_sh0 m -> 0x10000 + 64 <= A -> 0 <= n -> A + n + 64 <= 0x210c0 ->
  shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0).
Proof.
  intros m A n [SB _] H1 H2 H3. eapply shadow_bytes_sub; [exact SB | |]; apply shad_mono; lia.
Qed.

Lemma rodata_sh0_frame : forall W m m', rodata_sh0 m -> munch W m m' -> wmono bsegs m m' -> appW W -> rodata_sh0 m'.
Proof.
  intros W m m' [SB WR] MU WM AW. split.
  - eapply shadow_bytes_munch; [exact SB | exact MU |].
    pose proof (appW_shadow_disjoint W 0x10000 0x210c0 AW ltac:(lia) ltac:(unfold KEND; lia)) as D. exact D.
  - eapply wr_at_transport; [exact WR | exact WM].
Qed.

(* [comment removed for export] *)
Definition rrng_fmt (RNG : footprint) : Prop := rrng RNG RFMT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition drv_img_ranges : list (Z * Z) :=
  [(0x10000, 0x210c0);                      (* [comment removed for export] *)
   (0x602350, 0x602380);                    (* [comment removed for export] *)
   (RSTDERR, RSTDERR + 232); (RSTDOUT, RSTDOUT + 232); (0xcb9f0, 0xcb9f8); (0xcbae0, 0xcbae8); (0xcbbd0, 0xcbbd8);
   (0x623380, 0x623800);                    (* [comment removed for export] *)
   (0x602c08, 0x602c10); (0x622cf0, 0x622cf8); (0x622d00, 0x622d30); (0x622e20, 0x622e30); (0x622f20, 0x622f28);
   (0x622f40, 0x622f50);                    (* [comment removed for export] *)
   (0xcbc00, 0xcc640); (0xcc640, 0xcc648); (0xcc690, 0xcc691); (0xc9050, 0xc9058);
                                            (* [comment removed for export] *)
   (0x161ba0, 0x161ba1); (0xcd510, 0xcd514); (0xcd5b0, 0xcd5b8); (* [comment removed for export] *)
   (0x21100, 0x229a0);                      (* [comment removed for export] *)
   (0xcbae8, 0xcbb78);                    (* [comment removed for export] *)
   (0x5f2340, 0x602380)]%Z.                (* [comment removed for export] *)

(* [comment removed for export] *)
Definition cli_img_ranges : list (Z * Z) := [(0x602380, 0x6023a0); (0x229a0, 0x229c0)].      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aat_exit (code : Z) (s : APS) (RNG : footprint) (ms : machine_state) : Prop :=
  exists (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (lo t : Z) (reg : bool) (cdt thr sec : byte) (tm1 dso guard : word),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AEXIT_PC) fc None m (seg_rom bsegs)
    /\ mdtor_pre m
    /\ stk bsegs m lo (bv_unsigned sp)
    /\ rw_cells bsegs m 0x602c08 [C4 (Z_to_bv 64 t)]
    /\ rw_cells bsegs m 0x622f20 [C4 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m 0x622f40 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
    /\ rw_cells bsegs m 0x622d00 [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m 0x622d04 [C4 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m 0x622d08 [C4 (Z_to_bv 64 (if reg then 2 else 1))]        (* [comment removed for export] *)
    /\ rw_cells bsegs m 0x622d10 [C8 (Z_to_bv 64 0x622d18)]
    /\ rw_cells bsegs m 0x622d18 [C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m 0x622d20 [C8 (Z_to_bv 64 0xb6dd0)]
    /\ rw_cells bsegs m 0x622e20 [C8 (Z_to_bv 64 0x71fe8)]
    /\ (reg = true -> rw_cells bsegs m 0x622d28 [C8 (Z_to_bv 64 0xb6dd0)] /\ rw_cells bsegs m 0x622e28 [C8 (Z_to_bv 64 0x829b0)]
                   /\ rw_cells bsegs m 0x602354 [C1 (Z_to_bv 8 0)])       (* [comment removed for export] *)
    /\ rw_cells bsegs m 0x161ba0 [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m 0xc8010 [C8 (Z_to_bv 64 0xc6da0); C8 (Z_to_bv 64 0xc6d90)]
    /\ rw_cells bsegs m 0xc6d90 [C8 (Z_to_bv 64 0x82c6c); C8 (Z_to_bv 64 0x32980)]
    /\ rw_cells bsegs m 0xcc690 [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m 0xc72d8 [C8 (Z_to_bv 64 0xb6d08); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m 0xc9050 [C8 dso]
    /\ rw_cells bsegs m 0x6233a8 [C8 (Z_to_bv 64 0)] /\ rw_cells bsegs m 0xcbbd0 [C8 (Z_to_bv 64 RSTDIN)] /\ rw_cells bsegs m RSTDIN stdin_cells
    /\ rw_cells bsegs m 0xcbae0 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells bsegs m 0xcb9f0 [C8 (Z_to_bv 64 RSTDERR)]
    /\ stdout_file m (aps_so s) /\ stderr_file m
    /\ rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells bsegs m ssp_guard [C8 guard]
    /\ mem_inv bsegs m
    /\ tp = Z_to_bv 64 RTP /\ a0 = Z_to_bv 64 code
    /\ 0 < t < 4194304 /\ lo <= bv_unsigned sp - 48 - MDTOR_DEPTH /\ KHIGH <= lo
    /\ rng RNG lo (bv_unsigned sp - lo) /\ rng_aimg RNG /\ Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W /\ rng0 RNG
    /\ bv_unsigned sp < 2^47.                                    (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma aps_get_set' : forall (s : APS) so, aps_so (aset_so so s) = so. Proof. reflexivity. Qed.
Lemma aps_set_set' : forall (s : APS) so so', aset_so so' (aset_so so s) = aset_so so' s. Proof. reflexivity. Qed.
Lemma aps_set_get' : forall (s : APS), aset_so (aps_so s) s = s. Proof. intros [a b]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma aexit_from_aat_exit : forall code (s : APS) RNG ms (Q : Empty_set -> APS -> footprint -> machine_state -> Prop),
  aat_exit code s RNG ms -> implMA RNG (exit_model (ioA AAllocAsan) code) s Q ms.
Proof.
  intros code s RNG ms Q H.
  destruct H as (ra & sp & gp & tp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 &
                 s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & lo & t & reg &
                 cdt & thr & sec & tm1 & dso & guard & -> & H).
  destruct H as (PRE & ST & TID & EXL & LIBC & FIN & ALK & SLOT & HEAD & NEXT & F0 & A0 & REGC & COV & GF & FA & FINZ & GCX & DSO
                 & OFL & SIN & SINF & SOU & SEU & SOF & SEF & GG & GU & MI & Htp & Ha0 & Ht & LO & KH & RSTK & RIMG & RW & RG0 & SP47).
  unfold implMA. change (ioA AAllocAsan) with (io_S (St := APS) aps_so aset_so).
  eapply implF_epost_mono.
  - eapply (aexit_spec_closed aps_so aset_so aps_get_set' aps_set_set' aps_set_get' RNG s (fun (e : Empty_set) _ _ => match e with end));
      first [exact PRE | exact ST | exact SLOT | exact REGC | exact MI | exact Htp | exact Ha0 | exact Ht | exact LO | exact KH | exact RSTK | exact RW | exact RG0 | exact SP47
            | eassumption ].
  - intros [e ?] RNG' ms'. destruct e.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma atarget_alloc_init_spec : forall RNG (bitmap : Z) (s : APS)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem),
  implMA RNG (alloc_initA AAllocAsan bitmap) s
        (fun _ s' RNG' ms' => RNG' = RNG /\ s' = s /\
           ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m (seg_rom bsegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ATARGET_ALLOC_INIT) fc None m (seg_rom bsegs)).
Proof.
  intros. unfold alloc_initA, Adapter.target_alloc_init, ATARGET_ALLOC_INIT. apply implMA_ret.
  step. apply evtF_done. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma atarget_alloc_count_spec : forall RNG (s : APS)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem),
  implMA RNG (alloc_countA AAllocAsan) s
        (fun r s' RNG' ms' => RNG' = RNG /\ s' = s /\ r = 0 /\
           ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m (seg_rom bsegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ATARGET_ALLOC_COUNT) fc None m (seg_rom bsegs)).
Proof.
  intros. unfold alloc_countA, Adapter.target_alloc_count, ATARGET_ALLOC_COUNT. apply implMA_ret.
  step. step. apply evtF_done. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DrvStmts.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).

  (* [comment removed for export] *)

  Definition dmalloc_post (L : alayout) (RNG : footprint)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : astate) (LB : list ablock) (n lo : Z) (m : amem)
      (r : astate * option AsanCtrl.aptr) (RNG' : footprint) : machine_state -> Prop :=
    fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ aheap_pres CI LB (bv_unsigned sp) m m' /\ astk_shadow_pres (bv_unsigned sp) m m'
      /\ match snd r with
         | None => False
         | Some p => exists A junk,
             a0 = Z_to_bv 64 A /\ ablock_range A n
             /\ AHEAP AI L RNG' (fst r) (HB p A n :: LB) m'
             /\ rw_cells bsegs m' A [CB (Z.to_nat n) junk]
             /\ rng RNG' A n /\ rng RNG' (shad A) (shlen (n + 7))
             /\ (is_primary n = false -> A = AsanCtrl.aptr_addr (fst r) p)
         end.

  Definition dmalloc_stmt : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo : Z) (RESV : list (Z * Z)),
      AHEAP AI L RNG st LB m -> mem_inv bsegs m ->
      stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
      tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
      bv_unsigned s0 <= bv_unsigned sp -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC -> bv_unsigned sp mod 16 = 0 ->
      In [AMALLOC_PC; bv_unsigned ra] (al_U L) -> In [AMALLOC_PC] (al_U L) ->
      rng RNG lo (al_top L - lo) ->
      bv_unsigned sp < 2^47 -> rng RNG lo (bv_unsigned sp - lo) ->      (* [comment removed for export] *)
      aresv_ok L RESV ->                                            (* [comment removed for export] *)
      implS bsegs RNG (aembed ATOP (AsanCtrl.amalloc ATOP RESV st n))
            (epostF (dmalloc_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom bsegs)).

  Definition dfree_post (L : alayout) (RNG : footprint)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : astate) (LB : list ablock) (p : AsanCtrl.aptr) (lo : Z) (m : amem)
      (r : astate) (RNG' : footprint) : machine_state -> Prop :=
    fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m m' /\ astk_shadow_pres (bv_unsigned sp) m m'
      /\ AHEAP AI L RNG' r (lb_remove p LB) m'.

  Definition dfree_stmt : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : AsanCtrl.aptr) (A n lo : Z),
      AHEAP AI L RNG st LB m -> In (HB p A n) LB -> mem_inv bsegs m ->
      stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
      tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 A ->
      bv_unsigned s0 <= bv_unsigned sp -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC -> bv_unsigned sp mod 16 = 0 ->
      In [AFREE_PC; bv_unsigned ra] (al_U L) -> In [AFREE_PC] (al_U L) ->
      rng RNG lo (al_top L - lo) ->
      bv_unsigned sp < 2^47 -> rng RNG lo (bv_unsigned sp - lo) ->      (* [comment removed for export] *)
      implS bsegs RNG (aembed ATOP (AsanCtrl.afree st (Some p)))
            (epostF (dfree_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).

  Definition dfree_null_post (L : alayout) (RNG : footprint)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ aheap_pres CI LB (bv_unsigned sp) m m' /\ astk_shadow_pres (bv_unsigned sp) m m'
      /\ AHEAP AI L RNG st LB m'.

  Definition dfree_null_stmt : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
      AHEAP AI L RNG st LB m -> mem_inv bsegs m ->
      stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
      tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 0 ->
      bv_unsigned s0 <= bv_unsigned sp -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC -> bv_unsigned sp mod 16 = 0 ->
      In [AFREE_PC; bv_unsigned ra] (al_U L) -> In [AFREE_PC] (al_U L) ->
      rng RNG lo (al_top L - lo) ->
      bv_unsigned sp < 2^47 -> rng RNG lo (bv_unsigned sp - lo) ->      (* [comment removed for export] *)
      evtF bsegs RNG (dfree_null_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB lo m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition ashenv_law : Prop := forall L RNG st LB m, AHEAP AI L RNG st LB m -> ashenv m.

  (* [comment removed for export] *)
  Lemma ashenv_law_holds : ashenv_law.
  Proof.
    intros L RNG st LB m AH. pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT. unfold artcells in RT. decompose [and] RT.
    unfold ashenv. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma dmalloc_M : dmalloc_stmt -> forall (L : alayout) (RNG : footprint)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB : list ablock) (n lo : Z),
    AHEAP AI L RNG (aps_m s) LB m -> mem_inv bsegs m ->
    stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
    tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
    bv_unsigned s0 <= bv_unsigned sp -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC -> bv_unsigned sp mod 16 = 0 ->
    In [AMALLOC_PC; bv_unsigned ra] (al_U L) -> In [AMALLOC_PC] (al_U L) ->
    rng RNG lo (al_top L - lo) ->
    bv_unsigned sp < 2^47 -> rng RNG lo (bv_unsigned sp - lo) ->      (* [comment removed for export] *)
    aps_ok L s ->
    implMA RNG (amalloc_M n) s
      (fun r s' RNG' ms' => aps_rest s' = aps_rest s
         /\ dmalloc_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (aps_m s) LB n lo m (aps_m s', r) RNG' ms')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom bsegs)).
  Proof.
    intros DM. intros. lazymatch goal with H : aps_ok _ _ |- _ => destruct H as [HRV HAT] end.
    apply implMA_amalloc; [exact HAT|]. eapply implF_epost_mono; [eapply DM; eauto|].
    cbv beta. intros [st' r] RNG' ms' PO. split; [reflexivity| exact PO].
  Qed.

  Lemma dfree_M : dfree_stmt -> forall (L : alayout) (RNG : footprint)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB : list ablock) (p : AsanCtrl.aptr) (A n lo : Z),
    AHEAP AI L RNG (aps_m s) LB m -> In (HB p A n) LB -> mem_inv bsegs m ->
    stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
    tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 A ->
    bv_unsigned s0 <= bv_unsigned sp -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC -> bv_unsigned sp mod 16 = 0 ->
    In [AFREE_PC; bv_unsigned ra] (al_U L) -> In [AFREE_PC] (al_U L) ->
    rng RNG lo (al_top L - lo) ->
    bv_unsigned sp < 2^47 -> rng RNG lo (bv_unsigned sp - lo) ->      (* [comment removed for export] *)
    aps_ok L s ->                                                 (* [comment removed for export] *)
    implMA RNG (afree_M p) s
      (fun _ s' RNG' ms' => aps_rest s' = aps_rest s
         /\ dfree_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (aps_m s) LB p lo m (aps_m s') RNG' ms')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
  Proof.
    intros DF. intros. lazymatch goal with H : aps_ok _ _ |- _ => destruct H as [HRV HAT] end.
    apply implMA_afree; [exact HAT|]. eapply implF_epost_mono; [eapply DF; eauto|].
    cbv beta. intros st' RNG' ms' PO. split; [reflexivity| exact PO].
  Qed.

  (* [comment removed for export] *)
  Lemma aunw_drv : forall m L RNG lo PC (sp s0 ra : word),
    bv_unsigned s0 <= bv_unsigned sp -> bv_unsigned sp < 2^47 ->
    In [PC; bv_unsigned ra] (al_U L) -> In [PC] (al_U L) -> rng RNG lo (al_top L - lo) ->
    aunw m L RNG lo PC sp s0 ra [].
  Proof.
    intros m L RNG lo PC sp s0 ra Hs0 Hsp U2 U1 R. unfold aunw.
    destruct (Z.lt_ge_cases (bv_unsigned sp + 16) (al_top L)) as [LT|GE].
    - left. split; [exact LT|]. split; [apply uc_stop; lia|]. split; [cbn; lia|]. split; [exact U2| exact R].
    - right. split; [lia|]. split; [exact Hsp| exact U1].
  Qed.

  Lemma astk_shadow_pres_of_aheap_pres : forall LB (sp : Z) m m',
    aheap_pres CI LB sp m m' -> sp <= 2^47 -> astk_shadow_pres sp m m'.
  Proof.
    intros LB sp m m' HP Hsp a Ha. unfold shad, AsanEmbed.ASHOFF in Ha. rewrite !Z.shiftr_div_pow2 in Ha by lia. change (2^3) with 8 in Ha.
    destruct (HP a) as [E _]; [lia| | exact E].
    right. right. right. exists (8 * (a - 2147450880)). split.
    - left. atop_facts. pose proof ATOP_al16. Z.div_mod_to_equations. lia.
    - unfold shad, AsanEmbed.ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. pose proof ATOP_al16. Z.div_mod_to_equations. lia.
  Qed.

  Theorem dmalloc_of_AI : dmalloc_stmt.
  Proof.
    unfold dmalloc_stmt. intros until RESV. intros AH MI ST BOT LO TP A0 N S0 RA RA' SP16 U2 U1 RT SP47 RS ROK.
    eapply implF_epost_mono.
    - eapply (AI_malloc AI) with (tr := []); try eassumption.
      + apply aunw_drv; assumption.
      + lia.
    - cbv beta. intros [st' r] RNG' ms' (LE & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & HP & RR).
      split; [exact LE|]. exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
      split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HP|].
      split; [eapply astk_shadow_pres_of_aheap_pres; [exact HP| lia]| exact RR].
  Qed.

  Theorem dfree_of_AI : dfree_stmt.
  Proof.
    unfold dfree_stmt. intros until lo. intros AH IN MI ST BOT LO TP A0 S0 RA RA' SP16 U2 U1 RT SP47 RS.
    eapply implF_epost_mono.
    - eapply (AI_free AI) with (tr := []); try eassumption.
      + apply aunw_drv; assumption.
      + lia.
    - cbv beta. intros st' RNG' ms' (LE & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & HP & AH').
      split; [exact LE|]. exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
      split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HP|].
      split; [eapply astk_shadow_pres_of_aheap_pres; [exact HP| lia]| exact AH'].
  Qed.

  Theorem dfree_null_of_AI : dfree_null_stmt.
  Proof.
    unfold dfree_null_stmt. intros until lo. intros AH MI ST BOT LO TP A0 S0 RA RA' SP16 U2 U1 RT SP47 RS.
    eapply evtF_mono.
    - eapply (AI_free_null AI) with (tr := []); try eassumption.
      + apply aunw_drv; assumption.
      + lia.
    - cbv beta. intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & HP & AH').
      exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
      split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HP|].
      split; [eapply astk_shadow_pres_of_aheap_pres; [exact HP| lia]| exact AH'].
  Qed.
End DrvStmts.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TargetRun.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).

  (* [comment removed for export] *)
  Definition aatexit_cells (reg : bool) (m : amem) : Prop :=
       rw_cells bsegs m AATEXIT [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m (AATEXIT + 4) [C4 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m (AATEXIT + 8) [C4 (Z_to_bv 64 (if reg then 2 else 1))]
    /\ rw_cells bsegs m (AATEXIT + 16) [C8 (Z_to_bv 64 (AATEXIT + 24))]
    /\ rw_cells bsegs m (AATEXIT + 24) [C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m (AATEXIT + 32) [C8 (Z_to_bv 64 AATEXIT_CALL)]
    /\ rw_cells bsegs m (AATEXIT + 288) [C8 (Z_to_bv 64 ACOV_HOOK)]
    /\ rw_cells bsegs m (AATEXIT + 40) [C8 (Z_to_bv 64 (if reg then AATEXIT_CALL else 0))]
    /\ rw_cells bsegs m (AATEXIT + 296) [C8 (Z_to_bv 64 (if reg then AAEF_GUARD else 0))].
  (* [comment removed for export] *)
  Definition aincb0 (m : amem) : Prop := rw_cells bsegs m AAEF_INCB [C1 (Z_to_bv 8 0)].

  (* [comment removed for export] *)
  Definition atrun_cells0 (m : amem) : Prop :=
    rw_cells bsegs m AINIT_FLAG [C1 (Z_to_bv 8 0)] /\ aincb0 m /\ aatexit_cells false m
    /\ (exists cdt thr sec tm1, rw_cells bsegs m 0x622f40 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]).

  (* [comment removed for export] *)
  Definition atrun_ivs : list (Z * Z) :=
    [(RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024); (AINIT_FLAG, AINIT_FLAG + 8); (AATEXIT, AATEXIT + 0x220);   (* [comment removed for export] *)
     (0x602380, 0x602388)].      (* [comment removed for export] *)

  Fixpoint rin_ivs (ivs : list (Z * Z)) (a : Z) : Prop :=
    match ivs with [] => False | (lo, hi) :: ivs' => (lo <= a < hi) \/ rin_ivs ivs' a end.

  (* [comment removed for export] *)
  Definition adrv_pres (LB : list ablock) (SP : Z) (m m' : amem) : Prop :=
    forall a, 0 <= a < 2^64 -> (aclient_addr CI LB SP a \/ (shad ATOP <= a < shad SP)) -> ~ rin_ivs atrun_ivs a ->
      m' (wa a) = m (wa a) /\ (wview bsegs m (wa a) <> None -> wview bsegs m' (wa a) <> None).

  Lemma adrv_pres_refl : forall LB SP m, adrv_pres LB SP m m.
  Proof. intros LB SP m a _ _ _. auto. Qed.

  Lemma adrv_pres_trans : forall LB SP m1 m2 m3, adrv_pres LB SP m1 m2 -> adrv_pres LB SP m2 m3 -> adrv_pres LB SP m1 m3.
  Proof.
    intros LB SP m1 m2 m3 H1 H2 a Ha Hc Hx. destruct (H1 a Ha Hc Hx) as [E1 W1]. destruct (H2 a Ha Hc Hx) as [E2 W2].
    split; [congruence| auto].
  Qed.

  (* [comment removed for export] *)
  Definition atarget_run_postA (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (s : APS) (LB : list ablock) (lo : Z) (canary : word) (m : amem)
      (r : Z) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
    fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) (m' : amem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ (r = 0 \/ r = 2 \/ r = 78)                               (* [comment removed for export] *)
      /\ aatexit_cells true m' /\ aincb0 m'                        (* [comment removed for export] *)
      /\ mem_inv bsegs m' /\ frm0 fc' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ adrv_pres LB (bv_unsigned sp) m m'
      /\ AHEAP AI L RNG' (aps_m s') LB m'
      /\ stdout_file m' (aps_so s')
      /\ ssp_cells m' canary
      /\ aps_ok L s'.                                            (* [comment removed for export] *)

  Variable rng_fs : alayout -> footprint -> Prop.

  (* [comment removed for export] *)
  Definition atarget_run_stmtA : Prop :=
    forall (L : alayout) (RNG : footprint) (rstk : region)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : amem)
           (s : APS) (LB : list ablock) (p : AsanCtrl.aptr) (A cap Lc : Z) (content : list Z) (lo : Z) (canary : word),
      AHEAP AI L RNG (aps_m s) LB m -> In (HB p A cap) LB -> (forall b, In b LB -> exists p' A' n', b = HB p' A' n') ->
      bytes_at bsegs m A (map (Z_to_bv 8) content) -> Forall (fun c => 0 <= c < 256) content ->
      zlength content <= cap -> cap <= 2^26 -> 0 <= Lc -> 6 + Lc <= zlength content ->
      atrun_cells0 m -> harness_invA m ->
      stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - ATARGET_RUN_STACK ->
      bv_unsigned sp + 128 = al_sp0 L -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < 2^47 ->     (* [comment removed for export] *)
      mem_inv bsegs m -> frm0 fc ->
      stdout_file m (aps_so s) -> ssp_cells m canary ->
      aps_ok L s ->                                   (* [comment removed for export] *)
      (* [comment removed for export] *)
      rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk -> rodata_sh0 m -> rclean m RBstdout ->
      tp = Z_to_bv 64 ATP ->
      a0 = Z_to_bv 64 (A + 2) -> a1 = Z_to_bv 64 Lc -> a2 = Z_to_bv 64 (A + 6 + Lc) -> a3 = Z_to_bv 64 (zlength content - 6 - Lc) ->
      (* [comment removed for export] *)
      HU L -> In [AMALLOC_PC; ATRUN_MALLOC_RA] (al_U L) -> In [AFREE_PC; ATRUN_FREE_RA] (al_U L) -> In [AMALLOC_PC] (al_U L) -> In [AFREE_PC] (al_U L) ->
      (* [comment removed for export] *)
      rng RNG lo (bv_unsigned sp + 128 - lo) -> rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG ->
      rrng RNG rstk -> rrng RNG RFMT -> rrng RNG RBstdout ->
      implMA RNG (runA AAllocAsan (if 0 <? Lc then znth content 2 else 0) (skipn (Z.to_nat (6 + Lc)) content)) s
             (atarget_run_postA L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo canary m)
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 ATARGET_RUN) fc None m (seg_rom bsegs)).
End TargetRun.
End CANSEC1.
