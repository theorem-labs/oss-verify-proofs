(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress3_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec CatExec SeqExec StepTac StoreOk StreamSim WsegFast Frame MemSplit StartupTac ArgvEnv RefLayout DrawDefs
  U8StartupDefs U8Startup U8StartupFacts U8ExitBase.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM02. Import MM02. Import MM02.Malloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image InitMem Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require Import PImg RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require RunHit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainU8 Require PImgRun.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import PState. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr Require Import MrFeasNull MrRoom.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.MrP8 Require Import U8HBase U8HConv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* kitfix4 alias stage: Module SD := OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs expanded *)
(* kitfix4 alias stage: Module SS := OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8Startup expanded *)
(* kitfix4 alias stage: Module SF := OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupFacts expanded *)

Lemma rw_cells_of_rdn_gen {RCa1 : RunCtx}  : forall (M : word -> option byte) A cs,
  cells_wf cs ->
  rdn (run_segments psegs rc_inp rc_sp rc_mb) M (wa A) (cells_size cs) = Some (cells_bytes cs) ->
  store_ok (run_segments psegs rc_inp rc_sp rc_mb) M (wa A) (cells_size cs) = true -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 2^64 ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M A cs.
Proof.
  intros M A cs WF H S HA Hn. split; [split|].
  - exact WF.
  - eapply bytes_at_of_rdn; eassumption.
  - apply wr_at_of_store_ok; assumption.
Qed.

(* the auxv as rauxv_ok states it. [auxv_vals] lists StackLayout.auxv_entries' values in
   its own order (the flush port's VS, Plain/RDriver_kit rauxv_ok_init); u64s_rauxv_list says rauxv_list over them
   serializes to auxv_bytes, for either CONFIG_RSEQ value. *)
Definition auxv_vals (la : LaunchAuxv) (ph : PhdrInfo) (entry uid gid hw xfn : word) : list Z :=
  map bv_unsigned
    [la_sysinfo_ehdr la; cw_l1i_size (la_cache la); cw_l1i_geom (la_cache la);
     cw_l1d_size (la_cache la); cw_l1d_geom (la_cache la); cw_l2_size (la_cache la);
     cw_l2_geom (la_cache la); cw_l3_size (la_cache la); cw_l3_geom (la_cache la);
     la_minsigstksz la; hw; Z_to_bv 64 4096; Z_to_bv 64 100;
     Z_to_bv 64 (Z.of_N (ph_addr ph)); Z_to_bv 64 (Z.of_N (ph_ent ph)); Z_to_bv 64 (Z.of_N (ph_num ph));
     Z_to_bv 64 0; Z_to_bv 64 0; entry; uid; uid; gid; gid; Z_to_bv 64 0; xfn].

Lemma u64s_rauxv_list : forall (la : LaunchAuxv) (ph : PhdrInfo) (entry uid gid hw rnd xfn : word),
  u64s (rauxv_list (auxv_vals la ph entry uid gid hw xfn) (la_rseq la) (bv_unsigned rnd))
  = auxv_bytes la ph entry uid gid hw rnd xfn.
Proof.
  intros la ph entry uid gid hw rnd xfn.
  unfold auxv_vals, auxv_bytes, auxv_entries, rauxv_list, MallocRep.wz.
  destruct (la_rseq la); cbn [map u64s build_auxv fst snd app nth]; unfold le8;
    rewrite !Z_to_bv_bv_unsigned; reflexivity.
Qed.

Lemma rauxv_list_len : forall vs (r : bool) z, Z.of_nat (length (rauxv_list vs r z)) = 2 * Z.of_nat (auxv_count r).
Proof. intros vs r z. unfold rauxv_list, auxv_count. rewrite length_map. destruct r; reflexivity. Qed.

Section ME.
Context {rc : runConstT}.
(* the launch is one ProcInput:
   av / ev / uid / hw are its fields; the main entry also names the launch's mmap base. *)
Variables (sp0 : word) (inp : ProcInput) (mbase : word) (rdraw : EntryDraw) (tid : word).
#[local] Instance RC_a1_1 : RunCtx := mkRunCtx inp sp0 mbase.
Local Notation av := (in_argv inp) (only parsing).
Local Notation ev := (in_envp inp) (only parsing).
Local Notation uid := (in_uid inp) (only parsing).
Local Notation hw := (in_hwcap inp) (only parsing).
Variables (regs : bvmap 5 word) (mem : word -> option byte).
Hypothesis Hva : valid_argv av.
Hypothesis Hlo : 0x7fff80000000 <= bv_unsigned sp0.
Hypothesis Hhi : bv_unsigned sp0 <= 0x800000000000.
Hypothesis ME : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8Startup.main_entry sp0 inp mbase rdraw tid regs mem.
Hypothesis HCAN : CAN = DrawDefs.canary_w rdraw.
Hypothesis HSEC : SECRET = bv_unsigned (DrawDefs.secret_w rdraw).
Hypothesis HATOP : ATOP = bv_unsigned sp0 - 8388608.
Hypothesis Hve : valid_envp ev.
Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
(* the launch facts RefLayout's 727 layout reads (me_rauxv only uses them). *)
Variable brk : word.
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
Local Notation ENTW := (Z_to_bv 64 (Z.of_N Tgt_zlib_uncompress3_fuzzer_ubsan.M.init_pc)) (only parsing).
Variable M : word -> option byte.
Hypothesis AG : forall a : word, bv_unsigned a < 0x95000 -> M a = mem a.
Hypothesis AGv : forall a : word, bv_unsigned a < bv_unsigned sp0 - 8388608 -> M a = mem a.   (* below the 8 MiB stack area, where the vDSO pair lies *)
Hypothesis AGhi : forall a : word, bv_unsigned sp0 <= bv_unsigned a -> M a = mem a.
Hypothesis GR : OS.mem_grows mem M.

Lemma D_main_none : forall a : word,
  bv_unsigned a < 0x241b0 \/ 0x945f8 <= bv_unsigned a -> OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_main sp0 inp rdraw tid a = None.
Proof.
  intros a Ha. unfold OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_main, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_fd, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_ssp, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_tls, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_tlsB, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_tlsA, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_libc.
  repeat (rewrite MemSplit.wbytes_outside;
          [ | rewrite ?CatExec.length_N_to_le_bytes; cbn [length]; rewrite unsigned_lit by lia; lia
            | rewrite ?CatExec.length_N_to_le_bytes; cbn [length]; rewrite unsigned_lit by lia; lia ]).
  reflexivity.
Qed.

Lemma D_main_none_gen : forall a : word,
  Forall (fun c : Z * nat => bv_unsigned a < fst c \/ fst c + Z.of_nat (snd c) <= bv_unsigned a) OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupFacts.D_main_cells ->
  OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_main sp0 inp rdraw tid a = None.
Proof.
  intros a HF. unfold OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupFacts.D_main_cells in HF.
  repeat (apply Forall_cons_iff in HF; destruct HF as [?C HF]). clear HF.
  cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ] in *.
  unfold OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_main, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_fd, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_ssp, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_tls, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_tlsB, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_tlsA, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_libc.
  repeat (rewrite MemSplit.wbytes_outside;
          [ | rewrite ?CatExec.length_N_to_le_bytes; cbn [length]; rewrite unsigned_lit by lia; lia
            | rewrite ?CatExec.length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite unsigned_lit by lia; lia ]).
  reflexivity.
Qed.

Lemma me_below : forall a : word, bv_unsigned a < 0x95000 -> M a = OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_main sp0 inp rdraw tid a.
Proof.
  intros a Ha. rewrite AG by exact Ha. apply (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8Startup.main_entry_mem_data sp0 inp mbase rdraw tid regs mem ME).
  rewrite CatExec.stack_max_size_val. lia.
Qed.

Lemma me_none_gen : forall a : Z, 0 <= a < 0x95000 ->
  Forall (fun c : Z * nat => a < fst c \/ fst c + Z.of_nat (snd c) <= a) OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupFacts.D_main_cells ->
  M (Z_to_bv 64 a) = None.
Proof.
  intros a Ha HF. rewrite me_below by (rewrite unsigned_lit by lia; lia). apply D_main_none_gen.
  rewrite unsigned_lit by lia. exact HF.
Qed.

Lemma me_statics_none : forall a : word, 0x945f8 <= bv_unsigned a < 0x949a0 -> M a = None.
Proof. intros a Ha. rewrite me_below by lia. apply D_main_none. lia. Qed.

(* over the launch's own run (the section's RC_a1_1), M holds no byte on a read-only
   range: not on the image's (D_main is None there), nor on the vDSO pair, which lies below sp0 - 8 MiB, where
   M = mem (AGv) = D_main (main_entry_mem_data) = None. *)
Lemma me_mem_inv : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M.
Proof.
  intros a b Hab. pose proof (bv_unsigned_in_range 64 a) as Ra.
  assert (VT : forall sp mb : word, RunHit.vdso_top sp mb <= bv_unsigned sp - 8388608).
  { intros sp mb. unfold RunHit.vdso_top, page_round_down_Z, stack_max_size, page_size.
    pose proof (Z.le_min_r (bv_unsigned mb) ((bv_unsigned sp - 8 * 1024 * 1024) / 4096 * 4096)).
    pose proof (Z.mul_div_le (bv_unsigned sp - 8 * 1024 * 1024) 4096 ltac:(lia)).
    pose proof (Z.mul_div_le (Z.min (bv_unsigned mb) ((bv_unsigned sp - 8 * 1024 * 1024) / 4096 * 4096)) 4096
                  ltac:(lia)).
    lia. }
  destruct (Z_lt_le_dec (bv_unsigned a) 0x95000) as [L|L].
  - destruct (Z_lt_le_dec (bv_unsigned a) 0x10000) as [L0|L0].
    + exfalso. rewrite me_below in Hab by lia. rewrite D_main_none in Hab by lia. discriminate.
    + rewrite U8HBase.run_ro_addr_img by lia. rewrite p_ro_addr.
      destruct (Z.leb_spec0 0x10000 (bv_unsigned a)) as [H1|H1]; [|reflexivity].
      destruct (Z.ltb_spec0 (bv_unsigned a) 0x22000) as [H2|H2]; [|reflexivity].
      exfalso. rewrite me_below in Hab by lia. rewrite D_main_none in Hab by lia. discriminate.
  - destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned sp0 - 8388608)) as [L1|L1].
    + exfalso. rewrite AGv in Hab by lia.
      rewrite (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8Startup.main_entry_mem_data sp0 inp mbase rdraw tid regs mem ME) in Hab
        by (rewrite CatExec.stack_max_size_val; lia).
      rewrite D_main_none in Hab by lia. discriminate.
    + apply PImgRun.run_ref_ro_addr_false; [lia|]. right; right.
      pose proof (VT rc_sp rc_mb) as V. change (bv_unsigned (@rc_sp RC_a1_1)) with (bv_unsigned sp0) in V. lia.
Qed.

Lemma me_rdn : forall (a : Z) (n : nat), 0 <= a -> a + Z.of_nat n <= 0x95000 ->
  OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (wa a) n = OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_main sp0 inp rdraw tid) (wa a) n.
Proof.
  intros a n Ha Hn.
  rewrite <- (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8Startup.main_entry_rdn_data sp0 inp mbase rdraw tid regs mem ME)
    by (rewrite CatExec.stack_max_size_val; unfold wa; rewrite unsigned_lit by lia; lia).
  apply OP.rdn_ext; [unfold wa; rewrite unsigned_lit by lia; lia|].
  intros x Hx. unfold wa in Hx. rewrite unsigned_lit in Hx by lia. apply AG. lia.
Qed.

Ltac dm_unfold := unfold OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_main, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_fd, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_ssp, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_tls, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_tlsB, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_tlsA, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_libc.
Let D := OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.D_main sp0 inp rdraw tid.

Lemma len_av' : 1 <= Z.of_nat (length av) <= 1024.
Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

Lemma D_hit_cdt : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) D (Z_to_bv 64 0x94588) 1 = Some [Z_to_bv 8 1].
Proof.
  pose proof (bv_unsigned_in_range 64 tid). pose proof len_av'. subst D. dm_unfold. StartupTac.peel.
  apply (SeqExec.rdn_wbytes_hit (run_segments psegs rc_inp rc_sp rc_mb) [Z_to_bv 8 1]). cbn [length]. rewrite unsigned_lit by lia. lia.
Qed.

Lemma D_hit_auxv : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) D (Z_to_bv 64 0x94590) 8 = Some (word_to_le_bytes 8 (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.auxv_w sp0 inp)).
Proof.
  pose proof (bv_unsigned_in_range 64 tid). pose proof len_av'. subst D. dm_unfold. StartupTac.peel.
  apply SeqExec.rdn_wbytes_hit8. rewrite unsigned_lit by lia. lia.
Qed.

Lemma D_hit_tls_size : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) D (Z_to_bv 64 0x945a0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe0)).
Proof.
  pose proof (bv_unsigned_in_range 64 tid). pose proof len_av'. subst D. dm_unfold. StartupTac.peel.
  apply SeqExec.rdn_wbytes_hit8. rewrite unsigned_lit by lia. lia.
Qed.

Lemma D_hit_tls_align : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) D (Z_to_bv 64 0x945a8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 8)).
Proof.
  pose proof (bv_unsigned_in_range 64 tid). pose proof len_av'. subst D. dm_unfold. StartupTac.peel.
  apply SeqExec.rdn_wbytes_hit8. rewrite unsigned_lit by lia. lia.
Qed.

Ltac bytes_eq :=
  vm_compute; apply f_equal; repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]); reflexivity.

Lemma me_hit : forall a n bs, 0 <= a -> a + Z.of_nat n <= 0x95000 ->
  OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) D (Z_to_bv 64 a) n = Some bs -> OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (wa a) n = Some bs.
Proof. intros a n bs Ha Hn H. rewrite me_rdn by lia. exact H. Qed.

Lemma me_miss : forall a n bs, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupFacts.D_main_missb a n = true ->
  OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 a) n = Some bs -> OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (wa a) n = Some bs.
Proof.
  intros a n bs Hb H.
  assert (Hr : 0 <= a /\ a + Z.of_nat n <= 0x95000).
  { unfold OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupFacts.D_main_missb in Hb. apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [_ H1].
    apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
  rewrite me_rdn by lia. unfold wa. rewrite (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupFacts.D_main_miss sp0 inp rdraw tid (run_segments psegs rc_inp rc_sp rc_mb) a n Hb). exact H.
Qed.

Lemma sok_rw2 {RCa1 : RunCtx}  : forall (m : word -> option byte) a (n : nat), 0x23000 <= a -> a + Z.of_nat n <= 0x95000 ->
  store_ok (run_segments psegs rc_inp rc_sp rc_mb) m (wa a) n = true.
Proof. intros m a n Ha Hn. apply U8ExitBase.store_ok_data; unfold wa; rewrite unsigned_lit by lia; lia. Qed.

Lemma wseg_rw1 {RCa1 : RunCtx}  : StreamSim.wseg_ok (run_segments psegs rc_inp rc_sp rc_mb) (Z_to_bv 64 0x22000) (Z.to_nat (0x23000 - 0x22000)) = true.
Proof. apply WsegFast.wseg_fast_sound. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma sok_rw1 {RCa1 : RunCtx}  : forall (m : word -> option byte) a (n : nat), 0x22000 <= a -> a + Z.of_nat n <= 0x23000 ->
  store_ok (run_segments psegs rc_inp rc_sp rc_mb) m (wa a) n = true.
Proof.
  intros m a n Ha Hn.
  eapply (StoreOk.store_ok_window (run_segments psegs rc_inp rc_sp rc_mb) m (Z_to_bv 64 0x22000) (wa a) (Z.to_nat (0x23000 - 0x22000)) n 0x22000 0x23000);
    [ apply unsigned_lit; lia | reflexivity | lia | exact wseg_rw1
    | unfold wa; rewrite unsigned_lit by lia; lia | unfold wa; rewrite unsigned_lit by lia; lia ].
Qed.

Lemma me_cell {RCa1 : RunCtx}  : forall A c, cell_wf c -> 0x22000 <= A -> A + Z.of_nat (csize c) <= 0x95000 ->
  (A + Z.of_nat (csize c) <= 0x23000 \/ 0x23000 <= A) ->
  OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (wa A) (csize c) = Some (cbytes c) -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M A [c].
Proof.
  intros A c WF H1 H2 H3 H. apply rw_cells_of_rdn_gen; cbn [cells_size cells_bytes cells_wf]; rewrite ?Nat.add_0_r, ?app_nil_r.
  - split; [exact WF | exact I].
  - exact H.
  - destruct H3; [apply sok_rw1 | apply sok_rw2]; lia.
  - lia.
  - lia.
Qed.

Ltac cell_hit L := apply me_cell; [exact I | lia | cbn; lia | cbn; lia | cbn [csize cbytes]; apply me_hit; [lia | cbn; lia | exact L]].
Ltac cell_miss := apply me_cell; [try exact I; reflexivity | lia | cbn; lia | cbn; lia
                                  | cbn [csize cbytes]; apply me_miss; [vm_compute; reflexivity | bytes_eq]].
Ltac cells_cons := apply (proj2 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M _ [_] _)); cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add];
                   split.

Lemma me_libc1 : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x94588 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)].
Proof.
  change [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)]
    with ([C1 (Z_to_bv 8 1)] ++ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)]).
  apply (proj2 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M _ _ _)). split.
  - cell_hit D_hit_cdt.
  - cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
    apply rw_cells_of_rdn_gen; [cbn; tauto | | apply sok_rw2; cbn; lia | lia | cbn; lia].
    cbn [cells_size csize Nat.add]. apply me_miss; [vm_compute; reflexivity | bytes_eq].
Qed.

Lemma me_libc2 : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x94590
  [C8 (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.auxv_w sp0 inp); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)].
Proof.
  apply (proj2 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M 0x94590 [C8 (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.auxv_w sp0 inp)] _)). split; [cell_hit D_hit_auxv|].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M 0x94598 [C8 (Z_to_bv 64 0)] _)). split; [cell_miss|].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M 0x945a0 [C8 (Z_to_bv 64 224)] _)). split; [cell_hit D_hit_tls_size|].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M 0x945a8 [C8 (Z_to_bv 64 8)] _)). split; [cell_hit D_hit_tls_align|].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M 0x945b0 [C8 (Z_to_bv 64 0)] _)). split; [cell_miss|].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M 0x945b8 [C8 (Z_to_bv 64 4096)] _)). split.
  - cell_hit (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupFacts.D_main_pagesize sp0 inp rdraw tid Hva (run_segments psegs rc_inp rc_sp rc_mb)).
  - cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add]. cell_miss.
Qed.

Lemma me_got_ssp : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x22f80 [C8 (Z_to_bv 64 0x94568)].
Proof. cell_miss. Qed.

Lemma me_guard : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x94568 [C8 CAN].
Proof. rewrite HCAN. cell_hit (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupFacts.D_main_guard_w sp0 inp rdraw tid (run_segments psegs rc_inp rc_sp rc_mb)). Qed.

Theorem main_entry_RHEAP :
  RHEAP (ps_init (reservedZ psegs ++ RunHit.vdso_resvZ rc_inp rc_sp rc_mb) ATOP) [] M /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M RAUXV_CELL [C8 (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.auxv_w sp0 inp)].
Proof.
  apply RHEAP_init_proof.
  - exact me_statics_none.
  - exact me_libc1.
  - exact me_libc2.
  - exact me_got_ssp.
  - exact me_guard.
  - exact me_mem_inv.
Qed.

Lemma me_tid : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 0x74258) 4 = Some (word_to_le_bytes 4 tid).
Proof. apply (me_hit 0x74258 4); [lia | cbn; lia | exact (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupFacts.D_main_tid sp0 inp rdraw tid (run_segments psegs rc_inp rc_sp rc_mb))]. Qed.

Lemma me_errno : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M RERRNO [C4 (Z_to_bv 64 0)].
Proof. unfold RERRNO. cell_miss. Qed.

(* the ruled stack figure. The launch maps [sp0 - 6144513, sp0) (S8Startup
   main_entry_store_ok_win), not the whole 8 MiB below sp0; ATOP (= sp0 - 8388608, the heap ceiling) stays, and the
   malloc call's stack bound [lo] (call_pre: ATOP <= lo) is this figure. *)
Lemma me_stk : forall hi, hi <= bv_unsigned sp0 -> stk (run_segments psegs rc_inp rc_sp rc_mb) M (bv_unsigned sp0 - 6144513) hi.
Proof.
  intros hi Hhi'. apply stk_of_store_ok; [lia | lia |]. intros a Ha.
  eapply OS.store_ok_mono; [exact GR|].
  apply (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8Startup.main_entry_store_ok_win sp0 inp mbase rdraw tid regs mem ME (run_segments psegs rc_inp rc_sp rc_mb) (wa a) 1);
    unfold wa; rewrite unsigned_lit by lia; cbn; lia.
Qed.

(* the image above sp0 is Linux's whole block (StackLayout.entry_stack_image over the
   launch); S8Startup's main_entry reads it through wrap_mem, ArgvEnv peels the wrapper. *)
Lemma me_rdn_above : forall (a : word) n, bv_unsigned sp0 <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2^64 ->
  OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M a n
  = OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) (stack_to_mem sp0 (entry_stack_image inp mbase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupFacts.RPH
                    (Z_to_bv 64 (Z.of_N Tgt_zlib_uncompress3_fuzzer_ubsan.M.init_pc)) sp0 rdraw)) a n.
Proof.
  intros a n Ha Hn.
  rewrite <- (ArgvEnv.rdn_wmem_stack (run_segments psegs rc_inp rc_sp rc_mb) inp mbase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupFacts.RPH
                (Z_to_bv 64 (Z.of_N Tgt_zlib_uncompress3_fuzzer_ubsan.M.init_pc)) sp0 rdraw a n Ha Hn).
  unfold ArgvEnv.wmem.
  rewrite <- (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8Startup.main_entry_rdn_above sp0 inp mbase rdraw tid regs mem ME (run_segments psegs rc_inp rc_sp rc_mb) a n Ha Hn).
  apply OP.rdn_ext; [exact Hn|]. intros x Hx. apply AGhi. lia.
Qed.

(* a worker port727 (): the auxv mallocng's __malloc_init scans is Linux's whole vector, StackLayout.auxv_entries
   (27 pairs, 29 under CONFIG_RSEQ: the keys rauxv_list states, PlainS8/RMallocTree as carried from row 27's port).
   Its values are the launch's, read off RefLayout's 727 layout through me_rdn_above; the VALUES list [VS] is the
   flush port's (Plain/RDriver_kit rauxv_ok_init), in auxv_entries' order. The launch facts (Hvl / Hlau / brk) enter
   here only. *)
Lemma me_rauxv : rauxv_ok M (bv_unsigned sp0).
Proof.
  pose proof len_av' as LA. destruct Hve as [LE _].
  pose proof (RefLayout.rnd_facts (run_segments psegs rc_inp rc_sp rc_mb) Sv48 inp mbase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupFacts.RPH ENTW sp0 brk rdraw Hvl Hlau
                ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) Hal) as (R1 & R2 & R3 & R4 & R5).
  pose proof (RefLayout.lay_bsb_len Sv48 inp mbase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupFacts.RPH ENTW sp0 brk rdraw Hvl Hlau) as BL.
  set (rnd := at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev) in *.
  set (xfn := at_execfn_ptr (ed_top rdraw) (in_execfn inp)).
  pose proof (u64s_rauxv_list (launch_auxv inp sp0 mbase) OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupFacts.RPH ENTW uid (in_gid inp) hw rnd xfn) as EQL.
  pose proof (rauxv_list_len (auxv_vals (launch_auxv inp sp0 mbase) OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupFacts.RPH ENTW uid (in_gid inp) hw xfn)
                (la_rseq (launch_auxv inp sp0 mbase)) (bv_unsigned rnd)) as LR.
  change (la_rseq (launch_auxv inp sp0 mbase)) with (kb_rseq (in_kernel inp)) in EQL, LR.
  assert (CN : (auxv_count (kb_rseq (in_kernel inp)) <= 29)%nat)
    by (unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia).
  assert (AU : bv_unsigned (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.auxv_w sp0 inp) = bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
  { unfold OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.auxv_w. apply unsigned_lit. lia. }
  exists (bv_unsigned (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.auxv_w sp0 inp)), (auxv_vals (launch_auxv inp sp0 mbase) OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupFacts.RPH ENTW uid (in_gid inp) hw xfn),
         (kb_rseq (in_kernel inp)), (bv_unsigned rnd).
  split; [|split; [|split]].
  -
    unfold MallocRep.wz. rewrite Z_to_bv_bv_unsigned. exact (proj2 main_entry_RHEAP).
  -
    apply (bytes_at_of_rdn (auxv_size (kb_rseq (in_kernel inp)))); [ | lia | unfold auxv_size; lia].
    unfold wa. rewrite Z_to_bv_bv_unsigned.
    match goal with |- rdn ?s ?m ?a ?n = ?res => change (OP.rdn s m a n = res) end.
    rewrite me_rdn_above by (unfold auxv_size; lia).
    replace (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.auxv_w sp0 inp) with (sp0 + nat_to_word (RefLayout.auxv_off av ev))%bv.
    2:{ unfold OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupDefs.auxv_w, RefLayout.auxv_off. rewrite StepTac.word_add_nat. f_equal. lia. }
    rewrite (RefLayout.read_auxv_all (run_segments psegs rc_inp rc_sp rc_mb) Sv48 inp mbase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.U8StartupFacts.RPH ENTW sp0 brk rdraw Hvl Hlau
               ltac:(unfold sp_window_hi; lia)).
    f_equal. symmetry. exact EQL.
  -
    apply (bytes_at_of_rdn 8); [ | lia | lia].
    change (OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (wa (bv_unsigned rnd + 8)) 8 = Some (le8 (wz SECRET))).
    unfold wa. rewrite me_rdn_above by (rewrite unsigned_lit by lia; lia).
    rewrite (R5 8%nat 8%nat ltac:(lia)). f_equal.
    unfold le8, MallocRep.wz, wz. rewrite HSEC, Z_to_bv_bv_unsigned, DrawDefs.w8_secret. reflexivity.
  - pose proof (bv_unsigned_in_range 64 rnd).
    unfold bv_modulus in *. rewrite LR. repeat split; try lia.
Qed.
End ME.

Section MODEL.
Context {rc : runConstT}.

Lemma reserved_top_ge : forall l e, In e l -> bv_unsigned (fst e) + bv_unsigned (snd e) <= reserved_top l.
Proof.
  induction l as [|[a sz] l IH]; intros e Hin; [destruct Hin|].
  cbn [reserved_top]. destruct Hin as [<-|Hin]; cbn [fst snd]; [lia|]. specialize (IH e Hin). lia.
Qed.

(* KL (Spec/KLink) reads only minv, m_halted, m_vmmaps and m_kernel, so it carries to any
   model that agrees with a KL model on those four. Run.init_config's start model is
   with_vdso (vdso_run_init (ed_vdso draw)) (init_model ..), and the read chain's models add with_tid / with_fds on top:
   none of the three touches m_vmmaps, m_kernel or m_halted. *)
Lemma KL_transfer : forall L pbrk (mo mo' : Model),
  KL L pbrk mo -> minv mo' -> m_halted mo' = None ->
  m_vmmaps mo' = m_vmmaps mo -> m_kernel mo' = m_kernel mo -> KL L pbrk mo'.
Proof.
  intros L pbrk mo mo' K Hmi Hh Ev Ek. destruct K.
  constructor; rewrite ?Ev, ?Ek; assumption.
Qed.

(* the start ledger is init_model's (the image's reservations, then the vDSO pair,
   State.init_reserved); KLink's KL_init proves KL there, KL_transfer carries it to [mo]. The heap's ghost ledger stays
   [led_init (reservedZ segs) atop]: KLink's kl_resv splits vm_reserved into the image part (= reservedZ) and the
   vDSO pair above start_brk. *)
Lemma KL_init_vm_gen : forall segs (mo : Model) (brk0 mbase sp : word) lim (inp : ProcInput) atop,
  m_vmmaps mo = m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp) ->
  m_kernel mo = in_kernel inp ->
  minv mo -> m_halted mo = None ->
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  sp_window_lo <= bv_unsigned sp <= sp_window_hi ->
  atop = bv_unsigned sp - stack_max_size ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
  reserved_top (segments_reserved segs) + brk_aslr_max <= 2 ^ 33 ->
  mmap_base_min <= bv_unsigned mbase -> in_channel_reader inp = true ->
  KL (led_init (reservedZ segs ++ RunHit.vdso_resvZ inp sp mbase) atop) 0 mo.  (* the ledger holds the vDSO pair *)
Proof.
  intros segs mo brk0 mbase sp lim inp atop Evm Ek MI Eh Hb Hpos Hsp Eatop Hceil Hlow Hmb Hrd.
  apply (KL_transfer _ _ (init_model (segments_reserved segs) brk0 mbase sp lim inp) mo);
    [ | exact MI | exact Eh | exact Evm | rewrite Ek; reflexivity ].
  exact (KL_init_full segs brk0 mbase sp lim inp (reservedZ segs ++ RunHit.vdso_resvZ inp sp mbase) atop 0 eq_refl Hb Hpos Hsp Eatop Hceil Hlow Hmb Hrd).
Qed.

Lemma KL_init_vm : forall (mo : Model) (brk0 mbase sp : word) lim (inp : ProcInput) atop,
  m_vmmaps mo = m_vmmaps (init_model (segments_reserved psegs) brk0 mbase sp lim inp) ->
  m_kernel mo = in_kernel inp ->
  minv mo -> m_halted mo = None ->
  valid_brk psegs brk0 ->
  sp_window_lo <= bv_unsigned sp <= sp_window_hi ->
  atop = bv_unsigned sp - stack_max_size ->
  mmap_base_min <= bv_unsigned mbase -> in_channel_reader inp = true ->
  KL (led_init (reservedZ psegs ++ RunHit.vdso_resvZ inp sp mbase) atop) 0 mo.
Proof.
  intros mo brk0 mbase sp lim inp atop Evm Ek MI Eh Hb Hsp Eatop Hmb Hrd.
  apply (KL_init_vm_gen psegs mo brk0 mbase sp lim inp atop Evm Ek MI Eh Hb); [ | exact Hsp | exact Eatop | | | exact Hmb | exact Hrd].  (* the kernel ledger's segments are the IMAGE's (segments_reserved / reservedZ), not the run's *)
  - rewrite reserved_top_plain. lia.
  - rewrite reserved_top_plain, alloc_ceiling_lo_val. unfold brk_aslr_max, PGSZ. lia.
  - rewrite reserved_top_plain. unfold brk_aslr_max. lia.
Qed.

(* the start model's VM state is init_model's
   and its kernel build the launch's; the launch's channel reader feeds minv_init through KL_init. *)
Lemma OWN_init_vm : forall (G : PState -> Model -> Prop) (mo : Model) (brk0 mbase sp : word) lim (inp : ProcInput),
  m_vmmaps mo = m_vmmaps (init_model (segments_reserved psegs) brk0 mbase sp lim inp) ->
  m_kernel mo = in_kernel inp ->
  minv mo -> m_halted mo = None -> valid_brk psegs brk0 ->
  sp_window_lo <= bv_unsigned sp <= sp_window_hi ->
  ATOP = bv_unsigned sp - stack_max_size ->
  mmap_base_min <= bv_unsigned mbase -> in_channel_reader inp = true ->
  G (ps_init (reservedZ psegs ++ RunHit.vdso_resvZ inp sp mbase) ATOP) mo ->
  OWN [] G (ps_init (reservedZ psegs ++ RunHit.vdso_resvZ inp sp mbase) ATOP) mo.
Proof.
  intros G mo brk0 mbase sp lim inp Evm Ek MI Eh Hb Hsp Ea Hmb Hrd HG. split; [|split; [constructor | exact HG]].
  exists (led_init (reservedZ psegs ++ RunHit.vdso_resvZ inp sp mbase) ATOP). split; [|split].
  - apply creach_init. pose proof atop_range. unfold atop_hi. lia.
  - exact (KL_init_vm mo brk0 mbase sp lim inp ATOP Evm Ek MI Eh Hb Hsp Ea Hmb Hrd).
  - intros x [].
Qed.

Lemma allnone_init : forall resv atop, allnone (ps_m (ps_init resv atop)).
Proof. intros resv atop sc. reflexivity. Qed.

Lemma room_init_vm : forall (mo : Model) (brk0 mbase sp : word) lim B,
  m_vmmaps mo = mkVmMapsFull (segments_reserved psegs) [] [] brk0 brk0 lim mbase sp ->
  m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  sp_window_lo <= bv_unsigned sp -> B + 4096 <= lim ->
  room B mo.
Proof.
  intros mo brk0 mbase sp lim B Evm Hl Hm Hsp HB. unfold room. rewrite Evm. cbn [vm_reserved vm_maps vm_init_sp vm_limit app].
  split; [exact Hsp|]. rewrite app_nil_r, segments_reserved_plain.
  split; [repeat constructor; cbn [snd]; rewrite unsigned_lit by lia; lia|].
  split; [cbn; lia|].
  unfold vm_backing_used. rewrite Evm, Hl, Hm. cbn. lia.
Qed.
End MODEL.
