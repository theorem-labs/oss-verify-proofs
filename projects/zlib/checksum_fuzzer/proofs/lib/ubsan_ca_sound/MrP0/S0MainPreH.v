(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Import Vdso.   (* port727: the vDSO pair's page counts *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require PropExec CatExec SeqExec StepTac StoreOk StreamSim WsegFast Frame MemSplit StartupTac ArgvEnv RefLayout DrawDefs
  S0StartupDefs S0Startup S0StartupFacts S0ExitBase.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM02. Import MM02. Import MM02.Malloc_ifaceP.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Tac Image InitMem Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Plain Require Import PImg RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require RunHit.  (* miss kit, as S8MainPreH *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Plain Require PImgRun.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import PState. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KInv. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KLink. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Mr Require Import MrFeasNull MrRoom.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.MrP0 Require Import S0HBase S0HConv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module SD := OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.S0StartupDefs.
Module SS := OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.S0Startup.
Module SF := OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.S0StartupFacts.
(* port727 (): the image's entry pc, as S0MainEntry names it (the entry block's AT_ENTRY). *)
Local Notation ENT := (Z_to_bv 64 (Z.of_N Src_zlib_checksum_fuzzer_repro.M.init_pc)) (only parsing).

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

Section ME.
Context {rc : runConstT}.
(* port727 (): over the launch input, as S0Startup.Consumers: argv / envp / uid / AT_HWCAP are its
   fields; the launch facts are the ruled VLAUNCH + LOK (valid_launch, entry_launch_ok_va). *)
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
Hypothesis ME : SS.main_entry sp0 inp mbase rdraw tid regs mem.
Hypothesis HCAN : CAN = DrawDefs.canary_w rdraw.
Hypothesis HSEC : SECRET = bv_unsigned (DrawDefs.secret_w rdraw).
Hypothesis HATOP : ATOP = bv_unsigned sp0 - 8388608.
Hypothesis Hve : valid_envp ev.
Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
(* port727 (): the launch facts me_rauxv reads (the auxv via RefLayout), after Hal, in the order of
   S8MainPreH , so that the S8 read chain carries back by analogy. *)
Variable brk : word.
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
Variable M : word -> option byte.
Hypothesis AG : forall a : word, bv_unsigned a < 0x51000 -> M a = mem a.
Hypothesis AGv : forall a : word, bv_unsigned a < bv_unsigned sp0 - 8388608 -> M a = mem a.   (* below the 8 MiB stack area, where the vDSO pair lies *)
Hypothesis AGhi : forall a : word, bv_unsigned sp0 <= bv_unsigned a -> M a = mem a.
Hypothesis GR : OS.mem_grows mem M.

Lemma D_main_none : forall a : word,
  bv_unsigned a < 0x1f9b0 \/ 0x4fe00 <= bv_unsigned a -> SD.D_main sp0 inp rdraw tid a = None.
Proof.
  intros a Ha. unfold SD.D_main, SD.D_fd, SD.D_ssp, SD.D_tls, SD.D_tlsB, SD.D_tlsA, SD.D_libc.
  repeat (rewrite MemSplit.wbytes_outside;
          [ | rewrite ?CatExec.length_N_to_le_bytes; cbn [length]; rewrite unsigned_lit by lia; lia
            | rewrite ?CatExec.length_N_to_le_bytes; cbn [length]; rewrite unsigned_lit by lia; lia ]).
  reflexivity.
Qed.

Lemma D_main_none_gen : forall a : word,
  Forall (fun c : Z * nat => bv_unsigned a < fst c \/ fst c + Z.of_nat (snd c) <= bv_unsigned a) SF.D_main_cells ->
  SD.D_main sp0 inp rdraw tid a = None.
Proof.
  intros a HF. unfold SF.D_main_cells in HF.
  repeat (apply Forall_cons_iff in HF; destruct HF as [?C HF]). clear HF.
  cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ] in *.
  unfold SD.D_main, SD.D_fd, SD.D_ssp, SD.D_tls, SD.D_tlsB, SD.D_tlsA, SD.D_libc.
  repeat (rewrite MemSplit.wbytes_outside;
          [ | rewrite ?CatExec.length_N_to_le_bytes; cbn [length]; rewrite unsigned_lit by lia; lia
            | rewrite ?CatExec.length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite unsigned_lit by lia; lia ]).
  reflexivity.
Qed.

Lemma me_below : forall a : word, bv_unsigned a < 0x51000 -> M a = SD.D_main sp0 inp rdraw tid a.
Proof.
  intros a Ha. rewrite AG by exact Ha. apply (SS.main_entry_mem_data sp0 inp mbase rdraw tid regs mem ME).
  rewrite CatExec.stack_max_size_val. lia.
Qed.

Lemma me_none_gen : forall a : Z, 0 <= a < 0x51000 ->
  Forall (fun c : Z * nat => a < fst c \/ fst c + Z.of_nat (snd c) <= a) SF.D_main_cells ->
  M (Z_to_bv 64 a) = None.
Proof.
  intros a Ha HF. rewrite me_below by (rewrite unsigned_lit by lia; lia). apply D_main_none_gen.
  rewrite unsigned_lit by lia. exact HF.
Qed.

Lemma me_statics_none : forall a : word, 0x4fe00 <= bv_unsigned a < 0x501a8 -> M a = None.
Proof. intros a Ha. rewrite me_below by lia. apply D_main_none. lia. Qed.

(* over the launch's own run (the section's RC_a1_1), M holds no
   byte on a read-only range: not on the image's (D_main is None there), nor on the vDSO pair, which lies below
   sp0 - 8 MiB, where M = mem (AGv) = D_main (main_entry_mem_data) = None. *)
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
  destruct (Z_lt_le_dec (bv_unsigned a) 0x51000) as [L|L].
  - destruct (Z_lt_le_dec (bv_unsigned a) 0x10000) as [L0|L0].
    + exfalso. rewrite me_below in Hab by lia. rewrite D_main_none in Hab by lia. discriminate.
    + rewrite S0HBase.run_ro_addr_img by lia. rewrite p_ro_addr.
      destruct (Z.leb_spec0 0x10000 (bv_unsigned a)) as [H1|H1]; [|reflexivity].
      destruct (Z.ltb_spec0 (bv_unsigned a) 0x1e000) as [H2|H2]; [|reflexivity].
      exfalso. rewrite me_below in Hab by lia. rewrite D_main_none in Hab by lia. discriminate.
  - destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned sp0 - 8388608)) as [L1|L1].
    + exfalso. rewrite AGv in Hab by lia.
      rewrite (SS.main_entry_mem_data sp0 inp mbase rdraw tid regs mem ME) in Hab
        by (rewrite CatExec.stack_max_size_val; lia).
      rewrite D_main_none in Hab by lia. discriminate.
    + apply PImgRun.run_ref_ro_addr_false; [lia|]. right; right.
      pose proof (VT rc_sp rc_mb) as V. change (bv_unsigned (@rc_sp RC_a1_1)) with (bv_unsigned sp0) in V. lia.
Qed.

Lemma me_rdn : forall (a : Z) (n : nat), 0 <= a -> a + Z.of_nat n <= 0x51000 ->
  OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (wa a) n = OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) (SD.D_main sp0 inp rdraw tid) (wa a) n.
Proof.
  intros a n Ha Hn.
  rewrite <- (SS.main_entry_rdn_data sp0 inp mbase rdraw tid regs mem ME)
    by (rewrite CatExec.stack_max_size_val; unfold wa; rewrite unsigned_lit by lia; lia).
  apply OP.rdn_ext; [unfold wa; rewrite unsigned_lit by lia; lia|].
  intros x Hx. unfold wa in Hx. rewrite unsigned_lit in Hx by lia. apply AG. lia.
Qed.

Ltac dm_unfold := unfold SD.D_main, SD.D_fd, SD.D_ssp, SD.D_tls, SD.D_tlsB, SD.D_tlsA, SD.D_libc.
Let D := SD.D_main sp0 inp rdraw tid.

Lemma len_av' : 1 <= Z.of_nat (length av) <= 1024.
Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

Lemma D_hit_cdt : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) D (Z_to_bv 64 0x4fd90) 1 = Some [Z_to_bv 8 1].
Proof.
  pose proof (bv_unsigned_in_range 64 tid). pose proof len_av'. subst D. dm_unfold. StartupTac.peel.
  apply (SeqExec.rdn_wbytes_hit (run_segments psegs rc_inp rc_sp rc_mb) [Z_to_bv 8 1]). cbn [length]. rewrite unsigned_lit by lia. lia.
Qed.

Lemma D_hit_auxv : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) D (Z_to_bv 64 0x4fd98) 8 = Some (word_to_le_bytes 8 (SD.auxv_w sp0 inp)).
Proof.
  pose proof (bv_unsigned_in_range 64 tid). pose proof len_av'. subst D. dm_unfold. StartupTac.peel.
  apply SeqExec.rdn_wbytes_hit8. rewrite unsigned_lit by lia. lia.
Qed.

Lemma D_hit_tls_size : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) D (Z_to_bv 64 0x4fda8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe0)).
Proof.
  pose proof (bv_unsigned_in_range 64 tid). pose proof len_av'. subst D. dm_unfold. StartupTac.peel.
  apply SeqExec.rdn_wbytes_hit8. rewrite unsigned_lit by lia. lia.
Qed.

Lemma D_hit_tls_align : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) D (Z_to_bv 64 0x4fdb0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 8)).
Proof.
  pose proof (bv_unsigned_in_range 64 tid). pose proof len_av'. subst D. dm_unfold. StartupTac.peel.
  apply SeqExec.rdn_wbytes_hit8. rewrite unsigned_lit by lia. lia.
Qed.

Ltac bytes_eq :=
  vm_compute; apply f_equal; repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]); reflexivity.

Lemma me_hit : forall a n bs, 0 <= a -> a + Z.of_nat n <= 0x51000 ->
  OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) D (Z_to_bv 64 a) n = Some bs -> OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (wa a) n = Some bs.
Proof. intros a n bs Ha Hn H. rewrite me_rdn by lia. exact H. Qed.

Lemma me_miss : forall a n bs, SF.D_main_missb a n = true ->
  OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 a) n = Some bs -> OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (wa a) n = Some bs.
Proof.
  intros a n bs Hb H.
  assert (Hr : 0 <= a /\ a + Z.of_nat n <= 0x51000).
  { unfold SF.D_main_missb in Hb. apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [_ H1].
    apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
  rewrite me_rdn by lia. unfold wa. rewrite (SF.D_main_miss sp0 inp rdraw tid (run_segments psegs rc_inp rc_sp rc_mb) a n Hb). exact H.
Qed.

Lemma sok_rw2 {RCa1 : RunCtx}  : forall (m : word -> option byte) a (n : nat), 0x1f000 <= a -> a + Z.of_nat n <= 0x51000 ->
  store_ok (run_segments psegs rc_inp rc_sp rc_mb) m (wa a) n = true.
Proof. intros m a n Ha Hn. apply S0ExitBase.store_ok_data; unfold wa; rewrite unsigned_lit by lia; lia. Qed.

Lemma wseg_rw1 {RCa1 : RunCtx}  : StreamSim.wseg_ok (run_segments psegs rc_inp rc_sp rc_mb) (Z_to_bv 64 0x1e000) (Z.to_nat (0x1f000 - 0x1e000)) = true.
Proof. apply WsegFast.wseg_fast_sound. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma sok_rw1 {RCa1 : RunCtx}  : forall (m : word -> option byte) a (n : nat), 0x1e000 <= a -> a + Z.of_nat n <= 0x1f000 ->
  store_ok (run_segments psegs rc_inp rc_sp rc_mb) m (wa a) n = true.
Proof.
  intros m a n Ha Hn.
  eapply (StoreOk.store_ok_window (run_segments psegs rc_inp rc_sp rc_mb) m (Z_to_bv 64 0x1e000) (wa a) (Z.to_nat (0x1f000 - 0x1e000)) n 0x1e000 0x1f000);
    [ apply unsigned_lit; lia | reflexivity | lia | exact wseg_rw1
    | unfold wa; rewrite unsigned_lit by lia; lia | unfold wa; rewrite unsigned_lit by lia; lia ].
Qed.

Lemma me_cell {RCa1 : RunCtx}  : forall A c, cell_wf c -> 0x1e000 <= A -> A + Z.of_nat (csize c) <= 0x51000 ->
  (A + Z.of_nat (csize c) <= 0x1f000 \/ 0x1f000 <= A) ->
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

Lemma me_libc1 : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x4fd90 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)].
Proof.
  change [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)]
    with ([C1 (Z_to_bv 8 1)] ++ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)]).
  apply (proj2 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M _ _ _)). split.
  - cell_hit D_hit_cdt.
  - cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
    apply rw_cells_of_rdn_gen; [cbn; tauto | | apply sok_rw2; cbn; lia | lia | cbn; lia].
    cbn [cells_size csize Nat.add]. apply me_miss; [vm_compute; reflexivity | bytes_eq].
Qed.

Lemma me_libc2 : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x4fd98
  [C8 (SD.auxv_w sp0 inp); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)].
Proof.
  apply (proj2 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M 0x4fd98 [C8 (SD.auxv_w sp0 inp)] _)). split; [cell_hit D_hit_auxv|].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M 0x4fda0 [C8 (Z_to_bv 64 0)] _)). split; [cell_miss|].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M 0x4fda8 [C8 (Z_to_bv 64 224)] _)). split; [cell_hit D_hit_tls_size|].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M 0x4fdb0 [C8 (Z_to_bv 64 8)] _)). split; [cell_hit D_hit_tls_align|].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M 0x4fdb8 [C8 (Z_to_bv 64 0)] _)). split; [cell_miss|].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M 0x4fdc0 [C8 (Z_to_bv 64 4096)] _)). split.
  - cell_hit (SF.D_main_pagesize sp0 inp rdraw tid Hva (run_segments psegs rc_inp rc_sp rc_mb)).
  - cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add]. cell_miss.
Qed.

Lemma me_got_ssp : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x1e780 [C8 (Z_to_bv 64 0x4fd70)].
Proof. cell_miss. Qed.

Lemma me_guard : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x4fd70 [C8 CAN].
Proof. rewrite HCAN. cell_hit (SF.D_main_guard_w sp0 inp rdraw tid (run_segments psegs rc_inp rc_sp rc_mb)). Qed.

Theorem main_entry_RHEAP :
  RHEAP (ps_init (reservedZ psegs ++ RunHit.vdso_resvZ rc_inp rc_sp rc_mb) ATOP) [] M /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M RAUXV_CELL [C8 (SD.auxv_w sp0 inp)].
Proof.
  apply RHEAP_init_proof.
  - exact me_statics_none.
  - exact me_libc1.
  - exact me_libc2.
  - exact me_got_ssp.
  - exact me_guard.
  - exact me_mem_inv.
Qed.

Lemma me_tid : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 0x2fa58) 4 = Some (word_to_le_bytes 4 tid).
Proof. apply (me_hit 0x2fa58 4); [lia | cbn; lia | exact (SF.D_main_tid sp0 inp rdraw tid (run_segments psegs rc_inp rc_sp rc_mb))]. Qed.

Lemma me_errno : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M RERRNO [C4 (Z_to_bv 64 0)].
Proof. unfold RERRNO. cell_miss. Qed.

(* port727 (): the ruled stack WINDOW [sp0 - 6144513, sp0) (S0Startup.main_entry_store_ok_win), not
   the whole 8 MiB below sp0. *)
Lemma me_stk : forall hi, hi <= bv_unsigned sp0 -> stk (run_segments psegs rc_inp rc_sp rc_mb) M (bv_unsigned sp0 - 6144513) hi.
Proof.
  intros hi Hhi'. apply stk_of_store_ok; [lia | lia |]. intros a Ha.
  eapply OS.store_ok_mono; [exact GR|].
  apply (SS.main_entry_store_ok_win sp0 inp mbase rdraw tid regs mem ME (run_segments psegs rc_inp rc_sp rc_mb) (wa a) 1);
    unfold wa; rewrite unsigned_lit by lia; cbn; lia.
Qed.

(* port727 (): above sp0 the memory is the entry block of the launch (ArgvEnv's wmem over the
   entry stack image of inp / mbase / the image's phdrs and entry). *)
Lemma me_rdn_above : forall (a : word) n, bv_unsigned sp0 <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2^64 ->
  OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M a n = OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) (stack_to_mem sp0 (entry_stack_image inp mbase SF.RPH ENT sp0 rdraw)) a n.
Proof.
  intros a n Ha Hn.
  rewrite <- (ArgvEnv.rdn_wmem_stack (run_segments psegs rc_inp rc_sp rc_mb) inp mbase SF.RPH ENT sp0 rdraw a n Ha Hn). unfold ArgvEnv.wmem.
  rewrite <- (SS.main_entry_rdn_above sp0 inp mbase rdraw tid regs mem ME (run_segments psegs rc_inp rc_sp rc_mb) a n Ha Hn).
  apply OP.rdn_ext; [exact Hn|]. intros x Hx. apply AGhi. lia.
Qed.

(* port727 (): the auxv at is StackLayout.auxv_entries' (27 or 29 pairs: ARCH_DLINFO's ten
   first, the CONFIG_RSEQ pair last); Plain/RMallocTree's rauxv_ok takes it as (vs, r, rnd): the 25 values other
   than AT_RANDOM's in order, the launch's rseq bit and AT_RANDOM (CHANGE-LIST row 40, the donor's rauxv_ok_init). *)
Lemma me_rauxv : rauxv_ok M (bv_unsigned sp0).
Proof.
  pose proof len_av' as LA. pose proof Hve as Hve'. destruct Hve' as [LE _].
  pose proof (RefLayout.rnd_facts (run_segments psegs rc_inp rc_sp rc_mb) Sv48 inp mbase SF.RPH ENT sp0 brk rdraw) as RF.
  repeat (specialize (RF ltac:(first [assumption | unfold sp_window_lo, sp_window_hi; lia]))).
  destruct RF as (R1 & R2 & R3 & R4 & R5).
  pose proof (RefLayout.read_auxv_all (run_segments psegs rc_inp rc_sp rc_mb) Sv48 inp mbase SF.RPH ENT sp0 brk rdraw) as RA.
  repeat (specialize (RA ltac:(first [assumption | unfold sp_window_lo, sp_window_hi; lia]))).
  set (rnd := at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev) in *.
  set (VS := map bv_unsigned
               [la_sysinfo_ehdr (launch_auxv inp sp0 mbase); cw_l1i_size (la_cache (launch_auxv inp sp0 mbase));
                cw_l1i_geom (la_cache (launch_auxv inp sp0 mbase)); cw_l1d_size (la_cache (launch_auxv inp sp0 mbase));
                cw_l1d_geom (la_cache (launch_auxv inp sp0 mbase)); cw_l2_size (la_cache (launch_auxv inp sp0 mbase));
                cw_l2_geom (la_cache (launch_auxv inp sp0 mbase)); cw_l3_size (la_cache (launch_auxv inp sp0 mbase));
                cw_l3_geom (la_cache (launch_auxv inp sp0 mbase)); la_minsigstksz (launch_auxv inp sp0 mbase);
                hw; Z_to_bv 64 4096; Z_to_bv 64 100; Z_to_bv 64 (Z.of_N (ph_addr SF.RPH));
                Z_to_bv 64 (Z.of_N (ph_ent SF.RPH)); Z_to_bv 64 (Z.of_N (ph_num SF.RPH)); Z_to_bv 64 0; Z_to_bv 64 0;
                ENT; uid; uid; in_gid inp; in_gid inp; Z_to_bv 64 0; at_execfn_ptr (ed_top rdraw) (in_execfn inp)]).
  assert (LR : Z.of_nat (length (rauxv_list VS (kb_rseq (in_kernel inp)) (bv_unsigned rnd)))
               = 2 * Z.of_nat (auxv_count (kb_rseq (in_kernel inp)))).
  { unfold rauxv_list, auxv_count. rewrite length_map. destruct (kb_rseq (in_kernel inp)); reflexivity. }
  assert (AC : (auxv_count (kb_rseq (in_kernel inp)) <= 29)%nat)
    by (unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia).
  assert (AS : auxv_size (kb_rseq (in_kernel inp)) = (16 * auxv_count (kb_rseq (in_kernel inp)))%nat) by reflexivity.
  assert (AU : bv_unsigned (SD.auxv_w sp0 inp) = bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
  { unfold SD.auxv_w. apply unsigned_lit. lia. }
  exists (bv_unsigned (SD.auxv_w sp0 inp)), VS, (kb_rseq (in_kernel inp)), (bv_unsigned rnd).
  split; [|split; [|split]].
  -
    unfold MallocRep.wz. rewrite Z_to_bv_bv_unsigned. exact (proj2 main_entry_RHEAP).
  - (* the vector, read off the entry block *)
    apply (bytes_at_of_rdn (auxv_size (kb_rseq (in_kernel inp)))); [ | lia | rewrite AS; lia].
    unfold wa. rewrite Z_to_bv_bv_unsigned.
    change (rdn (run_segments psegs rc_inp rc_sp rc_mb) M (SD.auxv_w sp0 inp) (auxv_size (kb_rseq (in_kernel inp)))
              = Some (u64s (rauxv_list VS (kb_rseq (in_kernel inp)) (bv_unsigned rnd))))
      with (OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (SD.auxv_w sp0 inp) (auxv_size (kb_rseq (in_kernel inp)))
              = Some (u64s (rauxv_list VS (kb_rseq (in_kernel inp)) (bv_unsigned rnd)))).
    rewrite me_rdn_above by (rewrite ?AS; lia).
    replace (SD.auxv_w sp0 inp) with (sp0 + nat_to_word (RefLayout.auxv_off av ev))%bv.
    2:{ unfold SD.auxv_w, RefLayout.auxv_off. rewrite StepTac.word_add_nat. f_equal. lia. }
    rewrite RA. f_equal.
    unfold VS, rauxv_list, auxv_bytes, auxv_entries, MallocRep.wz.
    change (la_rseq (launch_auxv inp sp0 mbase)) with (kb_rseq (in_kernel inp)).
    destruct (kb_rseq (in_kernel inp)); cbn [map u64s build_auxv fst snd app nth]; unfold le8;
      rewrite !Z_to_bv_bv_unsigned; fold rnd; reflexivity.
  -
    apply (bytes_at_of_rdn 8); [ | lia | lia].
    change (OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (wa (bv_unsigned rnd + 8)) 8 = Some (le8 (wz SECRET))).
    unfold wa. rewrite me_rdn_above by (rewrite unsigned_lit by lia; lia).
    rewrite (R5 8%nat 8%nat ltac:(lia)). f_equal.
    unfold le8, MallocRep.wz, wz. rewrite HSEC, Z_to_bv_bv_unsigned, DrawDefs.w8_secret. reflexivity.
  - rewrite LR. pose proof (bv_unsigned_in_range 64 rnd).
    unfold bv_modulus in *. repeat split; try lia.
Qed.
End ME.

Section MODEL.
Context {rc : runConstT}.

Lemma reserved_top_ge : forall l e, In e l -> bv_unsigned (fst e) + bv_unsigned (snd e) <= reserved_top l.
Proof.
  induction l as [|[a sz] l IH]; intros e Hin; [destruct Hin|].
  cbn [reserved_top]. destruct Hin as [<-|Hin]; cbn [fst snd]; [lia|]. specialize (IH e Hin). lia.
Qed.

(* port727 (): KL reads minv, the halt state, the VmMaps and the kernel build (kl_vin), so it carries
   to any model that agrees on those four. The run's model at main is with_tid / with_vdso over init_model (and
   with_fds after an open), none of which touches them. *)
Lemma KL_transfer : forall L b mo mo', KL L b mo ->
  minv mo' -> m_halted mo' = m_halted mo -> m_vmmaps mo' = m_vmmaps mo -> m_kernel mo' = m_kernel mo -> KL L b mo'.
Proof. intros L b mo mo' K MI Eh Ev Ek. destruct K. constructor; rewrite ?Eh, ?Ev, ?Ek; assumption. Qed.

(* port727 (): the launch's ledger fact is KLink.KL_init over init_model (the ledger keeps the
   image's segments, reservedZ psegs; the model's vm_reserved adds the vDSO pair, State.init_reserved, which KL's
   kl_resv / kl_vin carry), moved to [mo] by KL_transfer. *)
Lemma KL_init_vm : forall (mo : Model) (brk0 mbase sp : word) lim inp,
  m_vmmaps mo = m_vmmaps (init_model (segments_reserved psegs) brk0 mbase sp lim inp) ->
  m_kernel mo = in_kernel inp ->
  minv mo -> m_halted mo = None ->
  valid_brk psegs brk0 ->
  sp_window_lo <= bv_unsigned sp <= sp_window_hi ->
  mmap_base_min <= bv_unsigned mbase -> in_channel_reader inp = true ->
  KL (led_init (reservedZ psegs ++ RunHit.vdso_resvZ inp sp mbase) (bv_unsigned sp - stack_max_size)) 0 mo.  (* the ledger holds the vDSO pair *)
Proof.
  intros mo brk0 mbase sp lim inp Evm Ek MI Eh Hb Hsp Hmb Hrdr.
  apply (KL_transfer _ _ (init_model (segments_reserved psegs) brk0 mbase sp lim inp) mo);
    [ | exact MI | rewrite Eh; reflexivity | exact Evm | rewrite Ek; reflexivity ].
  apply (KL_init_full psegs brk0 mbase sp lim inp (reservedZ psegs ++ RunHit.vdso_resvZ inp sp mbase) (bv_unsigned sp - stack_max_size) 0);
    [ reflexivity | exact Hb | rewrite reserved_top_plain; lia | exact Hsp | reflexivity
    | rewrite reserved_top_plain, alloc_ceiling_lo_val; unfold brk_aslr_max, PGSZ; lia
    | rewrite reserved_top_plain; unfold brk_aslr_max; lia | exact Hmb | exact Hrdr ].
Qed.

(* port727 (): premise order as S8MainPreH (ATOP before the launch band and
   the reader), so the S8 read chain's calls carry back unchanged. *)
Lemma OWN_init_vm : forall (G : PState -> Model -> Prop) (mo : Model) (brk0 mbase sp : word) lim inp,
  m_vmmaps mo = m_vmmaps (init_model (segments_reserved psegs) brk0 mbase sp lim inp) ->
  m_kernel mo = in_kernel inp ->
  minv mo -> m_halted mo = None -> valid_brk psegs brk0 ->
  sp_window_lo <= bv_unsigned sp <= sp_window_hi ->
  ATOP = bv_unsigned sp - stack_max_size ->
  mmap_base_min <= bv_unsigned mbase -> in_channel_reader inp = true ->
  G (ps_init (reservedZ psegs ++ RunHit.vdso_resvZ inp sp mbase) ATOP) mo ->
  OWN [] G (ps_init (reservedZ psegs ++ RunHit.vdso_resvZ inp sp mbase) ATOP) mo.
Proof.
  intros G mo brk0 mbase sp lim inp Evm Ek MI Eh Hb Hsp Ea Hmb Hrdr HG. split; [|split; [constructor | exact HG]].
  exists (led_init (reservedZ psegs ++ RunHit.vdso_resvZ inp sp mbase) ATOP). split; [|split].
  - apply creach_init. pose proof atop_range. unfold atop_hi. lia.
  - rewrite Ea. exact (KL_init_vm mo brk0 mbase sp lim inp Evm Ek MI Eh Hb Hsp Hmb Hrdr).
  - intros x [].
Qed.

Lemma allnone_init : forall resv atop, allnone (ps_m (ps_init resv atop)).
Proof. intros resv atop sc. reflexivity. Qed.

(* port727 (): the vDSO pair's two entries are small (State.vdso_reserved). *)
Lemma vdso_reserved_small : forall kb top,
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30) (vdso_reserved kb top) /\ (length (vdso_reserved kb top) <= 2)%nat.
Proof.
  intros kb top. unfold vdso_reserved. cbv zeta.
  match goal with |- context [if ?c then _ else _] => destruct c end; [split; [constructor | cbn; lia]|].
  pose proof (vdso_text_pages_pos kb). pose proof (vdso_text_pages_le kb).
  unfold vdso_vvar_pages, page_size. split; [|cbn [length]; lia].
  repeat constructor; cbn [snd]; rewrite unsigned_lit by lia; lia.
Qed.

(* port727 (): the launch's reserved list is the image's segments then the vDSO pair. *)
Lemma room_init_vm : forall (mo : Model) (brk0 mbase sp : word) lim B kb,
  m_vmmaps mo = mkVmMapsFull (init_reserved (segments_reserved psegs) mbase sp kb) [] [] brk0 brk0 lim mbase sp ->
  m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  sp_window_lo <= bv_unsigned sp -> B + 4096 <= lim ->
  room B mo.
Proof.
  intros mo brk0 mbase sp lim B kb Evm Hl Hm Hsp HB. unfold room. rewrite Evm. cbn [vm_reserved vm_maps vm_init_sp vm_limit].
  split; [exact Hsp|]. rewrite app_nil_r. unfold init_reserved. rewrite segments_reserved_plain.
  match goal with |- context [vdso_reserved ?k ?t] => destruct (vdso_reserved_small k t) as [VS VL] end.
  split; [apply Forall_app; split; [repeat constructor; cbn [snd]; rewrite unsigned_lit by lia; lia | exact VS]|].
  split; [rewrite length_app; cbn [length] in *; lia|].
  unfold vm_backing_used. rewrite Evm, Hl, Hm. cbn. lia.
Qed.
End MODEL.
