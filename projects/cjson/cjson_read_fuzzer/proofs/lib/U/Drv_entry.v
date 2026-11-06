(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PropExec StepTac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require UStartup UStartupDefs UStartupFacts Amb MmapSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import InitMem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import Malloc_ifaceP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import CJ_iface F_pad Exit F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_piface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_piface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import Drv_base.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Module F := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.
Module CE := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.WallSim.CatExec.
Module RL := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.RefLayout.
Module FS := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.FileSim.
Module AE := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.ArgvEnv.
Module PS := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.UStartup.
Module PD := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.UStartupDefs.
Module PF := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.UStartupFacts.
Module MSP := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.MemSplit.
Module ST := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.StartupTac.
Module SE := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.WallSim.SeqExec.
Module SSP := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.StartupSsp.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_flat : forall segs m a n, F.rdn segs m a n = rdn segs m a n.
Proof.
  intros segs m a n. revert a. induction n as [|n IH]; intros a; [reflexivity|].
  cbn [rdn F.rdn]. rewrite IH. reflexivity.
Qed.

Lemma rdn_bytes_at : forall segs m (a : Z) bs,
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  rdn segs m (wa a) (length bs) = Some bs -> bytes_at segs m a bs.
Proof.
  intros segs m a bs Ha Hb H. split; [exact Ha|]. split; [exact Hb|].
  revert a Ha Hb H. induction bs as [|b bs IH]; intros a Ha Hb H i Hi; [cbn in Hi; lia|].
  cbn [length] in Hb, Hi. rewrite rdn_unfold in H. cbn [length] in H.
  destruct (mrd segs m (wa a)) as [b'|] eqn:Eb; [|discriminate].
  rewrite wa_succ in H.
  destruct (rdn segs m (wa (a + 1)) (length bs)) as [r|] eqn:Er; [|discriminate].
  injection H as Hbb Hr. subst b' r.
  destruct i as [|i].
  - rewrite Z.add_0_r. exact Eb.
  - cbn [nth_error]. replace (a + Z.of_nat (S i)) with ((a + 1) + Z.of_nat i) by lia.
    apply (IH (a + 1)); [lia| lia| exact Er| lia].
Qed.

(* [comment removed for export] *)
Lemma wview_overlay_mono : forall segs (m : word -> option byte) a,
  wview segs (fun _ => None) a <> None -> wview segs m a <> None.
Proof. intros segs m a H. unfold wview in *. destruct (m a); [discriminate| exact H]. Qed.

Lemma wview_some : forall segs (m : word -> option byte) a b, m a = Some b -> wview segs m a <> None.
Proof. intros segs m a b H. unfold wview. rewrite H. discriminate. Qed.

Lemma mrd_some : forall segs (m : word -> option byte) a b, m a = Some b -> mrd segs m a = Some b.
Proof. intros segs m a b H. unfold mrd. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint wr_b (A : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match wview usegs (fun _ => None) (wa A) with Some _ => wr_b (A + 1) n' | None => false end
  end.

Lemma wr_b_sound : forall n A m, wr_b A n = true -> 0 <= A -> A + Z.of_nat n <= 2^64 -> wr_at usegs m A (Z.of_nat n).
Proof.
  induction n as [|n IH]; intros A m Hb HA Hn.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
  - cbn [wr_b] in Hb. destruct (wview usegs (fun _ => None) (wa A)) as [b|] eqn:E; [|discriminate].
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.eq_dec i 0) as [->|NE].
    + rewrite Z.add_0_r. apply wview_overlay_mono. rewrite E. discriminate.
    + replace (A + i) with ((A + 1) + (i - 1)) by lia. apply (IH (A + 1) m Hb); lia.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_of_bytes : forall m A cs,
  cells_wf cs -> bytes_at usegs m A (cells_bytes cs) -> wr_at usegs m A (Z.of_nat (cells_size cs)) -> rw_cells usegs m A cs.
Proof. intros m A cs Hwf HB HW. split; [split; [exact Hwf| exact HB]| exact HW]. Qed.

Lemma rw_cells_bytes : forall m A cs, rw_cells usegs m A cs -> bytes_at usegs m A (cells_bytes cs).
Proof. intros m A cs [[_ HB] _]. exact HB. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Entry.
  Context {AMB : Amb.Amb}.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable tid : word.
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : PS.u_main_entry sp0 rnd av ev tid regs mem.
  Hypothesis VA : valid_argv av.
  Hypothesis VE : valid_envp ev.
  Hypothesis VSP : valid_sp sp0.
  Hypothesis FITS : entry_stack_fits sp0 av ev.   (* [comment removed for export] *)
  Hypothesis HCEIL : alloc_ceiling <= bv_unsigned sp0 - 8388608.   (* [comment removed for export] *)
  Hypothesis HSEC : malloc_secret_val = rnd_secret (ed_random rnd).   (* [comment removed for export] *)

  Lemma usp_lo : 0x7fff80000000 <= bv_unsigned sp0.
  Proof. (nelimp VSP 3%nat; intros H _ _). unfold sp_window_lo in H. exact H. Qed.
  Lemma usp_hi : bv_unsigned sp0 <= 0x800000000000.
  Proof. (nelimp VSP 3%nat; intros _ H _). unfold sp_window_hi in H. exact H. Qed.
  Lemma usp_al : bv_unsigned sp0 mod 16 = 0.
  Proof. (nelimp VSP 3%nat; intros _ _ H). exact H. Qed.

  (* [comment removed for export] *)
  Definition bsb : list byte := build_stack_bytes Ubsan.M.phdrs sp0 av ev Amb.a_uid Amb.a_hwcap rnd.
  Definition LB : Z := Z.of_nat (length bsb).
  (* [comment removed for export] *)
  Definition SIMG : list byte := entry_stack_image Ubsan.M.phdrs sp0 av ev Amb.a_uid Amb.a_hwcap rnd.

  Lemma img_len_ge : LB <= Z.of_nat (length SIMG).
  Proof using ACEIL. unfold LB, SIMG, entry_stack_image. cbv zeta. fold bsb. rewrite length_app. lia. Qed.

  Lemma img_top : bv_unsigned sp0 + Z.of_nat (length SIMG) <= 0x800000000000.
  Proof using ACEIL FITS.
    unfold SIMG. rewrite (entry_stack_image_top Ubsan.M.phdrs sp0 av ev Amb.a_uid Amb.a_hwcap rnd).
    pose proof (F.entry_page_top_within_window Ubsan.M.phdrs sp0 av ev Amb.a_uid Amb.a_hwcap rnd FITS) as T.
    unfold sp_window_hi in T. exact T.
  Qed.

  (* [comment removed for export] *)
  Lemma img_top2 : bv_unsigned sp0 + Z.of_nat (length SIMG) <= bv_unsigned sp0 + LB + 4096.
  Proof using ACEIL.
    clear HCEIL HSEC FITS.   (* [comment removed for export] *)
    unfold SIMG. rewrite (entry_stack_image_top Ubsan.M.phdrs sp0 av ev Amb.a_uid Amb.a_hwcap rnd).
    unfold entry_page_top, entry_block_top, page_round_up_Z, page_size. fold bsb. unfold LB.
    pose proof (Z.mod_pos_bound (bv_unsigned sp0 + Z.of_nat (length bsb) + 4096 - 1) 4096 ltac:(lia)) as Hb.
    pose proof (Z.div_mod (bv_unsigned sp0 + Z.of_nat (length bsb) + 4096 - 1) 4096 ltac:(lia)) as Hd.
    lia.
  Qed.


  (* [comment removed for export] *)
  Lemma entry_mem_data : forall a : word, bv_unsigned a < 0x56000 -> mem a = PD.D_main sp0 av ev Amb.a_hwcap rnd tid a.
  Proof.
    intros a Ha. apply (PS.main_entry_mem_data sp0 av ev tid rnd regs mem ME).
    rewrite CE.stack_max_size_val. pose proof usp_lo. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_none_out : forall a : word,
    (bv_unsigned a < 0x24870 \/ 0x54cc8 <= bv_unsigned a) -> bv_unsigned a < 2^64 - 8 -> PD.D_main sp0 av ev Amb.a_hwcap rnd tid a = None.
  Proof.
    intros a Ha Hb.
    unfold PD.D_main, PD.D_fd, PD.D_ssp, PD.D_tls, PD.D_tlsB, PD.D_tlsA, PD.D_libc.
    repeat (rewrite MSP.wbytes_outside by
      (rewrite ?CE.length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite unsigned_lit by lia; lia)).
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma entry_mem_inv : mem_inv usegs mem.
  Proof.
    apply mem_inv_intro. intros a b Hab.
    destruct (Z.ltb_spec0 (bv_unsigned a) 0x56000) as [Hlt|Hge].
    - rewrite entry_mem_data in Hab by exact Hlt.
      destruct (Z.leb_spec0 0x24870 (bv_unsigned a)) as [H1|H1];
      [destruct (Z.ltb_spec0 (bv_unsigned a) 0x54cc8) as [H2|H2]|].
      + assert (FS3 : find_segment usegs (bv_unsigned a) 1 = Some Ubsan.Ubsan_segment_003).
        { unfold usegs, Ubsan.M.loaded_segments, Ubsan.Ubsan_loaded_segments. cbn [find_segment].
          replace (Z.of_N (seg_base Ubsan.Ubsan_segment_000)) with 65536%Z by (vm_compute; reflexivity).
          replace (Z.of_N (seg_size Ubsan.Ubsan_segment_000)) with 12288%Z by (vm_compute; reflexivity).
          replace (Z.of_N (seg_base Ubsan.Ubsan_segment_001)) with 77824%Z by (vm_compute; reflexivity).
          replace (Z.of_N (seg_size Ubsan.Ubsan_segment_001)) with 65536%Z by (vm_compute; reflexivity).
          replace (Z.of_N (seg_base Ubsan.Ubsan_segment_002)) with 143360%Z by (vm_compute; reflexivity).
          replace (Z.of_N (seg_size Ubsan.Ubsan_segment_002)) with 4096%Z by (vm_compute; reflexivity).
          replace (Z.of_N (seg_base Ubsan.Ubsan_segment_003)) with 147456%Z by (vm_compute; reflexivity).
          replace (Z.of_N (seg_size Ubsan.Ubsan_segment_003)) with 204800%Z by (vm_compute; reflexivity).
          destruct (Z.leb_spec0 65536 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) (65536 + 12288)); cbn [andb]; try lia.
          all: destruct (Z.leb_spec0 77824 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) (77824 + 65536)); cbn [andb]; try lia.
          all: destruct (Z.leb_spec0 143360 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) (143360 + 4096)); cbn [andb]; try lia.
          all: destruct (Z.leb_spec0 147456 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) (147456 + 204800)); cbn [andb]; try lia.
          reflexivity. }
        split; [| left; rewrite FS3; discriminate].
        unfold ro_addr. rewrite FS3. vm_compute. reflexivity.
      + rewrite D_main_none_out in Hab by lia. discriminate.
      + rewrite D_main_none_out in Hab by lia. discriminate.
    - split; [apply ref_ro_addr_false; lia| right].
      pose proof usp_hi as HI. unfold TASK_SIZE.
      destruct (Z.leb_spec0 (bv_unsigned sp0) (bv_unsigned a)) as [Ha|Ha]; [| lia].
      rewrite (PS.main_entry_mem_above sp0 av ev tid rnd regs mem ME) in Hab by lia.
      unfold F.wrap_mem in Hab. fold SIMG in Hab. unfold stack_to_mem in Hab.
      rewrite (proj2 (Z.leb_le _ _)) in Hab by lia.
      destruct (Z.ltb_spec0 (bv_unsigned a) (bv_unsigned sp0 + Z.of_nat (length SIMG))) as [Hb|Hb].
      + pose proof img_top. lia.   (* [comment removed for export] *)
      + rewrite (proj2 (Z.ltb_ge _ _)) in Hab by lia. cbn in Hab.
        rewrite (proj2 (Z.ltb_ge (bv_unsigned a) (bv_unsigned sp0))) in Hab by lia. rewrite andb_false_r in Hab. discriminate.
  Qed.


  (* [comment removed for export] *)
  Lemma entry_none : forall a : word,
    (bv_unsigned a < 0x24870 \/ 0x54cc8 <= bv_unsigned a < 0x56000) -> mem a = None.
  Proof.
    intros a Ha. rewrite entry_mem_data by lia. apply D_main_none_out; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma entry_stk : stk usegs mem (bv_unsigned sp0 - 8388608) (bv_unsigned sp0 - 48).
  Proof.
    pose proof usp_lo. pose proof usp_hi.
    split; [lia|]. split; [lia|]. intros a Ha.
    assert (NN : mem (wa a) <> None).
    { apply (PS.main_entry_win_mapped sp0 av ev tid rnd regs mem ME). rewrite CE.stack_max_size_val. rewrite wa_unsigned by lia. lia. }
    destruct (mem (wa a)) as [b|] eqn:E; [|congruence].
    split; [eapply wview_some; exact E| exists b; apply mrd_some; exact E].
  Qed.

  (* [comment removed for export] *)
  Lemma entry_none_b : forall (A : Z) (n : nat),
    PF.D_main_missb A n = true ->
    forall a : word, A <= bv_unsigned a < A + Z.of_nat n -> mem a = None.
  Proof.
    intros A n Hb a Ha. pose proof (F.u64_range tid). pose proof usp_lo. pose proof usp_hi.
    unfold PF.D_main_missb, PF.D_main_cells in Hb. cbn [forallb] in Hb.
    repeat match goal with
           | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H as [? ?]
           end.
    repeat match goal with
           | H : PF.range_disjoint_b _ _ _ = true |- _ =>
               apply PF.range_disjoint_djw in H; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ] in H
           | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
           | H : true = true |- _ => clear H
           end.
    rewrite entry_mem_data by lia.
    unfold PD.D_main, PD.D_fd, PD.D_ssp, PD.D_tls, PD.D_tlsB, PD.D_tlsA, PD.D_libc.
    repeat (rewrite MSP.wbytes_outside by
      (rewrite ?CE.length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite unsigned_lit by lia;
       lazymatch goal with
       | |- (_ \/ _) => match goal with H : PF.djw _ |- _ => clear -H Ha; unfold PF.djw in H; lia end
       | |- _ => lia
       end)).
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  Local Ltac hit8 :=
    unfold PD.D_main, PD.D_fd, PD.D_ssp, PD.D_tls, PD.D_tlsB, PD.D_tlsA, PD.D_libc; ST.peel;
    apply SE.rdn_wbytes_hit8; ST.unorm; lia.
  Local Ltac to_mem :=
    intros; rewrite (PS.main_entry_rdn_data sp0 av ev tid rnd regs mem ME) by (rewrite CE.stack_max_size_val; ST.unorm; pose proof usp_lo; lia).

  Lemma rd_self : forall segs, F.rdn segs mem (Z_to_bv 64 0x34908) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x34908)).
  Proof. to_mem. pose proof (F.u64_range tid). hit8. Qed.
  Lemma rd_next : forall segs, F.rdn segs mem (Z_to_bv 64 0x34910) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x34908)).
  Proof. to_mem. pose proof (F.u64_range tid). hit8. Qed.
  Lemma rd_prev : forall segs, F.rdn segs mem (Z_to_bv 64 0x34918) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x34908)).
  Proof. to_mem. pose proof (F.u64_range tid). hit8. Qed.
  Lemma rd_sysinfo : forall segs, F.rdn segs mem (Z_to_bv 64 0x34920) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Proof. to_mem. pose proof (F.u64_range tid). hit8. Qed.
  Lemma rd_tid : forall segs, F.rdn segs mem (Z_to_bv 64 0x34928) 4 = Some (word_to_le_bytes 4 tid).
  Proof. intros segs. apply (PF.main_entry_tid sp0 av ev tid rnd usp_lo regs mem ME). Qed.
  Lemma rd_guard : forall segs, F.rdn segs mem (Z_to_bv 64 0x54c38) 8 = Some (SSP.guard_bytes (ed_random rnd)).
  Proof. intros segs. apply (PF.main_entry_guard sp0 av ev tid rnd usp_lo regs mem ME). Qed.
  Lemma rd_cdt : forall segs, F.rdn segs mem (Z_to_bv 64 0x54c58) 1 = Some [Z_to_bv 8 1].
  Proof.
    to_mem. pose proof (F.u64_range tid).
    unfold PD.D_main, PD.D_fd, PD.D_ssp, PD.D_tls, PD.D_tlsB, PD.D_tlsA, PD.D_libc; ST.peel.
    apply (SE.rdn_wbytes_hit segs [Z_to_bv 8 1]). ST.unorm; cbn; lia.
  Qed.
  Lemma rd_auxv : forall segs, F.rdn segs mem (Z_to_bv 64 0x54c60) 8 = Some (word_to_le_bytes 8 (PD.auxv_w sp0 av ev)).
  Proof. to_mem. pose proof (F.u64_range tid). pose proof (PF.len_av av VA). hit8. Qed.
  Lemma rd_tls_size : forall segs, F.rdn segs mem (Z_to_bv 64 0x54c70) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe0)).
  Proof. to_mem. pose proof (F.u64_range tid). pose proof (PF.len_av av VA). hit8. Qed.
  Lemma rd_tls_align : forall segs, F.rdn segs mem (Z_to_bv 64 0x54c78) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 8)).
  Proof. to_mem. pose proof (F.u64_range tid). pose proof (PF.len_av av VA). hit8. Qed.
  Lemma rd_pagesize : forall segs, F.rdn segs mem (Z_to_bv 64 0x54c88) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
  Proof. to_mem. apply (PF.D_main_pagesize sp0 av ev tid rnd VA). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rd_bytes : forall (c : Z) bs,
    0 <= c -> c + Z.of_nat (length bs) <= 2^64 ->
    F.rdn usegs mem (Z_to_bv 64 c) (length bs) = Some bs -> bytes_at usegs mem c bs.
  Proof. intros c bs Hc Hb H. apply rdn_bytes_at; [lia| lia|]. unfold wa. rewrite <- rdn_flat. exact H. Qed.

  (* [comment removed for export] *)
  Lemma entry_img_chunk : forall (A : Z) (bs : list byte),
    PF.D_main_missb A (length bs) = true -> rw_bytes_b usegs A bs = true ->
    rw_cells usegs mem A [CB (length bs) bs].
  Proof.
    intros A bs Hm Hb.
    assert (HR : 0 <= A /\ A + Z.of_nat (length bs) <= 0x56000).
    { unfold PF.D_main_missb in Hm. apply andb_true_iff in Hm as [Hm H2]. apply andb_true_iff in Hm as [_ H1].
      apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
    apply rw_cells_image0; [| exact Hb| lia| lia].
    intros a Ha. apply (entry_none_b A (length bs) Hm a Ha).
  Qed.

  Local Ltac img_chunk A cs H :=
    let bs := eval vm_compute in (cells_bytes cs) in
    assert (H : rw_cells usegs mem A cs);
    [ apply (rw_cells_recast usegs mem A [CB (length bs) bs] cs);
      [ apply (entry_img_chunk A bs); [reflexivity| vm_compute; reflexivity]
      | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
    | ].

  (* [comment removed for export] *)
  Local Ltac bapp :=
    lazymatch goal with
    | |- bytes_at _ _ _ (_ ++ _) => apply (proj2 (bytes_at_app _ _ _ _ _)); split; [| cbn [length le8 le4 word_to_le_bytes Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ Nat.add];
                                     lazymatch goal with |- bytes_at _ _ ?a _ => let a' := eval vm_compute in a in change a with a' end; bapp]
    | |- bytes_at _ _ _ [] => apply bytes_at_nil; lia
    | |- _ => idtac
    end.

  (* [comment removed for export] *)
  Lemma entry_rtd : rw_cells usegs mem 0x34908 [C8 (Z_to_bv 64 0x34908); C8 (Z_to_bv 64 0x34908); C8 (Z_to_bv 64 0x34908); C8 (Z_to_bv 64 0); C4 tid].
  Proof.
    apply rw_cells_of_bytes; [cbn; repeat split; exact I| | apply (wr_b_sound 36); [vm_compute; reflexivity| lia| cbn; lia]].
    cbn [cells_bytes cbytes]. bapp.
    - apply (rd_bytes 0x34908 (le8 (Z_to_bv 64 0x34908))); [lia| cbn; lia| apply rd_self].
    - apply (rd_bytes 0x34910 (le8 (Z_to_bv 64 0x34908))); [lia| cbn; lia| apply rd_next].
    - apply (rd_bytes 0x34918 (le8 (Z_to_bv 64 0x34908))); [lia| cbn; lia| apply rd_prev].
    - apply (rd_bytes 0x34920 (le8 (Z_to_bv 64 0))); [lia| cbn; lia| apply rd_sysinfo].
    - apply (rd_bytes 0x34928 (le4 tid)); [lia| cbn; lia| apply rd_tid].
  Qed.

  (* [comment removed for export] *)
  Lemma entry_libc : rw_cells usegs mem 0x54c58 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)].
  Proof.
    img_chunk 0x54c59 [CB 7 (repeat (Z_to_bv 8 0) 7)] IMG.
    apply rw_cells_of_bytes; [cbn; repeat split; exact I| | apply (wr_b_sound 8); [vm_compute; reflexivity| lia| cbn; lia]].
    change (bytes_at usegs mem 0x54c58 ([Z_to_bv 8 1] ++ repeat (Z_to_bv 8 0) 7)).
    apply (proj2 (bytes_at_app _ _ _ _ _)); split.
    - apply (rd_bytes 0x54c58 [Z_to_bv 8 1]); [lia| cbn; lia| apply rd_cdt].
    - exact (rw_cells_bytes _ _ _ IMG).
  Qed.

  (* [comment removed for export] *)
  Lemma entry_libc2 : rw_cells usegs mem 0x54c60 [C8 (PD.auxv_w sp0 av ev); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                                               C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)].
  Proof.
    img_chunk 0x54c68 [CB 8 (repeat (Z_to_bv 8 0) 8)] I1.
    img_chunk 0x54c80 [CB 8 (repeat (Z_to_bv 8 0) 8)] I2.
    img_chunk 0x54c90 [CB 48 (repeat (Z_to_bv 8 0) 48)] I3.
    apply rw_cells_of_bytes; [cbn; repeat split; exact I| | apply (wr_b_sound 96); [vm_compute; reflexivity| lia| cbn; lia]].
    cbn [cells_bytes cbytes]. bapp.
    - apply (rd_bytes 0x54c60 (le8 _)); [lia| cbn; lia| apply rd_auxv].
    - exact (rw_cells_bytes _ _ _ I1).
    - apply (rd_bytes 0x54c70 (le8 _)); [lia| cbn; lia| apply rd_tls_size].
    - apply (rd_bytes 0x54c78 (le8 _)); [lia| cbn; lia| apply rd_tls_align].
    - exact (rw_cells_bytes _ _ _ I2).
    - apply (rd_bytes 0x54c88 (le8 _)); [lia| cbn; lia| apply rd_pagesize].
    - exact (rw_cells_bytes _ _ _ I3).
  Qed.

  (* [comment removed for export] *)
  Lemma guard_le8 : le8 (SSP.canary_w (ed_random rnd)) = SSP.guard_bytes (ed_random rnd).
  Proof.
    unfold le8, word_to_le_bytes. rewrite <- (SSP.canary_val (ed_random rnd)).
    rewrite <- (SSP.length_guard_bytes (ed_random rnd)) at 1. apply StrFun.Z_to_le_bytes_to_Z.
  Qed.
  Lemma entry_guard : rw_cells usegs mem 0x54c38 [C8 (SSP.canary_w (ed_random rnd))].
  Proof.
    apply rw_cells_of_bytes; [cbn; repeat split; exact I| | apply (wr_b_sound 8); [vm_compute; reflexivity| lia| cbn; lia]].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. apply (rd_bytes 0x54c38 (le8 _)); [lia| cbn; lia|].
    rewrite guard_le8. apply rd_guard.
  Qed.
  Lemma entry_got_ssp : rw_cells usegs mem 0x23630 [C8 (Z_to_bv 64 0x54c38)].
  Proof. img_chunk 0x23630 [C8 (Z_to_bv 64 0x54c38)] H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma entry_errno : rw_cells usegs mem 0x3492c [C4 (Z_to_bv 64 0)].
  Proof. img_chunk 0x3492c [C4 (Z_to_bv 64 0)] H. exact H. Qed.

  (* [comment removed for export] *)

  Lemma bsb_len_bound : 0 <= LB <= 2240000.
  Proof. split; [unfold LB; lia|]. unfold LB, bsb. apply (RL.lay_bsb_len _ sp0 rnd av ev _ Amb.a_hwcap VA VE). Qed.

  Lemma bsb_len_mod8 : LB mod 8 = 0.
  Proof.
    unfold LB, bsb. (nelim (RL.bsb_random_split Ubsan.M.phdrs sp0 rnd av ev Amb.a_uid Amb.a_hwcap) 4%nat; intros pre E _ Hm).
    rewrite E, length_app, length_at_random_bytes, Nat2Z.inj_add.
    rewrite Z.add_mod, Hm by lia. reflexivity.
  Qed.

  Lemma entry_above_rdn : forall (a : word) n,
    bv_unsigned sp0 <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2^64 ->
    F.rdn usegs mem a n = F.rdn usegs (stack_to_mem sp0 SIMG) a n.
  Proof.
    intros a n H1 H2. rewrite (PS.main_entry_rdn_above sp0 av ev tid rnd regs mem ME) by assumption.
    unfold SIMG. apply F.rdn_wrap_stack_above; assumption.
  Qed.

  Lemma entry_above_some : forall a : word,
    bv_unsigned sp0 <= bv_unsigned a < bv_unsigned sp0 + LB -> exists b, mem a = Some b.
  Proof.
    intros a Ha. rewrite (PS.main_entry_mem_above sp0 av ev tid rnd regs mem ME) by lia.
    unfold F.wrap_mem. fold SIMG. unfold stack_to_mem. pose proof img_len_ge.
    rewrite (proj2 (Z.leb_le _ _)) by lia. unfold LB in *. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
    destruct (nth_error SIMG (Z.to_nat (bv_unsigned a - bv_unsigned sp0))) as [b|] eqn:E; [exists b; reflexivity|].
    apply nth_error_None in E. lia.
  Qed.

  Lemma entry_above_wr : forall A n, bv_unsigned sp0 <= A -> A + n <= bv_unsigned sp0 + LB -> wr_at usegs mem A n.
  Proof.
    intros A n H1 H2. pose proof bsb_len_bound. pose proof usp_hi. pose proof usp_lo.
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (entry_above_some (wa (A + i))) as [b Hb]; [rewrite wa_unsigned by lia; lia|].
    eapply wview_some; exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma entry_above_bytes : forall (a : word) bs,
    bv_unsigned sp0 <= bv_unsigned a -> bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
    F.rdn usegs (stack_to_mem sp0 SIMG) a (length bs) = Some bs -> bytes_at usegs mem (bv_unsigned a) bs.
  Proof.
    intros a bs H1 H2 H. apply rd_bytes; [pose proof usp_lo; lia| exact H2|].
    rewrite Z_to_bv_bv_unsigned. rewrite entry_above_rdn by assumption. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma entry_argv_ptr : forall k, (k < length av)%nat ->
    rw_cells usegs mem (bv_unsigned sp0 + 8 + 8 * Z.of_nat k) [C8 (CE.cat_argv_ptr sp0 av ev k)].
  Proof.
    intros k Hk. pose proof usp_lo. pose proof usp_hi. pose proof (PF.len_av av VA).
    pose proof (RL.auxv_off_bound Ubsan.M.phdrs sp0 rnd av ev Amb.a_uid Amb.a_hwcap) as AB. fold bsb in AB. unfold RL.auxv_off in AB.
    assert (AB' : 8 + 8 * (Z.of_nat (length av) + 1) + 8 * (Z.of_nat (length ev) + 1) + 160 <= LB) by (unfold LB; lia). clear AB.
    pose proof bsb_len_bound.
    apply rw_cells_of_bytes; [cbn; repeat split; exact I| | apply entry_above_wr; cbn; lia].
    cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (AE.read_argv_ptr_w usegs Ubsan.M.phdrs sp0 av ev Amb.a_uid Amb.a_hwcap rnd VA VE usp_lo usp_hi k Hk) as R.
    unfold AE.wmem in R. rewrite StepTac.word_add_nat in R. fold bsb in R.
    rewrite F.rdn_wrap_stack_above in R by (rewrite unsigned_lit by lia; lia). fold SIMG in R.
    rewrite F.n_to_le_8_spec in R. change (word_to_le_bytes 8) with le8 in R.
    pose proof (entry_above_bytes (Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (8 + 8 * k))) (le8 (CE.cat_argv_ptr sp0 av ev k))) as B.
    rewrite unsigned_lit in B by lia. cbn [length le8 word_to_le_bytes Z_to_le_bytes] in B.
    replace (bv_unsigned sp0 + 8 + 8 * Z.of_nat k) with (bv_unsigned sp0 + Z.of_nat (8 + 8 * k)) by lia.
    apply B; [lia| lia| exact R].
  Qed.

  (* [comment removed for export] *)
  Lemma bsb_len_eq : LB = Z.of_nat (CE.cat_struct_size av ev) + Z.of_nat (F.total_arg_bytes_nat av) + Z.of_nat (F.total_arg_bytes_nat ev)
                          + ((8 - (Z.of_nat (CE.cat_struct_size av ev + F.total_arg_bytes_nat av + F.total_arg_bytes_nat ev)) mod 8) mod 8) + 16.
  Proof.
    unfold LB, bsb. set (ph := Ubsan.M.phdrs). clearbody ph. unfold build_stack_bytes. cbv zeta.
    rewrite (F.string_addrs_pair av). cbv beta iota. rewrite (F.string_addrs_pair ev). cbv beta iota.
    unfold at_random_bytes.
    set (AUX := auxv_bytes ph _ _ _). pose proof (length_auxv_bytes ph (at_random_ptr sp0 av ev) Amb.a_uid Amb.a_hwcap) as LA. fold AUX in LA. clearbody AUX.
    unfold auxv_size in LA.
    rewrite !length_app, !repeat_length, !F.length_flat_map_le8, !F.length_string_addrs_fst, !F.length_n_to_le_8, !LA, !F.length_flatten_strings.
    unfold CE.cat_struct_size, auxv_size.
    set (T := F.total_arg_bytes_nat av). set (U := F.total_arg_bytes_nat ev). clearbody T U.
    replace (8 + (length av + 1) * 8 + (length ev + 1) * 8 + 160 + T + U)%nat
      with (8 + (8 * length av + (8 + (8 * length ev + (8 + (160 + (T + U)))))))%nat by lia.
    replace (Z.of_nat (8 + (length av + 1) * 8 + (length ev + 1) * 8 + 160) + Z.of_nat T + Z.of_nat U)
      with (Z.of_nat (8 + (8 * length av + (8 + (8 * length ev + (8 + (160 + (T + U)))))))) by lia.
    set (X := (8 + (8 * length av + (8 + (8 * length ev + (8 + (160 + (T + U)))))))%nat). clearbody X.
    pose proof (Z.mod_pos_bound (8 - Z.of_nat X mod 8) 8 ltac:(lia)).
    rewrite !Nat2Z.inj_add, Z2Nat.id by lia. cbn [length]. lia.   (* [comment removed for export] *)
  Qed.

  Lemma total_firstn_nth : forall (l : list (list byte)) k, (k < length l)%nat ->
    (F.total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1 <= F.total_arg_bytes_nat l)%nat.
  Proof.
    induction l as [|x l IH]; intros k Hk; [cbn in Hk; lia|].
    destruct k as [|k]; cbn [firstn nth]; rewrite ?CE.total_arg_bytes_cons; [cbn; lia|].
    cbn [length] in Hk. specialize (IH k ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma entry_argv_str : forall k, (k < length av)%nat ->
    exists slack : list byte,
      bytes_at usegs mem (bv_unsigned (CE.cat_argv_ptr sp0 av ev k)) (nth k av [] ++ Z_to_bv 8 0 :: slack)
      /\ (- (bv_unsigned (CE.cat_argv_ptr sp0 av ev k) + Z.of_nat (length (nth k av [])) + 1)) mod 8 <= Z.of_nat (length slack)
      /\ bv_unsigned sp0 <= bv_unsigned (CE.cat_argv_ptr sp0 av ev k)
      /\ bv_unsigned (CE.cat_argv_ptr sp0 av ev k) + Z.of_nat (length (nth k av [])) + 1 + Z.of_nat (length slack) <= bv_unsigned sp0 + LB
      /\ ~ In (Z_to_bv 8 0) (nth k av [])
      /\ Z.of_nat (length (nth k av [])) <= 131071.
  Proof.
    intros k Hk. pose proof usp_lo as LO. pose proof usp_hi as HI. pose proof bsb_len_bound as BL.
    set (P := bv_unsigned (CE.cat_argv_ptr sp0 av ev k)). set (str := nth k av []).
    pose proof (RL.u_cat_argv_ptr Ubsan.M.phdrs sp0 rnd av ev Amb.a_uid Amb.a_hwcap VA VE usp_lo usp_hi k Hk) as HP. fold P in HP.
    pose proof (total_firstn_nth av k Hk) as TF. fold str in TF.
    pose proof bsb_len_eq as LE.
    assert (ROOM : P + Z.of_nat (length str) + 1 + 16 <= bv_unsigned sp0 + LB).
    { rewrite LE, HP. pose proof (Z.mod_pos_bound (8 - Z.of_nat (CE.cat_struct_size av ev + F.total_arg_bytes_nat av + F.total_arg_bytes_nat ev) mod 8) 8 ltac:(lia)). lia. }
    clear LE TF.
    set (x := P + Z.of_nat (length str) + 1). set (pad := (- x) mod 8).
    pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as PB. fold pad in PB.
    pose proof img_len_ge as IL. pose proof img_top2 as IT.
    exists (firstn (Z.to_nat pad) (skipn (Z.to_nat (x - bv_unsigned sp0)) SIMG)).
    assert (LS : length (firstn (Z.to_nat pad) (skipn (Z.to_nat (x - bv_unsigned sp0)) SIMG)) = Z.to_nat pad).
    { rewrite length_firstn, length_skipn. unfold LB in *. lia. }
    rewrite LS.
    split; [| split; [lia| split; [lia| split; [lia| split; [apply CE.valid_argv_str_nz; assumption| apply CE.valid_argv_str_len; assumption]]]]].
    replace (str ++ Z_to_bv 8 0 :: firstn (Z.to_nat pad) (skipn (Z.to_nat (x - bv_unsigned sp0)) SIMG))
      with ((str ++ [Z_to_bv 8 0]) ++ firstn (Z.to_nat pad) (skipn (Z.to_nat (x - bv_unsigned sp0)) SIMG)) by (rewrite <- app_assoc; reflexivity).
    apply (proj2 (bytes_at_app _ _ _ _ _)). split.
    - apply entry_above_bytes; [lia| rewrite length_app; cbn [length]; lia|].
      rewrite length_app. cbn [length]. fold str.
      apply (FS.read_argv_cstr_k Ubsan.M.phdrs usegs sp0 av ev k Amb.a_uid Amb.a_hwcap rnd Hk).
      fold bsb. unfold LB in BL. lia.
    - rewrite length_app. cbn [length]. fold str.
      pose proof (entry_above_bytes (Z_to_bv 64 x) (firstn (Z.to_nat pad) (skipn (Z.to_nat (x - bv_unsigned sp0)) SIMG))) as B.
      rewrite unsigned_lit in B by lia. rewrite LS in B.
      replace (P + Z.of_nat (length str + 1)) with x by lia. apply B; [lia| lia|].
      rewrite F.rdn_stack; rewrite ?unsigned_lit by lia; [reflexivity| lia| unfold LB in *; lia| unfold LB in *; lia].
  Qed.

  Lemma flat_map_le8_u64s : forall l, flat_map word_le8 l = u64s l.
  Proof. induction l as [|w l IH]; [reflexivity|]. cbn [flat_map u64s]. rewrite IH, F.n_to_le_8_spec. reflexivity. Qed.



  (* [comment removed for export] *)
  Lemma entry_dstat : DSTAT false tid mem.
  Proof.
    unfold DSTAT, ATEX, atex_cells, PDSO, PINCB, PATEX, PCXAFIN, wz. cbn [app].
    img_chunk 0x54c30 [C4 (Z_to_bv 64 0)] H2.
    img_chunk 0x23638 [C8 (Z_to_bv 64 0x23540); C8 (Z_to_bv 64 0x23538)] H3.
    img_chunk 0x23538 [C8 (Z_to_bv 64 0x130dc)] H4.
    img_chunk 0x248b8 [C1 (Z_to_bv 8 0)] H5.
    img_chunk 0x235e0 [C8 (Z_to_bv 64 0x15fdc); C8 (Z_to_bv 64 0)] H6.
    img_chunk 0x55088 [C8 (Z_to_bv 64 0)] H7.
    img_chunk 0x55078 [C8 (Z_to_bv 64 0)] H8.
    img_chunk 0x24860 [C8 (Z_to_bv 64 0x24778)] H9.
    img_chunk 0x24770 [C8 (Z_to_bv 64 0x24688)] H10.
    img_chunk 0x235f0 [C8 (Z_to_bv 64 0x235a0)] H11.
    img_chunk 0x235a0 [C8 (Z_to_bv 64 0x24688)] H12.
    img_chunk 0x235f8 [C8 (Z_to_bv 64 0)] H13.
    img_chunk 0x24648 [C8 (Z_to_bv 64 0x24648)] H14.
    img_chunk 0x348c4 [C1 (Z_to_bv 8 0)] H15.
    img_chunk 0x54a10 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
               C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] H16.
    img_chunk 0x54b30 [C8 (Z_to_bv 64 0)] H17.
    pose proof entry_rtd as H1.
    repeat (split; [assumption|]). exact H17.
  Qed.

  Lemma entry_cjst : CJST mem.
  Proof.
    unfold CJST, wz, PHOOKS, PGERROR, PLCONV, PMALLOC, PFREE, PREALLOC, PDOTSTR.
    img_chunk 0x24670 [C8 (Z_to_bv 64 0x16464); C8 (Z_to_bv 64 0x16324); C8 (Z_to_bv 64 0x17cd0)] H1.
    img_chunk 0x348f0 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] H2.
    img_chunk 0x23540 [C8 (Z_to_bv 64 0x102de)] H3.
    split; [exact H1|]. split; [exists (Z_to_bv 64 0), (Z_to_bv 64 0); exact H2| exact H3].
  Qed.

  Lemma entry_stdout : stdout_file mem stdout_init.
  Proof. apply stdout_file_init; intros a Ha; apply entry_none; lia. Qed.

  Lemma entry_stderr : stderr_wfile0 mem.
  Proof. apply stderr_wfile0_init; intros a Ha; apply entry_none; lia. Qed.

  Lemma entry_initflag : rw_cells usegs mem PINITFLAG [C1 (Z_to_bv 8 0)].
  Proof. unfold PINITFLAG. img_chunk 0x348c0 [C1 (Z_to_bv 8 0)] H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma entry_rs : rw_cells usegs mem PRS [CB RSN (repeat (Z_to_bv 8 0) RSN)].
  Proof.
    rewrite <- (repeat_length (Z_to_bv 8 0) RSN) at 1.
    apply (rw_cells_image0 usegs mem PRS (repeat (Z_to_bv 8 0) RSN)).
    - intros a Ha. rewrite repeat_length in Ha. apply (entry_none_b PRS RSN); [vm_compute; reflexivity| exact Ha].
    - vm_cast_no_check (@eq_refl bool true).   (* [comment removed for export] *)
    - unfold PRS. lia.
    - rewrite repeat_length, RSN_Z. unfold PRS. lia.
  Qed.

  Lemma entry_ssp : ssp_cells mem (SSP.canary_w (ed_random rnd)).
  Proof. split; [exact entry_got_ssp| exact entry_guard]. Qed.
  (* [comment removed for export] *)
  Lemma entry_rauxv : rauxv_ok mem (bv_unsigned sp0).
  Proof.
    pose proof usp_lo as LO. pose proof usp_hi as HI. pose proof bsb_len_bound as BL. pose proof (PF.len_av av VA) as LA.
    destruct VE as [LE _].
    (nelim (RL.rnd_facts usegs Ubsan.M.phdrs sp0 rnd av ev Amb.a_uid Amb.a_hwcap VA (conj LE (proj2 VE)) usp_lo usp_hi usp_al) 5%nat; intros R1 R2 R3 R4 R5).
    fold bsb in R2, R3.
    set (rptr := bv_unsigned (at_random_ptr sp0 av ev)) in *.
    exists (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)),
           65600, 56, 10, (bv_unsigned Amb.a_hwcap), 4096, (bv_unsigned Amb.a_uid), (bv_unsigned Amb.a_uid), 0, rptr.
    pose proof (bv_unsigned_in_range 64 Amb.a_uid) as UR. unfold bv_modulus in UR.
    pose proof (bv_unsigned_in_range 64 Amb.a_hwcap) as HWR. unfold bv_modulus in HWR.
    split; [| split; [| split; [| unfold LB in *; cbn in UR, HWR; lia]]].
    - (* [comment removed for export] *)
      pose proof (proj1 (proj1 (rw_cells_app usegs mem 0x54c60 [C8 (PD.auxv_w sp0 av ev)] _) entry_libc2)) as C.
      unfold RAUXV_CELL, MallocRep.wz, CJ_iface.wz. unfold PD.auxv_w in C. exact C.
    - (* [comment removed for export] *)
      pose proof (RL.read_auxv_all usegs Ubsan.M.phdrs sp0 rnd av ev Amb.a_uid Amb.a_hwcap VA (conj LE (proj2 VE)) usp_hi) as R.
      rewrite RL.auxv_bytes_words, RL.auxv_words_eq, flat_map_le8_u64s in R. fold bsb in R.
      rewrite StepTac.word_add_nat in R. unfold RL.auxv_off in R.
      pose proof (entry_above_bytes (Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (8 + 8 * (length av + 1) + 8 * (length ev + 1))))) as B.
      rewrite unsigned_lit in B by lia.
      replace (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))
        with (bv_unsigned sp0 + Z.of_nat (8 + 8 * (length av + 1) + 8 * (length ev + 1))) by lia.
      pose proof (RL.auxv_off_bound Ubsan.M.phdrs sp0 rnd av ev Amb.a_uid Amb.a_hwcap) as AB. fold bsb in AB. unfold RL.auxv_off in AB.
      apply B; [lia| cbn; unfold LB in *; lia|].
      etransitivity; [exact R|]. unfold auxv_list, MallocRep.wz, CJ_iface.wz, AT_PHDR, AT_PHENT, AT_PHNUM, AT_HWCAP, AT_PAGESZ, AT_UID, AT_EUID, AT_SECURE, AT_RANDOM, AT_NULL.
      cbn [map]. subst rptr. rewrite !Z_to_bv_bv_unsigned.
      replace (Z.of_N (ph_addr Ubsan.M.phdrs)) with 65600 by (vm_compute; reflexivity).
      replace (Z.of_N (ph_ent Ubsan.M.phdrs)) with 56 by (vm_compute; reflexivity).
      replace (Z.of_N (ph_num Ubsan.M.phdrs)) with 10 by (vm_compute; reflexivity).
      reflexivity.
    - (* [comment removed for export] *)
      rewrite HSEC, rnd_secret_le8.
      pose proof (entry_above_bytes (Z_to_bv 64 (rptr + 8)) (firstn 8 (skipn 8 (at_random_bytes (ed_random rnd))))) as B.
      rewrite length_firstn, length_skipn, length_at_random_bytes in B. cbn [Nat.sub Nat.min] in B.
      rewrite unsigned_lit in B by (unfold LB in *; lia). apply B; [lia| cbn; unfold LB in *; lia|].
      replace (rptr + 8) with (rptr + Z.of_nat 8) by lia. apply (R5 8%nat 8%nat). lia.
  Qed.
End Entry.


End CeilWrap.
