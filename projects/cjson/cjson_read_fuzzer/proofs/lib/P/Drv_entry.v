(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the entry section takes the whole ProcInput, the mmap base, brk, valid_launch and the launch placement in place of an argv/envp pair and the ambient uid and hwcap; the stack image is StackLayout's block ending at the stack top, so the image-length, argv-pointer, argv-string and auxv lemmas are restated over it with the new stack window and the launch auxv and the old bsb length lemmas go; comments record why the layout lemmas need brk, the address width, the program headers and the entry given explicitly. *)
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartup PStartupDefs PStartupFacts Amb MmapSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import InitMem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import Malloc_ifaceP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import CJ_iface F_pad Exit F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Drv_base.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Module F := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec.
Module CE := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.WallSim.CatExec.
Module RL := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.RefLayout.
Module FS := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.FileSim.
Module AE := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.ArgvEnv.
Module PS := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartup.
Module PD := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.
Module PF := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupFacts.
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
  | S n' => match wview psegs (fun _ => None) (wa A) with Some _ => wr_b (A + 1) n' | None => false end
  end.

Lemma wr_b_sound : forall n A m, wr_b A n = true -> 0 <= A -> A + Z.of_nat n <= 2^64 -> wr_at psegs m A (Z.of_nat n).
Proof.
  induction n as [|n IH]; intros A m Hb HA Hn.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
  - cbn [wr_b] in Hb. destruct (wview psegs (fun _ => None) (wa A)) as [b|] eqn:E; [|discriminate].
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.eq_dec i 0) as [->|NE].
    + rewrite Z.add_0_r. apply wview_overlay_mono. rewrite E. discriminate.
    + replace (A + i) with ((A + 1) + (i - 1)) by lia. apply (IH (A + 1) m Hb); lia.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_of_bytes : forall m A cs,
  cells_wf cs -> bytes_at psegs m A (cells_bytes cs) -> wr_at psegs m A (Z.of_nat (cells_size cs)) -> rw_cells psegs m A cs.
Proof. intros m A cs Hwf HB HW. split; [split; [exact Hwf| exact HB]| exact HW]. Qed.

Lemma rw_cells_bytes : forall m A cs, rw_cells psegs m A cs -> bytes_at psegs m A (cells_bytes cs).
Proof. intros m A cs [[_ HB] _]. exact HB. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Entry.
  (* every lemma takes the whole section context, so DrvTop calls them uniformly *)
  Set Default Proof Using "All".
  Variable sp0 : word.
  Variable inp : ProcInput.
  Variables mbase brk : word.
  Variable tid : word.
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation RENT := (Z_to_bv 64 (Z.of_N Plain.M.init_pc)) (only parsing).
  Hypothesis ME : PS.p_main_entry sp0 inp mbase rnd tid regs mem.
  Hypothesis VA : valid_argv av.
  Hypothesis VE : valid_envp ev.
  Hypothesis VSP : valid_sp sp0.
  Hypothesis VL : valid_launch inp.
  Hypothesis LAU : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rnd) inp.
  Hypothesis HCEIL : alloc_ceiling <= bv_unsigned sp0 - 8388608.   (* [comment removed for export] *)
  Hypothesis HSEC : malloc_secret_val = rnd_secret (ed_random rnd).   (* [comment removed for export] *)

  Lemma usp_lo : 0x7fff80000000 <= bv_unsigned sp0.
  Proof. (nelimp VSP 3%nat; intros H _ _). unfold sp_window_lo in H. exact H. Qed.
  Lemma usp_hi : bv_unsigned sp0 <= 0x800000000000.
  Proof. (nelimp VSP 3%nat; intros _ H _). unfold sp_window_hi in H. exact H. Qed.
  Lemma usp_al : bv_unsigned sp0 mod 16 = 0.
  Proof. (nelimp VSP 3%nat; intros _ _ H). exact H. Qed.

  Ltac lctx := first [ exact VA | exact VE | exact VL | exact LAU | exact usp_lo | exact usp_hi | exact usp_al ].

  (* the entry image: StackLayout's block, ending at the stack VMA's top (ed_top) *)
  Definition SIMG : list byte := entry_stack_image inp mbase Plain.M.phdrs RENT sp0 rnd.
  Definition LB : Z := Z.of_nat (length SIMG).

  Lemma lb_top : bv_unsigned sp0 + LB = bv_unsigned (ed_top rnd).
  Proof. unfold LB, SIMG. rewrite (F.length_entry_stack_image_launch Sv48 inp mbase Plain.M.phdrs RENT sp0 brk rnd LAU). lia. Qed.

  Lemma top_facts : bv_unsigned (ed_top rnd) <= 0x800000000000 /\ bv_unsigned (ed_top rnd) mod 8 = 0.
  Proof.
    destruct LAU as ((T1 & T2 & _) & _). cbn [va_stack_top] in T2. unfold sp_window_hi, page_size in *.
    split; [lia|]. rewrite <- (Z.mod_mod (bv_unsigned (ed_top rnd)) 8) by lia.
    replace (bv_unsigned (ed_top rnd)) with (4096 * (bv_unsigned (ed_top rnd) / 4096) + bv_unsigned (ed_top rnd) mod 4096)
      by (symmetry; apply Z.div_mod; lia).
    rewrite T1, Z.add_0_r. replace (4096 * (bv_unsigned (ed_top rnd) / 4096)) with ((512 * (bv_unsigned (ed_top rnd) / 4096)) * 8) by lia.
    rewrite Z_mod_mult. reflexivity.
  Qed.

  Lemma img_top : bv_unsigned sp0 + Z.of_nat (length SIMG) <= 0x800000000000.
  Proof. pose proof lb_top. pose proof top_facts. unfold LB in *. lia. Qed.

  (* [comment removed for export] *)
  Lemma entry_mem_data : forall a : word, bv_unsigned a < 0x55000 -> mem a = PD.D_main sp0 inp rnd tid a.
  Proof.
    intros a Ha. apply (PS.main_entry_mem_data sp0 inp mbase rnd tid regs mem ME).
    rewrite CE.stack_max_size_val. pose proof usp_lo. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_none_out : forall a : word,
    (bv_unsigned a < 0x23730 \/ 0x53b88 <= bv_unsigned a) -> bv_unsigned a < 2^64 - 8 -> PD.D_main sp0 inp rnd tid a = None.
  Proof.
    intros a Ha Hb.
    unfold PD.D_main, PD.D_fd, PD.D_ssp, PD.D_tls, PD.D_tlsB, PD.D_tlsA, PD.D_libc.
    repeat (rewrite MSP.wbytes_outside by
      (rewrite ?CE.length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite unsigned_lit by lia; lia)).
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma entry_mem_inv : mem_inv psegs mem.
  Proof.
    apply mem_inv_intro. intros a b Hab.
    destruct (Z.ltb_spec0 (bv_unsigned a) 0x55000) as [Hlt|Hge].
    - rewrite entry_mem_data in Hab by exact Hlt.
      destruct (Z.leb_spec0 0x23730 (bv_unsigned a)) as [H1|H1];
      [destruct (Z.ltb_spec0 (bv_unsigned a) 0x53b88) as [H2|H2]|].
      + assert (FS3 : find_segment psegs (bv_unsigned a) 1 = Some Plain.Plain_segment_003).
        { unfold psegs, Plain.M.loaded_segments, Plain.Plain_loaded_segments. cbn [find_segment].
          replace (Z.of_N (seg_base Plain.Plain_segment_000)) with 65536%Z by (vm_compute; reflexivity).
          replace (Z.of_N (seg_size Plain.Plain_segment_000)) with 8192%Z by (vm_compute; reflexivity).
          replace (Z.of_N (seg_base Plain.Plain_segment_001)) with 73728%Z by (vm_compute; reflexivity).
          replace (Z.of_N (seg_size Plain.Plain_segment_001)) with 65536%Z by (vm_compute; reflexivity).
          replace (Z.of_N (seg_base Plain.Plain_segment_002)) with 139264%Z by (vm_compute; reflexivity).
          replace (Z.of_N (seg_size Plain.Plain_segment_002)) with 4096%Z by (vm_compute; reflexivity).
          replace (Z.of_N (seg_base Plain.Plain_segment_003)) with 143360%Z by (vm_compute; reflexivity).
          replace (Z.of_N (seg_size Plain.Plain_segment_003)) with 204800%Z by (vm_compute; reflexivity).
          destruct (Z.leb_spec0 65536 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) (65536 + 8192)); cbn [andb]; try lia.
          all: destruct (Z.leb_spec0 73728 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) (73728 + 65536)); cbn [andb]; try lia.
          all: destruct (Z.leb_spec0 139264 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) (139264 + 4096)); cbn [andb]; try lia.
          all: destruct (Z.leb_spec0 143360 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) (143360 + 204800)); cbn [andb]; try lia.
          reflexivity. }
        split; [| left; rewrite FS3; discriminate].
        unfold ro_addr. rewrite FS3. vm_compute. reflexivity.
      + rewrite D_main_none_out in Hab by lia. discriminate.
      + rewrite D_main_none_out in Hab by lia. discriminate.
    - split; [apply ref_ro_addr_false; lia| right].
      pose proof usp_hi as HI. unfold TASK_SIZE.
      destruct (Z.leb_spec0 (bv_unsigned sp0) (bv_unsigned a)) as [Ha|Ha]; [| lia].
      rewrite (PS.main_entry_mem_above sp0 inp mbase rnd tid regs mem ME) in Hab by lia.
      unfold F.wrap_mem in Hab. fold SIMG in Hab. unfold stack_to_mem in Hab.
      rewrite (proj2 (Z.leb_le _ _)) in Hab by lia.
      destruct (Z.ltb_spec0 (bv_unsigned a) (bv_unsigned sp0 + Z.of_nat (length SIMG))) as [Hb|Hb].
      + pose proof img_top. lia.   (* [comment removed for export] *)
      + rewrite (proj2 (Z.ltb_ge _ _)) in Hab by lia. cbn in Hab.
        rewrite (proj2 (Z.ltb_ge (bv_unsigned a) (bv_unsigned sp0))) in Hab by lia. rewrite andb_false_r in Hab. discriminate.
  Qed.


  (* [comment removed for export] *)
  Lemma entry_none : forall a : word,
    (bv_unsigned a < 0x23730 \/ 0x53b88 <= bv_unsigned a < 0x55000) -> mem a = None.
  Proof.
    intros a Ha. rewrite entry_mem_data by lia. apply D_main_none_out; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma entry_stk : stk psegs mem (bv_unsigned sp0 - 6144512) (bv_unsigned sp0 - 48).
  Proof.
    pose proof usp_lo. pose proof usp_hi.
    split; [lia|]. split; [lia|]. intros a Ha.
    assert (NN : mem (wa a) <> None).
    { apply (PS.main_entry_win_mapped sp0 inp mbase rnd tid regs mem ME). unfold MSP.wok_lo, OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.StoreOk.stack_window_reach. rewrite CE.stack_max_size_val. rewrite wa_unsigned by lia. lia. }
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
    intros; rewrite (PS.main_entry_rdn_data sp0 inp mbase rnd tid regs mem ME) by (rewrite CE.stack_max_size_val; ST.unorm; pose proof usp_lo; lia).

  Lemma rd_self : forall segs, F.rdn segs mem (Z_to_bv 64 0x337c8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x337c8)).
  Proof. to_mem. pose proof (F.u64_range tid). hit8. Qed.
  Lemma rd_next : forall segs, F.rdn segs mem (Z_to_bv 64 0x337d0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x337c8)).
  Proof. to_mem. pose proof (F.u64_range tid). hit8. Qed.
  Lemma rd_prev : forall segs, F.rdn segs mem (Z_to_bv 64 0x337d8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x337c8)).
  Proof. to_mem. pose proof (F.u64_range tid). hit8. Qed.
  Lemma rd_sysinfo : forall segs, F.rdn segs mem (Z_to_bv 64 0x337e0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Proof. to_mem. pose proof (F.u64_range tid). hit8. Qed.
  Lemma rd_tid : forall segs, F.rdn segs mem (Z_to_bv 64 0x337e8) 4 = Some (word_to_le_bytes 4 tid).
  Proof. intros segs. apply (PF.main_entry_tid sp0 inp mbase tid rnd usp_lo regs mem ME). Qed.
  Lemma rd_guard : forall segs, F.rdn segs mem (Z_to_bv 64 0x53af8) 8 = Some (SSP.guard_bytes (ed_random rnd)).
  Proof. intros segs. apply (PF.main_entry_guard sp0 inp mbase tid rnd usp_lo regs mem ME). Qed.
  Lemma rd_cdt : forall segs, F.rdn segs mem (Z_to_bv 64 0x53b18) 1 = Some [Z_to_bv 8 1].
  Proof.
    to_mem. pose proof (F.u64_range tid).
    unfold PD.D_main, PD.D_fd, PD.D_ssp, PD.D_tls, PD.D_tlsB, PD.D_tlsA, PD.D_libc; ST.peel.
    apply (SE.rdn_wbytes_hit segs [Z_to_bv 8 1]). ST.unorm; cbn; lia.
  Qed.
  Lemma rd_auxv : forall segs, F.rdn segs mem (Z_to_bv 64 0x53b20) 8 = Some (word_to_le_bytes 8 (PD.auxv_w sp0 inp)).
  Proof. to_mem. pose proof (F.u64_range tid). pose proof (PF.len_av inp VA). hit8. Qed.
  Lemma rd_tls_size : forall segs, F.rdn segs mem (Z_to_bv 64 0x53b30) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe0)).
  Proof. to_mem. pose proof (F.u64_range tid). pose proof (PF.len_av inp VA). hit8. Qed.
  Lemma rd_tls_align : forall segs, F.rdn segs mem (Z_to_bv 64 0x53b38) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 8)).
  Proof. to_mem. pose proof (F.u64_range tid). pose proof (PF.len_av inp VA). hit8. Qed.
  Lemma rd_pagesize : forall segs, F.rdn segs mem (Z_to_bv 64 0x53b48) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
  Proof. to_mem. apply (PF.D_main_pagesize sp0 inp tid rnd VA). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rd_bytes : forall (c : Z) bs,
    0 <= c -> c + Z.of_nat (length bs) <= 2^64 ->
    F.rdn psegs mem (Z_to_bv 64 c) (length bs) = Some bs -> bytes_at psegs mem c bs.
  Proof. intros c bs Hc Hb H. apply rdn_bytes_at; [lia| lia|]. unfold wa. rewrite <- rdn_flat. exact H. Qed.

  (* [comment removed for export] *)
  Lemma entry_img_chunk : forall (A : Z) (bs : list byte),
    PF.D_main_missb A (length bs) = true -> rw_bytes_b psegs A bs = true ->
    rw_cells psegs mem A [CB (length bs) bs].
  Proof.
    intros A bs Hm Hb.
    assert (HR : 0 <= A /\ A + Z.of_nat (length bs) <= 0x55000).
    { unfold PF.D_main_missb in Hm. apply andb_true_iff in Hm as [Hm H2]. apply andb_true_iff in Hm as [_ H1].
      apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
    apply rw_cells_image0; [| exact Hb| lia| lia].
    intros a Ha. apply (entry_none_b A (length bs) Hm a Ha).
  Qed.

  Local Ltac img_chunk A cs H :=
    let bs := eval vm_compute in (cells_bytes cs) in
    assert (H : rw_cells psegs mem A cs);
    [ apply (rw_cells_recast psegs mem A [CB (length bs) bs] cs);
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
  Lemma entry_rtd : rw_cells psegs mem 0x337c8 [C8 (Z_to_bv 64 0x337c8); C8 (Z_to_bv 64 0x337c8); C8 (Z_to_bv 64 0x337c8); C8 (Z_to_bv 64 0); C4 tid].
  Proof.
    apply rw_cells_of_bytes; [cbn; repeat split; exact I| | apply (wr_b_sound 36); [vm_compute; reflexivity| lia| cbn; lia]].
    cbn [cells_bytes cbytes]. bapp.
    - apply (rd_bytes 0x337c8 (le8 (Z_to_bv 64 0x337c8))); [lia| cbn; lia| apply rd_self].
    - apply (rd_bytes 0x337d0 (le8 (Z_to_bv 64 0x337c8))); [lia| cbn; lia| apply rd_next].
    - apply (rd_bytes 0x337d8 (le8 (Z_to_bv 64 0x337c8))); [lia| cbn; lia| apply rd_prev].
    - apply (rd_bytes 0x337e0 (le8 (Z_to_bv 64 0))); [lia| cbn; lia| apply rd_sysinfo].
    - apply (rd_bytes 0x337e8 (le4 tid)); [lia| cbn; lia| apply rd_tid].
  Qed.

  (* [comment removed for export] *)
  Lemma entry_libc : rw_cells psegs mem 0x53b18 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)].
  Proof.
    img_chunk 0x53b19 [CB 7 (repeat (Z_to_bv 8 0) 7)] IMG.
    apply rw_cells_of_bytes; [cbn; repeat split; exact I| | apply (wr_b_sound 8); [vm_compute; reflexivity| lia| cbn; lia]].
    change (bytes_at psegs mem 0x53b18 ([Z_to_bv 8 1] ++ repeat (Z_to_bv 8 0) 7)).
    apply (proj2 (bytes_at_app _ _ _ _ _)); split.
    - apply (rd_bytes 0x53b18 [Z_to_bv 8 1]); [lia| cbn; lia| apply rd_cdt].
    - exact (rw_cells_bytes _ _ _ IMG).
  Qed.

  (* [comment removed for export] *)
  Lemma entry_libc2 : rw_cells psegs mem 0x53b20 [C8 (PD.auxv_w sp0 inp); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                                               C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)].
  Proof.
    img_chunk 0x53b28 [CB 8 (repeat (Z_to_bv 8 0) 8)] I1.
    img_chunk 0x53b40 [CB 8 (repeat (Z_to_bv 8 0) 8)] I2.
    img_chunk 0x53b50 [CB 48 (repeat (Z_to_bv 8 0) 48)] I3.
    apply rw_cells_of_bytes; [cbn; repeat split; exact I| | apply (wr_b_sound 96); [vm_compute; reflexivity| lia| cbn; lia]].
    cbn [cells_bytes cbytes]. bapp.
    - apply (rd_bytes 0x53b20 (le8 _)); [lia| cbn; lia| apply rd_auxv].
    - exact (rw_cells_bytes _ _ _ I1).
    - apply (rd_bytes 0x53b30 (le8 _)); [lia| cbn; lia| apply rd_tls_size].
    - apply (rd_bytes 0x53b38 (le8 _)); [lia| cbn; lia| apply rd_tls_align].
    - exact (rw_cells_bytes _ _ _ I2).
    - apply (rd_bytes 0x53b48 (le8 _)); [lia| cbn; lia| apply rd_pagesize].
    - exact (rw_cells_bytes _ _ _ I3).
  Qed.

  (* [comment removed for export] *)
  Lemma guard_le8 : le8 (SSP.canary_w (ed_random rnd)) = SSP.guard_bytes (ed_random rnd).
  Proof.
    unfold le8, word_to_le_bytes. rewrite <- (SSP.canary_val (ed_random rnd)).
    rewrite <- (SSP.length_guard_bytes (ed_random rnd)) at 1. apply StrFun.Z_to_le_bytes_to_Z.
  Qed.
  Lemma entry_guard : rw_cells psegs mem 0x53af8 [C8 (SSP.canary_w (ed_random rnd))].
  Proof.
    apply rw_cells_of_bytes; [cbn; repeat split; exact I| | apply (wr_b_sound 8); [vm_compute; reflexivity| lia| cbn; lia]].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. apply (rd_bytes 0x53af8 (le8 _)); [lia| cbn; lia|].
    rewrite guard_le8. apply rd_guard.
  Qed.
  Lemma entry_got_ssp : rw_cells psegs mem 0x224e8 [C8 (Z_to_bv 64 0x53af8)].
  Proof. img_chunk 0x224e8 [C8 (Z_to_bv 64 0x53af8)] H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma entry_errno : rw_cells psegs mem 0x337ec [C4 (Z_to_bv 64 0)].
  Proof. img_chunk 0x337ec [C4 (Z_to_bv 64 0)] H. exact H. Qed.

  (* [comment removed for export] *)

  Lemma bsb_len_bound : 0 <= LB <= 2101782.
  Proof. split; [unfold LB; lia|]. unfold LB, SIMG. eapply RL.lay_bsb_len; lctx. Qed.

  Lemma entry_above_rdn : forall (a : word) n,
    bv_unsigned sp0 <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2^64 ->
    F.rdn psegs mem a n = F.rdn psegs (stack_to_mem sp0 SIMG) a n.
  Proof.
    intros a n H1 H2. rewrite (PS.main_entry_rdn_above sp0 inp mbase rnd tid regs mem ME) by assumption.
    unfold SIMG. apply F.rdn_wrap_stack_above; assumption.
  Qed.

  Lemma entry_above_some : forall a : word,
    bv_unsigned sp0 <= bv_unsigned a < bv_unsigned sp0 + LB -> exists b, mem a = Some b.
  Proof.
    intros a Ha. rewrite (PS.main_entry_mem_above sp0 inp mbase rnd tid regs mem ME) by lia.
    unfold F.wrap_mem. fold SIMG. unfold stack_to_mem.
    rewrite (proj2 (Z.leb_le _ _)) by lia. unfold LB in *. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
    destruct (nth_error SIMG (Z.to_nat (bv_unsigned a - bv_unsigned sp0))) as [b|] eqn:E; [exists b; reflexivity|].
    apply nth_error_None in E. lia.
  Qed.

  Lemma entry_above_wr : forall A n, bv_unsigned sp0 <= A -> A + n <= bv_unsigned sp0 + LB -> wr_at psegs mem A n.
  Proof.
    intros A n H1 H2. pose proof bsb_len_bound. pose proof usp_hi. pose proof usp_lo.
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (entry_above_some (wa (A + i))) as [b Hb]; [rewrite wa_unsigned by lia; lia|].
    eapply wview_some; exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma entry_above_bytes : forall (a : word) bs,
    bv_unsigned sp0 <= bv_unsigned a -> bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
    F.rdn psegs (stack_to_mem sp0 SIMG) a (length bs) = Some bs -> bytes_at psegs mem (bv_unsigned a) bs.
  Proof.
    intros a bs H1 H2 H. apply rd_bytes; [pose proof usp_lo; lia| exact H2|].
    rewrite Z_to_bv_bv_unsigned. rewrite entry_above_rdn by assumption. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma entry_argv_ptr : forall k, (k < length av)%nat ->
    rw_cells psegs mem (bv_unsigned sp0 + 8 + 8 * Z.of_nat k) [C8 (CE.cat_argv_ptr (ed_top rnd) av ev (in_execfn inp) k)].
  Proof.
    intros k Hk. pose proof usp_lo. pose proof usp_hi. pose proof (PF.len_av inp VA).
    assert (AB : (RL.auxv_off av ev + auxv_size (kb_rseq (in_kernel inp)) + 16 <= length SIMG)%nat)
      (* The DISCHARGED signature settles this:
           RL.auxv_off_bound : forall (inp : ProcInput) (mbase : word) (ph : PhdrInfo)
                                      (entry sp : word), word -> forall rdraw : EntryDraw, …
           Arguments RL.auxv_off_bound inp mbase ph (entry sp brk) rdraw
         SEVEN arguments, NO hypotheses -- so `lctx` has nothing to discharge.  The
         sixth, `brk`, is ANONYMOUS IN THE TYPE (a bare `word ->`, named only by Arguments)
         and occurs nowhere in the conclusion, so eapply cannot determine it and `first
         [exact …|…]` cannot close a goal carrying `?brk`.  That is the whole defect.
         So: supply brk positionally, underscore the rest -- unification fixes inp, mbase,
         ph, entry, sp and rdraw from SIMG's own `entry_stack_image inp mbase ph entry sp rnd`,
         and no side goal remains.  brk is this Section's Variable at :144.
         "Undetermined Section Variable" and "anonymous in its type" are the same fact from
         two sides, and the Arguments line is what shows it: brk is a Section Variable that
         the discharged type leaves unnamed. *)
      by (unfold SIMG; apply (RL.auxv_off_bound _ _ _ _ _ brk _)).
    unfold RL.auxv_off in AB.
    assert (AB' : 8 + 8 * (Z.of_nat (length av) + 1) + 8 * (Z.of_nat (length ev) + 1) <= LB) by (unfold LB; lia). clear AB.
    pose proof bsb_len_bound.
    apply rw_cells_of_bytes; [cbn; repeat split; exact I| | apply entry_above_wr; cbn; lia].
    cbn [cells_bytes cbytes]. rewrite app_nil_r.
    (* `Locate rdn` in THIS scope settles it:
         Constant …lib.Lib.PropExec.rdn            <- what bare `rdn` resolves to HERE
         Constant …lib.P.Drv_entry.F.rdn  (syntactically equal to …lib.PropExec.rdn)
       TWO DIFFERENT CONSTANTS named `rdn`, in lib/Lib/PropExec.v and lib/PropExec.v.
       `Module F := …lib.PropExec` (:40), so F.rdn is the SECOND; the Lib.StoreCache and
       Lib.NElim imports at :35 and :57 bring the FIRST into scope and it wins the bare name.
       So the assert below names F.rdn: :494 rewrites with F.rdn_wrap_stack_above, whose LHS
       is F.rdn, and `rewrite` matches SYNTACTICALLY, so an assert over the bare rdn leaves no
       subterm to find even though every argument is right and the two constants are
       convertible (which is exactly why the `eapply` on the next line succeeds and hides it).
       The cause is two files of the same name in ONE unit, each defining the same
       identifier. *)
    assert (R : F.rdn psegs (F.wrap_mem inp mbase Plain.M.phdrs RENT sp0 rnd) (sp0 + nat_to_word (8 + 8 * k)) 8%nat
                = Some (word_le8 (CE.cat_argv_ptr (ed_top rnd) av ev (in_execfn inp) k)))
      by (eapply AE.read_argv_ptr_w; first [lctx | exact Hk]).
    rewrite StepTac.word_add_nat in R.
    rewrite F.rdn_wrap_stack_above in R by (rewrite unsigned_lit by lia; lia). fold SIMG in R.
    rewrite F.n_to_le_8_spec in R. change (word_to_le_bytes 8) with le8 in R.
    pose proof (entry_above_bytes (Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (8 + 8 * k))) (le8 (CE.cat_argv_ptr (ed_top rnd) av ev (in_execfn inp) k))) as B.
    rewrite unsigned_lit in B by lia. cbn [length le8 word_to_le_bytes Z_to_le_bytes] in B.
    replace (bv_unsigned sp0 + 8 + 8 * Z.of_nat k) with (bv_unsigned sp0 + Z.of_nat (8 + 8 * k)) by lia.
    apply B; [lia| lia| exact R].
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
      bytes_at psegs mem (bv_unsigned (CE.cat_argv_ptr (ed_top rnd) av ev (in_execfn inp) k)) (nth k av [] ++ Z_to_bv 8 0 :: slack)
      /\ (- (bv_unsigned (CE.cat_argv_ptr (ed_top rnd) av ev (in_execfn inp) k) + Z.of_nat (length (nth k av [])) + 1)) mod 8 <= Z.of_nat (length slack)
      /\ bv_unsigned sp0 <= bv_unsigned (CE.cat_argv_ptr (ed_top rnd) av ev (in_execfn inp) k)
      /\ bv_unsigned (CE.cat_argv_ptr (ed_top rnd) av ev (in_execfn inp) k) + Z.of_nat (length (nth k av [])) + 1 + Z.of_nat (length slack) <= bv_unsigned sp0 + LB
      /\ ~ In (Z_to_bv 8 0) (nth k av [])
      /\ Z.of_nat (length (nth k av [])) <= 131071.
  Proof.
    intros k Hk. pose proof usp_lo as LO. pose proof usp_hi as HI. pose proof bsb_len_bound as BL.
    set (P := bv_unsigned (CE.cat_argv_ptr (ed_top rnd) av ev (in_execfn inp) k)). set (str := nth k av []).
    assert (HP : P = bv_unsigned sp0 + Z.of_nat (CE.cat_string_off (kb_rseq (in_kernel inp)) sp0 (ed_top rnd) av ev (in_execfn inp)
                                                  + F.total_arg_bytes_nat (firstn k av)))
      (* same Section, same defect as :470's auxv_off_bound.
         RL.u_cat_argv_ptr and RL.struct_av_bound are declared in the SAME Section Layout of
         PStartupDefs.v as auxv_off_bound, whose DISCHARGED signature is
         `Arguments … inp mbase ph (entry sp brk) rdraw` — seven arguments with the
         sixth, brk, ANONYMOUS IN THE TYPE and absent from the conclusion.  Section discharge
         gives every lemma in a Section the same leading binders, so eapply leaves ?brk here too
         and `first [lctx | exact Hk]` cannot close a goal carrying a metavariable.
         Supplied BY NAME rather than positionally: `with (brk := brk)` uses the name the
         Arguments line declares, so it is robust to the discharge COUNT differing per lemma —
         Section discharge keeps only the variables a lemma actually uses, so one lemma's
         count says nothing of another's. *)
      (* THE PRINTED SIGNATURE, not one inferred from the Section-mate auxv_off_bound.
         Inferring this lemma's discharge from auxv_off_bound's gives brk alone, which is not
         enough: the two signatures differ in every respect that matters —
           auxv_off_bound    7 arguments, ZERO hypotheses
           u_cat_argv_ptr   11 arguments, FOUR hypotheses, and a LEADING `v : VaSize`
             Arguments RL.u_cat_argv_ptr v inp mbase ph (entry sp brk) rdraw
                                         Hvl Hlau Hsp_lo Hsp_hi k _
         Section discharge keeps only the variables a lemma USES, and this one's proof goes
         through `cat_string_base_offset v inp mbase sp brk rdraw Hlau`, which drags in v,
         Hlau and then the sp_window pair.  `brk` alone is accepted and is not the obstacle:
         `v` occurs ONLY inside Hlau's `entry_launch_ok_va v …` and nowhere in the
         conclusion, so eapply cannot determine it and `first [lctx | exact Hk]` cannot
         close a goal still carrying `?v`.  Supplied by name beside brk.
         Sv48 is the width LAU is stated at in this Section
         (:158, `entry_launch_ok_va Sv48 …`). *)
      (* FINAL, read off the two printed signatures together rather than inferred.
         The full type:
           ∀ (v : VaSize) (inp : ProcInput) (mbase : word), PhdrInfo → word →
             ∀ (sp brk : word) (rdraw : EntryDraw), valid_launch inp →
             entry_launch_ok_va v {| en_sp := sp; en_brk := brk; en_mmap_base := mbase;
                                     en_draw := rdraw |} inp → … → <conclusion>
         The conclusion mentions inp, sp, rdraw and k, and NOTHING else; Hlau mentions v,
         mbase and brk.  So `ph` (4th) and the anonymous `word` the Arguments line names
         `entry` (5th) occur in NO premise and NO conclusion and can never be determined by
         unification.  Measured: of the seven goals
         `eapply … with (v := Sv48) (brk := brk)` leaves, `first [lctx | exact Hk]` closes
         five and leaves `PhdrInfo` and `word` OPEN — which is the "No applicable tactic".
         Supplying brk and v is necessary and not sufficient.  ph and entry are given the
         Section's own values, the pair SIMG is built from at :171, so the instance is the
         image this file reasons about and not an arbitrary witness. *)
      by (subst P; eapply RL.u_cat_argv_ptr with (v := Sv48) (brk := brk)
                     (ph := Plain.M.phdrs) (entry := RENT); first [lctx | exact Hk]).
    assert (SB : (CE.cat_string_off (kb_rseq (in_kernel inp)) sp0 (ed_top rnd) av ev (in_execfn inp)
                  + F.total_arg_bytes_nat av + F.total_arg_bytes_nat ev <= length SIMG)%nat)
      by (unfold SIMG; eapply RL.struct_av_bound with (brk := brk); lctx).
    pose proof (total_firstn_nth av k Hk) as TF. fold str in TF.
    (* the strings end at ed_top, a page boundary: the padding to the next 8 bytes stays inside *)
    pose proof lb_top as LT. pose proof top_facts as (TT & T8).
    set (x := P + Z.of_nat (length str) + 1). set (pad := (- x) mod 8).
    assert (ROOM : x <= bv_unsigned sp0 + LB) by (subst x; unfold LB; lia).
    pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as PB. fold pad in PB.
    pose proof (Z.div_mod (- x) 8 ltac:(lia)) as DX. fold pad in DX.
    pose proof (Z.div_mod (bv_unsigned (ed_top rnd)) 8 ltac:(lia)) as DT. rewrite T8, Z.add_0_r in DT.
    assert (ROOM2 : x + pad <= bv_unsigned sp0 + LB) by lia.
    clear TF SB.
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
      unfold SIMG. eapply FS.read_argv_cstr_k; [exact LAU| exact Hk].
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
    img_chunk 0x53af0 [C4 (Z_to_bv 64 0)] H2.
    img_chunk 0x224f0 [C8 (Z_to_bv 64 0x223f8); C8 (Z_to_bv 64 0x223f0)] H3.
    img_chunk 0x223f0 [C8 (Z_to_bv 64 0x120bc)] H4.
    img_chunk 0x23778 [C1 (Z_to_bv 8 0)] H5.
    img_chunk 0x22498 [C8 (Z_to_bv 64 0x14e98); C8 (Z_to_bv 64 0)] H6.
    img_chunk 0x53f48 [C8 (Z_to_bv 64 0)] H7.
    img_chunk 0x53f38 [C8 (Z_to_bv 64 0)] H8.
    img_chunk 0x23718 [C8 (Z_to_bv 64 0x23630)] H9.
    img_chunk 0x23628 [C8 (Z_to_bv 64 0x23540)] H10.
    img_chunk 0x224a8 [C8 (Z_to_bv 64 0x22458)] H11.
    img_chunk 0x22458 [C8 (Z_to_bv 64 0x23540)] H12.
    img_chunk 0x224b0 [C8 (Z_to_bv 64 0)] H13.
    img_chunk 0x23500 [C8 (Z_to_bv 64 0x23500)] H14.
    img_chunk 0x33784 [C1 (Z_to_bv 8 0)] H15.
    img_chunk 0x538d0 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
               C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] H16.
    img_chunk 0x539f0 [C8 (Z_to_bv 64 0)] H17.
    pose proof entry_rtd as H1.
    repeat (split; [assumption|]). exact H17.
  Qed.

  Lemma entry_cjst : CJST mem.
  Proof.
    unfold CJST, wz, PHOOKS, PGERROR, PLCONV, PMALLOC, PFREE, PREALLOC, PDOTSTR.
    img_chunk 0x23528 [C8 (Z_to_bv 64 0x15320); C8 (Z_to_bv 64 0x151e0); C8 (Z_to_bv 64 0x16b8c)] H1.
    img_chunk 0x337b0 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] H2.
    img_chunk 0x223f8 [C8 (Z_to_bv 64 0x102de)] H3.
    split; [exact H1|]. split; [exists (Z_to_bv 64 0), (Z_to_bv 64 0); exact H2| exact H3].
  Qed.

  Lemma entry_stdout : stdout_file mem stdout_init.
  Proof. apply stdout_file_init; intros a Ha; apply entry_none; lia. Qed.

  Lemma entry_stderr : stderr_wfile0 mem.
  Proof. apply stderr_wfile0_init; intros a Ha; apply entry_none; lia. Qed.

  Lemma entry_initflag : rw_cells psegs mem PINITFLAG [C1 (Z_to_bv 8 0)].
  Proof. unfold PINITFLAG. img_chunk 0x33780 [C1 (Z_to_bv 8 0)] H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma entry_rs : rw_cells psegs mem PRS [CB RSN (repeat (Z_to_bv 8 0) RSN)].
  Proof.
    rewrite <- (repeat_length (Z_to_bv 8 0) RSN) at 1.
    apply (rw_cells_image0 psegs mem PRS (repeat (Z_to_bv 8 0) RSN)).
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
    pose proof usp_lo as LO. pose proof usp_hi as HI. pose proof bsb_len_bound as BL. pose proof (PF.len_av inp VA) as LA.
    destruct VE as [LE _].
    pose proof (RL.rnd_facts psegs Sv48 inp mbase Plain.M.phdrs RENT sp0 brk rnd) as RF.
    repeat (specialize (RF ltac:(lctx))).
    destruct RF as (R1 & R2 & R3 & R4 & R5).
    fold SIMG in R2, R3.
    pose proof (F.u64_range (at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev)) as RR.
    set (rptr := bv_unsigned (at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev)) in *.
    assert (AB : (RL.auxv_off av ev + auxv_size (kb_rseq (in_kernel inp)) + 16 <= length SIMG)%nat)
      by (unfold SIMG; apply (RL.auxv_off_bound _ _ _ _ _ brk _)).
    assert (AS : (auxv_size (kb_rseq (in_kernel inp)) <= 464)%nat)
      by (unfold auxv_size, auxv_count; destruct (kb_rseq (in_kernel inp)); lia).
    unfold RL.auxv_off in AB.
    exists (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)),
           (launch_auxv inp sp0 mbase), Plain.M.phdrs, RENT, (in_uid inp), (in_gid inp), (in_hwcap inp),
           (at_execfn_ptr (ed_top rnd) (in_execfn inp)), rptr.
    split; [| split; [| split; [| unfold LB in *; lia]]].
    - pose proof (proj1 (proj1 (rw_cells_app psegs mem 0x53b20 [C8 (PD.auxv_w sp0 inp)] _) entry_libc2)) as C.
      unfold RAUXV_CELL, MallocRep.wz, CJ_iface.wz. unfold PD.auxv_w in C. exact C.
    - assert (R : rdn psegs (stack_to_mem sp0 SIMG) (sp0 + nat_to_word (RL.auxv_off av ev)) (auxv_size (kb_rseq (in_kernel inp)))
                  = Some (auxv_bytes (launch_auxv inp sp0 mbase) Plain.M.phdrs RENT (in_uid inp) (in_gid inp) (in_hwcap inp)
                            (at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev) (at_execfn_ptr (ed_top rnd) (in_execfn inp))))
        by (unfold SIMG; eapply RL.read_auxv_all; first [lctx | exact (conj LE (proj2 VE))]).
      rewrite RL.auxv_bytes_words in R.
      rewrite RL.auxv_words_eq in R.
      rewrite flat_map_le8_u64s in R.
      rewrite StepTac.word_add_nat in R. unfold RL.auxv_off in R.
      pose proof (F.rdn_length _ _ _ _ _ R) as RL'.
      pose proof (entry_above_bytes (Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (8 + 8 * (length av + 1) + 8 * (length ev + 1))))) as B.
      rewrite unsigned_lit in B by lia.
      replace (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))
        with (bv_unsigned sp0 + Z.of_nat (8 + 8 * (length av + 1) + 8 * (length ev + 1))) by lia.
      unfold auxv_list, MallocRep.wz, CJ_iface.wz. unfold rptr. rewrite Z_to_bv_bv_unsigned.
      apply B; [lia| rewrite RL'; unfold LB in *; lia|]. rewrite RL'. exact R.
    - rewrite HSEC, rnd_secret_le8.
      pose proof (entry_above_bytes (Z_to_bv 64 (rptr + 8)) (firstn 8 (skipn 8 (at_random_bytes (ed_random rnd))))) as B.
      rewrite length_firstn, length_skipn, length_at_random_bytes in B. cbn [Nat.sub Nat.min] in B.
      rewrite unsigned_lit in B by (unfold LB in *; lia). apply B; [lia| cbn; unfold LB in *; lia|].
      replace (rptr + 8) with (rptr + Z.of_nat 8) by lia. apply (R5 8%nat 8%nat). lia.
  Qed.
End Entry.


End CeilWrap.
