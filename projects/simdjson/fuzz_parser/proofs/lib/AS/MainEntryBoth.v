(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: bmain_at restates the launch block's layout (argv's strings at the block's top, the hidden bytes against the launch's initial memory, the stack span STACK_SPAN below sp, the pad, gap and gid variables) with its facts in the recorded numbering renamed onto the start-up hand-off states the build computes (MainFactsBoth.fM) and justified against those states by computation, the model gains the vDSO pair's reservations and the channel reader's fields, the bridge takes the run's whole launch input, and both_side_ok lifts the walk to the run's segments (RomStable.srun_init). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit BothStartup BothStartupCert2 BothBoot
  RegsEqv0 SrzEqv MainExport MainRename MainFactsBoth RomStable.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Nodes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import AcctCore TopLevelGen.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import TopLevel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition BMAIN : Z := 0x95160.           (* [comment removed for export] *)
Definition BRA : Z := 0xf9ed4.             (* [comment removed for export] *)
Definition BGP : Z := 0x10800.             (* [comment removed for export] *)
Definition BTP : Z := 0x64e9f0.            (* [comment removed for export] *)
Definition BIMG_LO : Z := 0x10000.         (* [comment removed for export] *)
Definition BIMG_HI : Z := 0x671000.
Definition ACEIL : Z := 0x7fff7f800000.    (* [comment removed for export] *)
Definition KHIGH : Z := 0x10007fff8000.    (* [comment removed for export] *)
Definition ASHOFF : Z := 0x7fff8000.       (* [comment removed for export] *)
Definition ABAND_LO : Z := 0x7fff7000.     (* [comment removed for export] *)
Definition ABAND_LEN : Z := 0x100000001000.
Definition V_VMBRK : nat := 452.           (* [comment removed for export] *)

Lemma bsegs_BSEGS : BSEGS = bsegs. Proof. reflexivity. Qed.
Lemma bph_BPH : BPH = b_phdrs. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record bmodel (V : nat -> Z) (sp : word) (fs : Fs.Fs) (mo : Model) : Prop := BMODEL {
  bm_halted   : m_halted mo = None;
  bm_fds      : m_fds mo = [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
                            (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))];
  bm_fs       : m_fs mo = fs;
  (* LPS 727298f3: the launch reserves the image's ranges AND the vDSO pair ([State.init_reserved]):
     at most two intervals, at most twenty pages, above the image, below 2^47 ([AsanPlanSound.co_res]) *)
  bm_reserved : exists rx, vm_reserved (m_vmmaps mo) = segments_reserved bsegs ++ rx
                  /\ (length rx <= 2)%nat /\ ivs_sum rx <= 81920
                  /\ Forall (fun iv => 0 < bv_unsigned (snd iv) /\ BIMG_HI <= bv_unsigned (fst iv)
                                       /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= 2 ^ 47) rx;
  bm_limit    : vm_limit (m_vmmaps mo) = target_alloc_limit;
  bm_brk      : vm_brk (m_vmmaps mo) = Z_to_bv 64 (V V_VMBRK);
  bm_start_brk : bv_unsigned (vm_start_brk (m_vmmaps mo)) <= V V_VMBRK;
  (* [comment removed for export] *)
  bm_top      : vm_init_sp (m_vmmaps mo) = sp;
  bm_usp      : 0x7fff80000000 <= bv_unsigned sp /\ bv_unsigned sp <= 0x800000000000 /\ bv_unsigned sp mod 16 = 0;
  (* [comment removed for export] *)
  bm_maps     : ledger_den V both_ledger (vm_maps (m_vmmaps mo));
  bm_kinds    : Forall (lentry_kind_ok V mo) both_ledger;
  bm_sep      : ivs_sep (vm_maps (m_vmmaps mo));
  bm_bounds   : Forall (fun iv => 0 < bv_unsigned (snd iv) /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                                  /\ 0 < bv_unsigned (fst iv)
                                  /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= BIMG_LO \/ BIMG_HI <= bv_unsigned (fst iv))
                                  /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned sp - 8388608)
                       (vm_maps (m_vmmaps mo));
  bm_lazy_bounds : Forall (fun iv => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= BIMG_LO \/ BIMG_HI <= bv_unsigned (fst iv))
                                     /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned sp - 8388608)
                          (m_vm_lazy mo);
  bm_noaccess_wf : Forall (fun iv => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= 2 ^ 64) (vm_noaccess (m_vmmaps mo));
  bm_noaccess_sub : forall z, MainExport.in_ivs z (vm_noaccess (m_vmmaps mo)) -> MainExport.in_ivs z (vm_maps (m_vmmaps mo));
  (* [comment removed for export] *)
  bm_noaccess_pos : Forall (fun iv => 0 < bv_unsigned (snd iv)) (vm_noaccess (m_vmmaps mo));
  bm_totsz    : ivs_sum (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) <= both_totsz;
  (* [comment removed for export] *)
  bm_nonlazy  : nonlazy_bytes mo <= both_eager;
  bm_abytes   : ivz_bytes (allow_of ASHOFF V both_vis) <= both_abytes;
  bm_budget   : nonlazy_bytes mo + ivz_bytes (allow_of ASHOFF V both_vis) <= target_alloc_limit;
  bm_allow_wf : ivz_wf (allow_of ASHOFF V both_vis);
  bm_mat_nodup : List.NoDup (m_vm_materialized mo);
  bm_mat      : forall p, In p (m_vm_materialized mo) ->
                  bv_unsigned p mod 4096 = 0 /\ page_in_ranges p (m_vm_lazy mo) = true /\ aallowed (allow_of ASHOFF V both_vis) p;
  (* LPS 727298f3: every map is apart from every reservation, the vDSO pair included ([co_mres]) *)
  bm_mres     : Forall (fun iv => Forall (iv_disjoint iv) (vm_reserved (m_vmmaps mo))) (vm_maps (m_vmmaps mo));
  (* LPS 727298f3: the channel's reader bit, which [Lib/Nodes.minv] carries ([co_rdr]) *)
  bm_reader   : m_channel_reader mo = true
}.

(* LPS 727298f3: the stack span the start guarantees mapped below sp is the model's zero-filled window
   ([StoreOk.stack_window_depth] = 6144513, AsanPlanCore's STK_ZDEPTH), not 8 MiB: RLIMIT_STACK is
   counted from the stack VMA's end.  The main phase's stack region is the page-aligned span below
   it; the allocator ceiling stays 8 MiB below sp ([alloc_top]). *)
Definition STACK_SPAN : Z := 0x5D0000.

(* LPS 727298f3: argv[0]'s first byte.  The strings sit at the TOP of the block, above the auxv
   ([AUXSZ] bytes), the alignment gap, the sixteen AT_RANDOM bytes and the [arch_align_stack] pad
   (AsanInit's [STR0]). *)
Definition str0_of (en : ExecEntry) (inp : ProcInput) : Z :=
  bv_unsigned (en_sp en) + Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
  + Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) (en_sp en) (ed_top (en_draw en)) (in_argv inp) (in_envp inp) (in_execfn inp)).

(* LPS 727298f3: the block bytes the start-up never reads as values, AsanInit's [argH0]: argv[2..],
   envp and their NULLs, and the string area up to the stack VMA's end *)
Definition hidden_arg (en : ExecEntry) (inp : ProcInput) (a : Z) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
  (usp + 24 <= a < usp + 8 * argc + 8 * envc + 24)
  \/ (str0_of en inp <= a < bv_unsigned (ed_top (en_draw en))).

(* the launch's initial memory, as [Run.init_config] maps it *)
Definition bmem0 (en : ExecEntry) (inp : ProcInput) : word -> option byte :=
  wrap_mem inp (en_mmap_base en) b_phdrs (Z_to_bv 64 (Z.of_N b_init_pc)) (en_sp en) (en_draw en).

(* the run's CONFIG_RSEQ value as 0 or 1: the auxv is [AUXSZ (brz inp)] bytes *)
Definition brz (inp : ProcInput) : Z := rseq_z (kb_rseq (in_kernel inp)).
Lemma brz_cases : forall inp, (kb_rseq (in_kernel inp) = false /\ brz inp = 0) \/ (kb_rseq (in_kernel inp) = true /\ brz inp = 1).
Proof. intros inp. unfold brz. destruct (kb_rseq (in_kernel inp)); [right | left]; split; reflexivity. Qed.

(* [comment removed for export] *)
Definition bshadow (a : Z) : Prop := (0x7fff7000 <= a < 0x8fff7000) \/ (0x2008fff7000 <= a < 0x10007fff8000).
Definition BSHADOWS : list (Z * Z) := [(0x7fff7000, 0x8fff7000); (0x2008fff7000, 0x10007fff8000)].
Definition bshadow_vis (V : nat -> Z) (a : Z) : Prop :=
  exists bn, In bn both_vis_app /\ ASHOFF + zv V (fst bn) / 8 <= a < ASHOFF + (zv V (fst bn) + zv V (snd bn)) / 8.
(* [comment removed for export] *)
Definition bshadow0 (V : nat -> Z) (m : word -> option byte) : Prop :=
  forall a, bshadow a -> ~ bshadow_vis V a -> m (wa a) = Some (Z_to_bv 8 0).

(* [comment removed for export] *)

(* LPS 727298f3: the facts are in the numbering of the start-up the plans were recorded against
   (the bridge renames them onto the computed hand-off state, [MainFactsBoth.fM]); the block's
   layout facts ([both_mem_facts_l], [both_pure_facts_l]) depend on the run's CONFIG_RSEQ value, the
   auxv being [AUXSZ rz] bytes; V 4 is the [arch_align_stack] pad in bytes, V 11 the gap in words and
   V 12 the gid, as the start state names them ([AsanInit.vals0]). *)
Definition bmain_at (en : ExecEntry) (inp : ProcInput) (ms : machine_state) (mo : Model) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
  let rseq := kb_rseq (in_kernel inp) in
  exists (w : bool) (V : nat -> Z) (m : word -> option byte),
    ms = MS (mkR (Z_to_bv 64 BRA) (Z_to_bv 64 (usp - 48)) (Z_to_bv 64 BGP) (Z_to_bv 64 BTP)
                 (Z_to_bv 64 (V 1017%nat)) (Z_to_bv 64 (V 1018%nat)) (Z_to_bv 64 (V 1019%nat))
                 (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (usp + 8))
                 (Z_to_bv 64 (usp + 8 * argc + 16)) (Z_to_bv 64 0x6000000000000000)
                 (Z_to_bv 64 (V 1020%nat)) (Z_to_bv 64 (V 1021%nat)) (Z_to_bv 64 (V 1022%nat)) (Z_to_bv 64 (V 1023%nat))
                 (Z_to_bv 64 BMAIN) (Z_to_bv 64 (usp + 8 * argc + 16))
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 (V 1024%nat)) (Z_to_bv 64 (V 1025%nat)) (Z_to_bv 64 (V 1026%nat)) (Z_to_bv 64 (V 1027%nat)))
            bvmap_empty (Z_to_bv 64 BMAIN) (Z_to_bv 32 0) None m (seg_rom bsegs)
    /\ (forall n, 0 <= V n < 2 ^ 64)
    (* [comment removed for export] *)
    /\ (V 0%nat = usp / 32768 /\ V 6%nat = usp mod 4096 / 16 /\ V 10%nat = usp mod 32768 / 4096
        /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp
        /\ V 1%nat = argc /\ V 2%nat = envc
        /\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) [])) /\ V 7%nat = Z.of_nat (length (nth 1 (in_argv inp) []))
        /\ V 4%nat = Z.of_nat (block_pad_len rseq (en_sp en) (ed_top (en_draw en)) (in_argv inp) (in_envp inp) (in_execfn inp))
        /\ V 5%nat = bv_unsigned (en_brk en) / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
        /\ V 9%nat = bv_unsigned (in_hwcap inp)
        /\ V 11%nat = Z.of_nat (block_items (in_argv inp) (in_envp inp) mod 2)
        /\ V 12%nat = bv_unsigned (in_gid inp))
    /\ Forall (mfact_ok bsegs V m) (both_mem_facts ++ both_mem_facts_w w ++ both_mem_facts_l (brz inp))
    /\ Forall (pfact_ok V) (both_pure_facts ++ both_pure_facts_w w ++ both_pure_facts_l (brz inp))
    /\ mem_inv bsegs m
    /\ stk bsegs m (usp - STACK_SPAN) usp
    /\ (forall a, hidden_arg en inp a -> m (wa a) = bmem0 en inp (wa a))
    /\ bshadow0 V m
    /\ bmodel V (en_sp en) (in_fs inp) mo.

(* [comment removed for export] *)
Lemma bshadow0_range : forall V m lo n,
  bshadow0 V m -> 0 < n ->
  (forall a, lo <= a < lo + n -> bshadow a /\ ~ bshadow_vis V a) ->
  (forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0))
  /\ wr_at bsegs m lo n /\ rw_cells bsegs m lo [CB (Z.to_nat n) (zeros n)].
Proof.
  intros V m lo n H0 Hn HR.
  assert (Z0 : forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. destruct (HR (lo + i) ltac:(lia)) as (S1 & S2). exact (H0 _ S1 S2). }
  split; [exact Z0|].
  destruct (HR lo ltac:(lia)) as (Slo & _). destruct (HR (lo + n - 1) ltac:(lia)) as (Shi & _). unfold bshadow in Slo, Shi.
  apply overlay_zero_rw; [lia| unfold MainExport.two64; lia| lia| exact Z0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sub_of (bn : zexp * zexp) (b' : zexp) (n' : Z) : bool :=
  match snd bn with
  | ZLit nn =>
      (zexp_eqb (fst bn) b' && (0 <=? nn) && (nn <=? n'))
      || match fst bn with
         | ZAdd b0 (ZLit k) => zexp_eqb b0 b' && (0 <=? k) && (0 <=? nn) && (k + nn <=? n')
         | _ => false
         end
  | _ => false
  end.

Lemma sub_of_sound : forall V bn b' n', sub_of bn b' n' = true ->
  zv V b' <= zv V (fst bn) /\ zv V (fst bn) + zv V (snd bn) <= zv V b' + n'.
Proof.
  intros V [b n] b' n' H. unfold sub_of in H. cbn [fst snd] in *. destruct n as [nn| | | | |]; try discriminate.
  apply orb_prop in H as [H|H].
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply zexp_eqb_eq in H1. subst b'.
    apply Z.leb_le in H2. apply Z.leb_le in H3. cbn [zv]. lia.
  - destruct b as [| |b0 k| | |]; try discriminate. destruct k as [k| | | | |]; try discriminate.
    apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply zexp_eqb_eq in H1. subst b'. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. cbn [zv]. lia.
Qed.

(* [comment removed for export] *)
Definition band_fact (blo blen : Z) (PF : list pfact) (bn : zexp * zexp) : bool :=
  existsb (fun f => match f with
                    | PDisj b' n' (ZLit c) d => (c =? blo) && (d =? blen) && sub_of bn b' n'
                    | _ => false
                    end) PF.

Lemma band_fact_sound : forall V blo blen PF bn a, Forall (pfact_ok V) PF -> band_fact blo blen PF bn = true ->
  blo <= a < blo + blen -> ~ (zv V (fst bn) <= a < zv V (fst bn) + zv V (snd bn)).
Proof.
  intros V blo blen PF bn a HPF H Ha Hin. unfold band_fact in H. apply existsb_exists in H as (f & Hf & Hm).
  destruct f as [| |b' n' c d|]; try discriminate. destruct c as [c| | | | |]; try discriminate.
  apply andb_prop in Hm as [Hm H3]. apply andb_prop in Hm as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst c d.
  pose proof (sub_of_sound V bn b' n' H3) as [S1 S2].
  pose proof (proj1 (Forall_forall _ _) HPF _ Hf) as D. cbn [pfact_ok zv] in D. lia.
Qed.

(* [comment removed for export] *)
Definition shad_clear (VR : vranges) (PF : list pfact) (bn : zexp * zexp) : bool :=
  range_clear BSHADOWS VR bn || band_fact ABAND_LO ABAND_LEN PF bn.

Lemma shad_clear_sound : forall V VR PF bn a, vr_sound V VR -> Forall (pfact_ok V) PF -> shad_clear VR PF bn = true ->
  (exists s, In s BSHADOWS /\ fst s <= a < snd s) -> ~ (zv V (fst bn) <= a < zv V (fst bn) + zv V (snd bn)).
Proof.
  intros V VR PF bn a HV HPF H HS. unfold shad_clear in H. apply orb_prop in H as [H|H].
  - exact (range_clear_sound V VR BSHADOWS bn a HV H HS).
  - apply (band_fact_sound V ABAND_LO ABAND_LEN PF bn a HPF H).
    destruct HS as (s & Hs & Ha). unfold ABAND_LO, ABAND_LEN. cbn in Hs. destruct Hs as [<-|[<-|[]]]; cbn in Ha; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* LPS 727298f3: the main-entry facts are justified against the computed hand-off states by
   computation (kept here, not in [MainFactsBoth], so a file that only reads the facts builds
   apart from these checks) *)
Ltac main_cases := intros r w Hr; assert (r = 0 \/ r = 1) as [-> | ->] by lia; destruct w.
Lemma both_regs_main : forall r w, 0 <= r <= 1 -> s_regs (a_ss (HS2 r w)) = REGS_MAIN.
Proof. main_cases; vm_compute; reflexivity. Qed.
Lemma both_main_pc : forall r w, 0 <= r <= 1 -> pc (HS2 r w) = 610656.
Proof. main_cases; vm_compute; reflexivity. Qed.
Lemma both_main_fd : forall r w, 0 <= r <= 1 -> a_fd (HS2 r w) = FdStd.
Proof. main_cases; vm_compute; reflexivity. Qed.
Lemma both_main_brk : forall r w, 0 <= r <= 1 -> a_brk (HS2 r w) = EVar (fM 452).
Proof. main_cases; vm_compute; reflexivity. Qed.

Lemma both_mem_justified : forall r w, 0 <= r <= 1 ->
  forallb (mjustify (s_know (a_ss (HS2 r w))) (var_ranges (s_know (a_ss (HS2 r w)))) 65536 6754304)
          (map (mfsh fM) (both_mem_facts ++ both_mem_facts_w w ++ both_mem_facts_l r)) = true.
Proof. main_cases; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_pure_justified : forall r w, 0 <= r <= 1 ->
  forallb (pjustify (s_know (a_ss (HS2 r w))) (var_ranges (s_know (a_ss (HS2 r w)))))
          (map (pfsh fM) (both_pure_facts ++ both_pure_facts_w w ++ both_pure_facts_l r)) = true.
Proof. main_cases; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_vis_justified : forall r w, 0 <= r <= 1 ->
  vis_match (var_ranges (s_know (a_ss (HS2 r w)))) (a_vis (HS2 r w)) (map (zpsh fM) both_vis_app) = true
  /\ vis_match (var_ranges (s_know (a_ss (HS2 r w)))) (a_ghost (HS2 r w)) (map (zpsh fM) both_ghost) = true.
Proof. main_cases; split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_ledger_justified : forall r w, 0 <= r <= 1 ->
  ledger_xmatch (var_ranges (s_know (a_ss (HS2 r w)))) (a_maps (HS2 r w)) (map (lsh fM) both_ledger) = true.
Proof. main_cases; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_consts : forall r w, 0 <= r <= 1 ->
  a_totsz (HS2 r w) <= both_totsz /\ a_eager (HS2 r w) <= both_eager /\ a_abytes (HS2 r w) <= both_abytes.
Proof. main_cases; vm_compute; repeat split; discriminate. Qed.

Section Bridge.
  (* LPS 727298f3: the run's whole launch input, as AS/BothBoot.v's Section Boot takes it *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable inp : ProcInput.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  Hypothesis Hhw : valid_hwcap (in_hwcap inp).

  Definition en0 : ExecEntry := mkEntry sp brk0 mbase rdraw.

  #[local] Notation RZ := (rseq_z (kb_rseq (in_kernel inp))).
  #[local] Abbreviation SINV := (SINV0 BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp).
  #[local] Abbreviation argH := (argH0 sp rdraw inp).
  #[local] Abbreviation E0a := (AsanInit.E0 sp rdraw brk0 inp).
  #[local] Abbreviation LIM := AsanInit.LIMIT.
  #[local] Notation fs := (in_fs inp).

  Let AH := argH0_high AsanUbsan.M.init_pc sp rdraw inp Hsp Hva.

  Lemma RZ_range' : 0 <= RZ <= 1.
  Proof. exact (rseq_z_range _). Qed.

  (* LPS 727298f3: a main-entry hand-off state [hs] whose renamed facts it justifies ([fM]: the
     recorded numbering -> the computed one) realizes [bmain_at]; V reads the recorded numbering *)
  Theorem bmain_bridge_w : forall (w : bool) (hs : acs),
    s_regs (a_ss hs) = REGS_MAIN -> pc hs = BMAIN -> a_fd hs = FdStd -> a_brk hs = EVar (fM V_VMBRK) ->
    forallb (mjustify (kn hs) (var_ranges (kn hs)) BIMG_LO BIMG_HI)
            (map (mfsh fM) (both_mem_facts ++ both_mem_facts_w w ++ both_mem_facts_l RZ)) = true ->
    forallb (pjustify (kn hs) (var_ranges (kn hs)))
            (map (pfsh fM) (both_pure_facts ++ both_pure_facts_w w ++ both_pure_facts_l RZ)) = true ->
    vis_match (var_ranges (kn hs)) (a_vis hs) (map (zpsh fM) both_vis_app) = true
      /\ vis_match (var_ranges (kn hs)) (a_ghost hs) (map (zpsh fM) both_ghost) = true ->
    ledger_xmatch (var_ranges (kn hs)) (a_maps hs) (map (lsh fM) both_ledger) = true ->
    a_totsz hs <= both_totsz /\ a_eager hs <= both_eager /\ a_abytes hs <= both_abytes ->
    forall E R FULL mo,
    cs_ok BSEGS BOTH LIM SINV argH fs E hs R FULL mo ->
    exists ms, cfg_eqv (cfg_of BSEGS R (pc hs) FULL mo) (mkCfg ms mo) /\ bmain_at en0 inp ms mo.
  Proof.
    intros w hs Hregs Hpc Hfd Hbrk0 MJ PJ VJ LJ CONSTS E R FULL mo HC. rewrite Hpc.
    set (V := fun n => uev E (fM n)).
    (* the launch's own variables keep their numbers *)
    assert (VU : forall n, (n <= 12)%nat -> V n = uev E n).
    { intros n Hn. unfold V. do 13 (destruct n as [|n]; [reflexivity|]). lia. }
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as HSINV. pose proof HSINV as [Hev Hhid].
    pose proof (AsanInit.SINV0_sp BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau E FULL HSINV) as USP.
    pose proof (AsanInit.uE0 BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau) as (U0 & U6 & U1 & U2 & U3 & U4 & U5 & U11).
    pose proof (AsanInit.uE0_sp BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau) as U10.
    (* [AsanInit.uE0_L1] closes with [lia] inside AsanInit's Section Init, so it carries that
       section's [apc : N] although its conclusion does not mention it; no N is in scope here, so
       [eassumption] cannot close that goal and the entry pc is given, as AS/AsanStartup.v does
       for [argH0_high]. *)
    assert (U7 : uE E0a (EVar V_L1) = Z.of_nat (length (nth 1 (in_argv inp) [])))
      by (eapply AsanInit.uE0_L1; first [eassumption | exact AsanUbsan.M.init_pc]).
    assert (U8 : uE E0a (EVar V_UID) = bv_unsigned (in_uid inp)) by reflexivity.
    assert (U9 : uE E0a (EVar V_HW) = bv_unsigned (in_hwcap inp)) by reflexivity.
    assert (U12 : uE E0a (EVar V_GID) = bv_unsigned (in_gid inp)) by reflexivity.
    unfold APS.uE in U0, U6, U1, U2, U3, U4, U5, U11, U10, U7, U8, U9, U12.
    cbn [edenot] in U0, U6, U1, U2, U3, U4, U5, U11, U10, U7, U8, U9, U12.
    assert (PINu : forall n z, (n <= 12)%nat -> bv_unsigned (ev E0a n) = z -> uev E n = z).
    { intros n z Hn Hz. unfold uev. rewrite (Hev n) by (unfold NX0; lia). exact Hz. }
    pose proof (PINu 0%nat _ ltac:(lia) U0) as Q0. pose proof (PINu 6%nat _ ltac:(lia) U6) as Q6.
    pose proof (PINu 1%nat _ ltac:(lia) U1) as Q1. pose proof (PINu 2%nat _ ltac:(lia) U2) as Q2.
    pose proof (PINu 3%nat _ ltac:(lia) U3) as Q3. pose proof (PINu 4%nat _ ltac:(lia) U4) as Q4.
    pose proof (PINu 5%nat _ ltac:(lia) U5) as Q5. pose proof (PINu 7%nat _ ltac:(lia) U7) as Q7.
    pose proof (PINu 8%nat _ ltac:(lia) U8) as Q8. pose proof (PINu 9%nat _ ltac:(lia) U9) as Q9.
    pose proof (PINu 10%nat _ ltac:(lia) U10) as Q10. pose proof (PINu 11%nat _ ltac:(lia) U11) as Q11.
    pose proof (PINu 12%nat _ ltac:(lia) U12) as Q12.
    clear U0 U6 U1 U2 U3 U4 U5 U7 U8 U9 U10 U11 U12.
    assert (P0 : V 0%nat = bv_unsigned sp / 32768) by (rewrite VU by lia; exact Q0).
    assert (P6 : V 6%nat = bv_unsigned sp mod 4096 / 16) by (rewrite VU by lia; exact Q6).
    assert (P10 : V 10%nat = bv_unsigned sp mod 32768 / 4096) by (rewrite VU by lia; exact Q10).
    assert (P1 : V 1%nat = Z.of_nat (length (in_argv inp))) by (rewrite VU by lia; exact Q1).
    assert (P2 : V 2%nat = Z.of_nat (length (in_envp inp))) by (rewrite VU by lia; exact Q2).
    assert (P3 : V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) []))) by (rewrite VU by lia; exact Q3).
    assert (P7 : V 7%nat = Z.of_nat (length (nth 1 (in_argv inp) []))) by (rewrite VU by lia; exact Q7).
    assert (P4 : V 4%nat = Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) sp (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp)))
      by (rewrite VU by lia; exact Q4).
    assert (P5 : V 5%nat = bv_unsigned brk0 / 4096) by (rewrite VU by lia; exact Q5).
    assert (P8 : V 8%nat = bv_unsigned (in_uid inp)) by (rewrite VU by lia; exact Q8).
    assert (P9 : V 9%nat = bv_unsigned (in_hwcap inp)) by (rewrite VU by lia; exact Q9).
    assert (P11 : V 11%nat = Z.of_nat (block_items (in_argv inp) (in_envp inp) mod 2)) by (rewrite VU by lia; exact Q11).
    assert (P12 : V 12%nat = bv_unsigned (in_gid inp)) by (rewrite VU by lia; exact Q12).
    (* [valid_sp] is three conjuncts, the alignment last; take it by projection rather than by
       [destruct Hsp], which must clear [Hsp] and now fails ("This variable is used in
       conclusion": a term built earlier from [Hsp] depends on it). *)
    assert (Hal : bv_unsigned sp mod 16 = 0) by exact (proj2 (proj2 Hsp)).
    assert (LO : 0x7fff80000000 <= bv_unsigned sp) by (pose proof (proj1 Hsp) as H; unfold sp_window_lo in H; lia).
    assert (PSPu : 32768 * uev E 0%nat + 4096 * uev E 10%nat + 16 * uev E 6%nat = bv_unsigned sp).
    { rewrite Q0, Q6, Q10. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (PSP : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = bv_unsigned sp) by (rewrite !VU by lia; exact PSPu).
    assert (VR : forall n, 0 <= V n < 2 ^ 64) by (intros n; unfold V; apply uev_range).
    pose proof (co_top _ _ _ _ _ _ _ _ _ _ _ HC) as TOP. rewrite USP in TOP.
    assert (ATOP : atop mo = bv_unsigned sp - 8388608) by (unfold atop; rewrite TOP; reflexivity).
    eexists. split; cycle 1.
    { exists w, V, FULL. split; [reflexivity|].
      split; [exact VR|].
      split; [cbn [en0 en_sp en_brk en_draw]; repeat split; assumption|].
      assert (HIDrom : forall a, APS.hid BOTH argH E hs mo a = true -> seg_rom bsegs a = None).
      { intros a Ha. apply (APS.seg_rom_off_hull BSEGS BOTH both_in_hull).
        unfold APS.hid in Ha. apply orb_prop in Ha as [Ha|Ha].
        - pose proof (AH E a Ha) as Hc. unfold APS.in_hull. cbn [img_lo img_hi BOTH]. unfold CEIL in Hc.
          apply andb_false_iff. right. apply Z.ltb_ge. lia.
        - apply negb_true_iff in Ha. unfold APS.vis in Ha. apply orb_false_iff in Ha as [Ha _]. apply orb_false_iff in Ha as [Ha _]. exact Ha. }
      assert (HULLvis : forall a, BIMG_LO <= bv_unsigned a < BIMG_HI -> APS.hid BOTH argH E hs mo a = false).
      { intros a Ha. apply (APS.hid_hull BOTH both_hull_ok argH AH). unfold APS.in_hull. cbn [img_lo img_hi BOTH]. unfold BIMG_LO, BIMG_HI in Ha.
        apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
      pose proof (export_sound bsegs E (APS.hid BOTH argH E hs mo) FULL (kn hs) BIMG_LO BIMG_HI
                    (co_know _ _ _ _ _ _ _ _ _ _ _ HC) HIDrom HULLvis _ _ MJ PJ) as [HMF0 HPF0].
      pose proof (Forall_mfsh fM bsegs (uev E) FULL _ HMF0) as HMF.
      pose proof (Forall_pfsh fM (uev E) _ HPF0) as HPF. fold V in HMF, HPF.
      pose proof (proj1 (Forall_app _ _ _) HMF) as [HMFc _].
      pose proof (proj1 (Forall_app _ _ _) HPF) as [HPFc _].
      split; [exact HMF|]. split; [exact HPF|].
      (* [comment removed for export] *)
      split.
      { intros a b Hab. rewrite a_ro_addr.
        destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); [|reflexivity].
        destruct (Z.ltb_spec0 (bv_unsigned a) 0x10f000); [|reflexivity].
        exfalso. pose proof (mimg_cover bsegs V FULL both_mem_facts 0x10000 0x10f000 HMFc ltac:(vm_compute; reflexivity) (bv_unsigned a) ltac:(lia)) as X.
        unfold wa in X. rewrite Z_to_bv_bv_unsigned in X. congruence. }
      (* LPS 727298f3: the stack window the start guarantees ([STK_ZDEPTH] = 6144513 below sp), cut to
         the page-aligned span *)
      split.
      { pose proof (mwr_find bsegs V FULL both_mem_facts
                      (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-6144513))) 6144513
                      HMFc ltac:(vm_compute; reflexivity)) as W.
        cbn [zv] in W.
        replace (32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat) + -6144513) with (bv_unsigned sp - 6144513) in W by lia.
        cbn [en0 en_sp].
        assert (ST : stk bsegs FULL (bv_unsigned sp - 6144513) (bv_unsigned sp)).
        { apply wr_at_stk; [replace (bv_unsigned sp - (bv_unsigned sp - 6144513)) with 6144513 by lia; exact W|].
          intros a Ha. apply ref_find_segment_none; [lia|]. lia. }
        destruct (stk_split _ _ (bv_unsigned sp - 6144513) (bv_unsigned sp - STACK_SPAN) (bv_unsigned sp) ST
                    ltac:(unfold STACK_SPAN; lia)) as [_ ST2].
        exact ST2. }
      (* LPS 727298f3: the hidden block bytes are the launch's image ([SINV0]'s second half) *)
      split.
      { intros a Ha. unfold hidden_arg, str0_of in Ha. cbn [en0 en_sp en_draw] in Ha.
        pose proof (bv_unsigned_in_range 64 (ed_top rdraw)) as RT. unfold bv_modulus in RT. cbn in RT.
        (* the envp array's end (hidden_arg's first half) is below 2^64: sp <= sp_window_hi
           ([valid_sp]), at most 1024 argv and 256 envp pointers ([valid_argv], [valid_envp]) *)
        pose proof (proj1 Hva) as LAV. pose proof (proj1 Hve) as LEV.
        pose proof (proj1 (proj2 Hsp)) as LSP. unfold sp_window_hi in LSP.
        unfold bmem0. cbn [en0 en_sp en_draw en_mmap_base].
        apply Hhid. unfold argH0. rewrite wa_unsigned by lia.
        apply orb_true_intro. destruct Ha as [Ha|Ha]; [left| right];
          apply andb_true_intro; split; first [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
      (* [comment removed for export] *)
      pose proof (var_ranges_sound BSEGS E _ (kn hs) (co_know _ _ _ _ _ _ _ _ _ _ _ HC)) as HVR.
      destruct VJ as [VJa VJg].
      pose proof (vis_match_sound E _ _ _ HVR VJa) as HVISa. pose proof (vis_match_sound E _ _ _ HVR VJg) as HVISg.
      pose proof (Forall2_app HVISa HVISg) as HVIS. rewrite <- map_app in HVIS. change (both_vis_app ++ both_ghost) with both_vis in HVIS.
      pose proof (ledger_den_sound E _ HVR _ _ _ LJ (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)) as HLD0.
      pose proof (ledger_den_lsh fM (uev E) _ _ HLD0) as HLD.
      pose proof (ledger_kinds_sound E _ HVR _ _ mo LJ (co_none _ _ _ _ _ _ _ _ _ _ _ HC) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC)) as HKD0.
      pose proof (Forall_lsh_kind fM (uev E) mo _ HKD0) as HKD.
      fold V in HLD, HKD.
      (* [comment removed for export] *)
      split.
      { pose proof (pvranges_sound V both_pure_facts VR HPFc) as HVRp.
        assert (CLRv : forallb (shad_clear (pvranges both_pure_facts) both_pure_facts) both_vis_app = true) by (vm_compute; reflexivity).
        assert (CLRg : forallb (shad_clear (pvranges both_pure_facts) both_pure_facts) both_ghost = true) by (vm_compute; reflexivity).
        assert (Elow : In (LMap (ZLit 0x7fff7000) 0x10000000 KRWLAZY) both_ledger) by (cbn; tauto).
        assert (Ehigh : In (LMap (ZLit 0x2008fff7000) 0xdfff0001000 KRWLAZY) both_ledger) by (cbn; tauto).
        intros a Hsh Hnv.
        assert (Ha : 0 <= a < 2 ^ 64) by (unfold bshadow in Hsh; lia).
        assert (Ua : bv_unsigned (wa a) = a) by (apply wa_unsigned; exact Ha).
        assert (KL : ~ MainExport.in_ivs a (vm_noaccess (m_vmmaps mo)) /\ page_in_ranges (page_base (wa a)) (m_vm_lazy mo) = true
                     /\ APS.in_ivs a (vm_maps (m_vmmaps mo)) = true).
        { destruct Hsh as [Hsh|Hsh].
          - pose proof (proj1 (Forall_forall _ _) HKD _ Elow) as K. cbn [lentry_kind_ok zv] in K.
            destruct (K (wa a) ltac:(rewrite Ua; lia)) as [K1 K2]. rewrite Ua in K1. split; [exact K1|]. split; [exact K2|].
            apply (proj2 (in_ivs_APS _ _)). exists (wa 0x7fff7000, wa 0x10000000). split; [exact (ledger_den_In V _ _ _ _ _ HLD Elow)|].
            cbn [fst snd]. rewrite !wa_unsigned by lia. lia.
          - pose proof (proj1 (Forall_forall _ _) HKD _ Ehigh) as K. cbn [lentry_kind_ok zv] in K.
            destruct (K (wa a) ltac:(rewrite Ua; lia)) as [K1 K2]. rewrite Ua in K1. split; [exact K1|]. split; [exact K2|].
            apply (proj2 (in_ivs_APS _ _)). exists (wa 0x2008fff7000, wa 0xdfff0001000). split; [exact (ledger_den_In V _ _ _ _ _ HLD Ehigh)|].
            cbn [fst snd]. rewrite !wa_unsigned by lia. lia. }
        destruct KL as (Kna & Klz & Kmap).
        assert (HSS : exists s, In s BSHADOWS /\ fst s <= a < snd s).
        { destruct Hsh as [Hsh|Hsh]; [exists (0x7fff7000, 0x8fff7000) | exists (0x2008fff7000, 0x10007fff8000)]; cbn; split; auto; lia. }
        apply (co_zero _ _ _ _ _ _ _ _ _ _ _ HC (wa a)); rewrite ?Ua.
        - (* [comment removed for export] *)
          unfold APS.hid. apply orb_true_intro. right. apply negb_true_iff. unfold APS.vis. rewrite Ua.
          rewrite Klz. cbn [negb].
          replace (APS.in_hull BOTH a) with false.
          2:{ symmetry. unfold APS.in_hull. cbn [img_lo img_hi BOTH]. apply andb_false_iff. right. apply Z.ltb_ge. unfold bshadow in Hsh. lia. }
          replace (atop mo <=? a) with false by (symmetry; apply Z.leb_gt; rewrite ATOP; unfold bshadow in Hsh; lia).
          cbn [orb]. replace (APS.in_allow BOTH E hs a) with false; [destruct (APS.in_ivs _ _ && _)%bool; reflexivity|].
          symmetry. unfold APS.in_allow. apply orb_false_intro.
          + (* [comment removed for export] *)
            unfold APS.in_vis. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Xp).
            apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
            destruct (Forall2_In_l _ _ _ _ HVISa Hp) as (bn & Hbn & E1 & E2 & E3).
            apply in_map_iff in Hbn as (bn0 & <- & Hbn0). cbn [zpsh fst snd] in E1, E2. rewrite !zv_zsh in E1, E2. fold V in E1, E2.
            unfold APS.uE in X1, X2. rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2.
            apply (shad_clear_sound V _ both_pure_facts bn0 a HVRp HPFc (proj1 (forallb_forall _ _) CLRv bn0 Hbn0) HSS). lia.
          + (* [comment removed for export] *)
            unfold APS.in_sh. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Xp).
            apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. unfold APS.sh_lo, APS.sh_hi, APS.uE in X1, X2.
            destruct (Forall2_In_l _ _ _ _ HVISa Hp) as (bn & Hbn & E1 & E2 & E3).
            apply in_map_iff in Hbn as (bn0 & <- & Hbn0). cbn [zpsh fst snd] in E1, E2. rewrite !zv_zsh in E1, E2. fold V in E1, E2.
            rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2.
            apply Hnv. exists bn0. split; [exact Hbn0|]. change (shadow_off BOTH) with ASHOFF in X1, X2. lia.
        - exact Kmap.
        - apply Bool.not_true_iff_false. intros X. apply Kna. apply (proj1 (in_ivs_APS _ _)). exact X.
        - exact Klz.
        - (* [comment removed for export] *)
          unfold APS.in_ghost. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Xp).
          apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. unfold APS.uE in X1, X2.
          destruct (Forall2_In_l _ _ _ _ HVISg Hp) as (bn & Hbn & E1 & E2 & E3).
          apply in_map_iff in Hbn as (bn0 & <- & Hbn0). cbn [zpsh fst snd] in E1, E2. rewrite !zv_zsh in E1, E2. fold V in E1, E2.
          rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2.
          apply (shad_clear_sound V _ both_pure_facts bn0 a HVRp HPFc (proj1 (forallb_forall _ _) CLRg bn0 Hbn0) HSS). lia. }
      (* [comment removed for export] *)
      pose proof (allowA_allow_of BOTH E _ _ HVIS) as HAL. change (shadow_off BOTH) with ASHOFF in HAL.
      change (flat_map (allow1 BOTH E) (a_vis hs ++ a_ghost hs)) with (allowA BOTH E hs) in HAL.
      rewrite allow_of_zpsh in HAL. fold V in HAL.
      pose proof CONSTS as (Ct & Ce & Ca).
      assert (USPW : vm_init_sp (m_vmmaps mo) = sp) by (apply bv_eq; exact TOP).
      destruct HC. cbn [in_fs en0 en_sp]. rewrite Hfd in co_fds0. rewrite Hbrk0 in co_brk0.
      constructor.
      + exact co_halt0.
      + exact co_fds0.
      + exact co_fs0.
      + destruct co_res0 as (rx & Hres & Hok & Hlen & Hsum). exists rx. split; [exact Hres|].
        assert (NR : n_resx BOTH = 2%nat) by reflexivity. assert (RB : resx_bytes BOTH = 81920) by reflexivity.
        rewrite NR in Hlen. rewrite RB in Hsum.
        split; [exact Hlen|]. split; [exact Hsum|].
        eapply Forall_impl; [|exact Hok]. intros iv (R1 & _ & _ & R4 & _ & R6). cbn [img_hi BOTH] in R4.
        unfold BIMG_HI. repeat split; lia.
      + exact co_limit0.
      + rewrite co_brk0. cbn [edenot]. symmetry. apply Z_to_bv_bv_unsigned.
      + rewrite co_brk0 in co_sbrk0. cbn [edenot] in co_sbrk0. exact co_sbrk0.
      + exact USPW.
      + split; [exact LO|]. split; [pose proof (proj1 (proj2 Hsp)) as H; unfold sp_window_hi in H; lia| exact Hal].
      + exact HLD.
      + exact HKD.
      + apply seps_ivs_sep. exact co_seps0.
      + eapply Forall_impl; [|exact co_bounds0]. cbv beta. intros iv (B1 & B2 & B3 & B4 & B5 & B6).
        unfold hull_clear in B5. cbn [img_lo img_hi BOTH] in B5. rewrite ATOP in B6. unfold BIMG_LO, BIMG_HI. repeat split; assumption.
      + eapply Forall_impl; [|exact co_lazyb0]. cbv beta. intros iv (B5 & B6).
        unfold hull_clear in B5. cbn [img_lo img_hi BOTH] in B5. rewrite ATOP in B6. unfold BIMG_LO, BIMG_HI. split; assumption.
      + destruct co_wf0 as (_ & Wn & _). apply Forall_forall. intros iv Hiv. exact (Wn iv Hiv).
      + intros z Hz. apply (proj1 (in_ivs_APS _ _)). apply co_nasub0. apply (proj2 (in_ivs_APS _ _)). exact Hz.
      + exact co_napos0.
      + eapply Z.le_trans; [exact co_totsz0| exact Ct].
      + eapply Z.le_trans; [exact co_eager0| exact Ce].
      + rewrite <- HAL. eapply Z.le_trans; [exact co_abytes0| exact Ca].
      + rewrite <- HAL. pose proof (minv_budget _ _ co_minv0) as B. rewrite co_limit0 in B. exact B.
      + rewrite <- HAL. exact (APS.A_wf_allowA BOTH (fun _ : nat => @None acs) XN0 XE0 XB0 NX0 E hs).
      + exact (minv_nodup _ _ co_minv0).
      + intros p Hp. split; [exact (minv_aligned _ _ co_minv0 p Hp)|]. split; [exact (minv_lazy _ _ co_minv0 p Hp)|].
        rewrite <- HAL. apply page_allowedb_aallowed. exact (minv_allowed _ _ co_minv0 p Hp).
      + exact co_mres0.
      + exact co_rdr0. }
    - (* [comment removed for export] *)
      unfold cfg_of. split; [|reflexivity]. cbn [cfg_ms].
      split; [| split; [apply regs_eqv_refl| repeat split; reflexivity]].
      cbn [ms_regs AS.PropExec.mkst MS].
      intros r Hr. destruct (OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib.RegsEquiv.reg_of_nat r) as (n & -> & Hn).
      pose proof (is_x0_of_nat n Hn Hr) as Hn1.
      rewrite (regs_ok_nth E _ R (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) n Hn1). rewrite reg_get_mkR by exact Hn1. rewrite Hregs.
      destruct n as [|n]; [cbv in Hr; discriminate|].
      cbn [en0 en_sp in_argv in_envp]. unfold REGS_MAIN.
      do 31 (destruct n as [|n];
        [ cbn [nth];
          first [ reflexivity
                | symmetry; apply Z_to_bv_bv_unsigned
                | erewrite <- (zexp_of_sound E) by reflexivity; cbn [zv]; unfold V; cbn [fM];
                  unfold BMAIN, BRA, BGP, BTP; f_equal; lia ]
        |]). lia.
  Qed.

  (* LPS 727298f3: both main-entry hand-offs of the computed start-up, at the run's CONFIG_RSEQ value *)
  Theorem bmain_bridge : forall h ch, HS_both2 RZ h = Some ch -> forall E R FULL mo,
    cs_ok BSEGS BOTH LIM SINV argH fs E ch R FULL mo ->
    exists ms, cfg_eqv (cfg_of BSEGS R (pc ch) FULL mo) (mkCfg ms mo) /\ bmain_at en0 inp ms mo.
  Proof.
    intros h ch Hh. destruct (HS2_cases RZ h ch RZ_range' Hh) as [w ->].
    exact (bmain_bridge_w w (HS2 RZ w) (both_regs_main RZ w RZ_range') (both_main_pc RZ w RZ_range')
             (both_main_fd RZ w RZ_range') (both_main_brk RZ w RZ_range')
             (both_mem_justified RZ w RZ_range') (both_pure_justified RZ w RZ_range')
             (both_vis_justified RZ w RZ_range') (both_ledger_justified RZ w RZ_range') (both_consts RZ w RZ_range')).
  Qed.

  (* [comment removed for export] *)
  Variable T : TSet.
  Hypothesis T_nil : T [].
  Hypothesis MAINA : forall ms mo, bmain_at en0 inp ms mo -> srealizes bsegs (mkCfg ms mo) T.

  Theorem both_main_boot :
    srealizes bsegs (init_config bsegs AsanUbsan.M.init_pc b_phdrs sp brk0 mbase rdraw target_alloc_limit inp) T.
  Proof.
    change bsegs with BSEGS. change b_phdrs with BPH. change target_alloc_limit with AsanInit.LIMIT.
    apply (both_boot sp rdraw brk0 mbase inp Hsp Hbrk Hmb Hva Hve Huid Hlaunch Hrdr Hlau Hhw (fun _ _ => T)).
    - intros; reflexivity.
    - intros; exact T_nil.
    - intros h ch Hh E R FULL mo HC. destruct (bmain_bridge h ch Hh E R FULL mo HC) as (ms & Heqv & Hat).
      apply (srealizes_eqv BSEGS (mkCfg ms mo) T (MAINA ms mo Hat)). apply cfg_eqv_sym. exact Heqv.
  Qed.
End Bridge.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* LPS 727298f3: the run reads the binary over [run_segments] (the image's segments and the vDSO
   pair) from [init_config (run_segments ..)]; [RomStable.srun_init] carries the walk over the
   image's own segments there ([bsegs] has no kernel mapping). *)
Theorem both_side_ok : forall T : tfam,
  (forall en inp, valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp ->
      T inp en [] /\ forall ms mo, bmain_at en inp ms mo -> srealizes bsegs (mkCfg ms mo) (T inp en)) ->
  side_ok bsegs b_init_pc b_phdrs target_alloc_limit T.
Proof.
  intros T HT. apply side_ok_of_srealizes. intros [sp brk0 mbase rdraw] inp Hv Hi.
  destruct (HT _ _ Hv Hi) as [Tnil MAINA].
  rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in Hv.
  destruct Hv as (Hsp & Hbrk & Hmb & _ & Hlau).
  pose proof (valid_input_either_launch inp Hi) as Hlaunch.
  pose proof (OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib.Nodes.valid_input_either_reader inp Hi) as Hrdr.
  assert (Hva : valid_argv (in_argv inp)) by (clear - Hi; red in Hi; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  assert (Hve : valid_envp (in_envp inp)) by (clear - Hi; red in Hi; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  assert (Huid : valid_id (in_uid inp)) by (clear - Hi; red in Hi; unfold valid_creds in Hi; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  assert (Hhw : valid_hwcap (in_hwcap inp)) by (clear - Hi; red in Hi; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  cbn [en_sp en_brk en_mmap_base en_draw].
  apply srun_init; [vm_compute; repeat constructor|].
  exact (both_main_boot sp rdraw brk0 mbase inp Hsp Hbrk Hmb Hva Hve Huid Hlaunch Hrdr Hlau Hhw _ Tnil MAINA).
Qed.
