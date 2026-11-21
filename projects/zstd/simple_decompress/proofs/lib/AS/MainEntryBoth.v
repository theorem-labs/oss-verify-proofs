(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (bmain_at over the launch's whole ProcInput: the pad pin (Wpad), the hidden argument block as argH0's two ranges (hidden_arg, STR0_of), the argv pointer cells in the launch's terms (argv_cells), the launch's memory (wrap_mem) and the zero-mapped stack window 6,144,513 below sp; the facts remade by MainRegen's rule from the computed main-entry states per CONFIG_RSEQ value (bmf, bpf) and the recorded lists as kept (BMKN, BMKNW, BPKN, keep_facts); bmodel's reserved ledger with the vDSO pair, the mappings' clearance from it, the channel-reader fact and the computed total BTOTSZ; the start-up chain, the bridge and both_side_ok moved to MainBridgeBoth.v). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit StartupRegenBoth PlanRegen MainRenum
  RegsEqv0 SrzEqv MainExport MainFactsBoth MainRegen.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import AcctCore TopLevelGen.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.simple_decompress.lib Require Import TopLevel.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition BMAIN : Z := 0x8262c.           (* [comment removed for export] *)
Definition BRA : Z := 0xbadb8.             (* [comment removed for export] *)
Definition BGP : Z := 0x10800.             (* [comment removed for export] *)
Definition BTP : Z := 0x6072b0.            (* [comment removed for export] *)
Definition BIMG_LO : Z := 0x10000.         (* [comment removed for export] *)
Definition BIMG_HI : Z := 0x629000.
Definition ACEIL : Z := 0x7fff7f800000.    (* [comment removed for export] *)
Definition KHIGH : Z := 0x10007fff8000.    (* [comment removed for export] *)
Definition ASHOFF : Z := 0x7fff8000.       (* [comment removed for export] *)
Definition ABAND_LO : Z := 0x7fff7000.     (* [comment removed for export] *)
Definition ABAND_LEN : Z := 0x100000001000.
Definition V_VMBRK : nat := 452.           (* [comment removed for export] *)

(* LPS 727298f3: the main entry's facts per CONFIG_RSEQ value [r] and hand-off [w]: the recorded ones
   (MainFactsBoth), remade from the computed main-entry state ([stS1 r] / [stS2 r], StartupRegenBoth) by
   MainRegen's rule, computed in the build.  The start-up run numbers its fresh variables by the probe-read
   map [bp2] (StartupRegenBoth); the remade facts keep the recorded numbering. *)
Definition BMW (w : bool) : list mfact := both_mem_facts ++ (if w then both_mem_facts_w1 else both_mem_facts_w2).
Definition BPW (w : bool) : list pfact := both_pure_facts ++ (if w then both_pure_facts_w1 else both_pure_facts_w2).
Definition rmf (hs : acs) (l : list mfact) : list mfact := remake_facts (kn hs) BIMG_LO BIMG_HI bp2 l.
Definition rpf (hs : acs) (l : list pfact) : list pfact := remake_pfacts (kn hs) bp2 l.
Definition BMF0T : list mfact := Eval vm_compute in rmf (stS1 0) (BMW true).
Definition BMF1T : list mfact := Eval vm_compute in rmf (stS1 1) (BMW true).
Definition BMF0F : list mfact := Eval vm_compute in rmf (stS2 0) (BMW false).
Definition BMF1F : list mfact := Eval vm_compute in rmf (stS2 1) (BMW false).
Definition BPF0T : list pfact := Eval vm_compute in rpf (stS1 0) (BPW true).
Definition BPF1T : list pfact := Eval vm_compute in rpf (stS1 1) (BPW true).
Definition BPF0F : list pfact := Eval vm_compute in rpf (stS2 0) (BPW false).
Definition BPF1F : list pfact := Eval vm_compute in rpf (stS2 1) (BPW false).
Definition bmf (r : Z) (w : bool) : list mfact :=
  if w then (if Z.eqb r 1 then BMF1T else BMF0T) else (if Z.eqb r 1 then BMF1F else BMF0F).
Definition bpf (r : Z) (w : bool) : list pfact :=
  if w then (if Z.eqb r 1 then BPF1T else BPF0T) else (if Z.eqb r 1 then BPF1F else BPF0F).

(* the recorded lists as the main-phase proofs read them (MainRegen's [kept_m] / [kept_p]): a recorded fact
   every remade list still holds keeps its place, any other is replaced in place by a fact true of every
   memory *)
Definition BMKN : list mfact := Eval vm_compute in map (kept_m [BMF0T; BMF1T; BMF0F; BMF1F]) both_mem_facts.
Definition BMKN1 : list mfact := Eval vm_compute in map (kept_m [BMF0T; BMF1T]) both_mem_facts_w1.
Definition BMKN2 : list mfact := Eval vm_compute in map (kept_m [BMF0F; BMF1F]) both_mem_facts_w2.
Definition BMKNW (w : bool) : list mfact := if w then BMKN1 else BMKN2.
Definition BPKN : list pfact := Eval vm_compute in map (kept_p [BPF0T; BPF1T; BPF0F; BPF1F]) both_pure_facts.
Lemma BMKN_eq : BMKN = map (kept_m [BMF0T; BMF1T; BMF0F; BMF1F]) both_mem_facts. Proof. vm_compute. reflexivity. Qed.
Lemma BMKN1_eq : BMKN1 = map (kept_m [BMF0T; BMF1T]) both_mem_facts_w1. Proof. vm_compute. reflexivity. Qed.
Lemma BMKN2_eq : BMKN2 = map (kept_m [BMF0F; BMF1F]) both_mem_facts_w2. Proof. vm_compute. reflexivity. Qed.
Lemma BPKN_eq : BPKN = map (kept_p [BPF0T; BPF1T; BPF0F; BPF1F]) both_pure_facts. Proof. vm_compute. reflexivity. Qed.

(* what a main-phase proof reads off [bmain_at]'s facts *)
Lemma keep_facts : forall segs V m r w,
  Forall (mfact_ok segs V m) (bmf r w) -> Forall (pfact_ok V) (bpf r w) ->
  Forall (mfact_ok segs V m) BMKN /\ Forall (mfact_ok segs V m) (BMKNW w) /\ Forall (pfact_ok V) BPKN.
Proof.
  intros segs V m r w HM HP.
  assert (IM : In (bmf r w) [BMF0T; BMF1T; BMF0F; BMF1F])
    by (unfold bmf; destruct w, (Z.eqb r 1); cbn [In]; repeat (first [left; reflexivity | right])).
  assert (IP : In (bpf r w) [BPF0T; BPF1T; BPF0F; BPF1F])
    by (unfold bpf; destruct w, (Z.eqb r 1); cbn [In]; repeat (first [left; reflexivity | right])).
  assert (IW : In (bmf r w) (if w then [BMF0T; BMF1T] else [BMF0F; BMF1F]))
    by (unfold bmf; destruct w, (Z.eqb r 1); cbn [In]; repeat (first [left; reflexivity | right])).
  split; [rewrite BMKN_eq; exact (kept_m_ok segs V m _ _ both_mem_facts IM HM)|].
  split; [|rewrite BPKN_eq; exact (kept_p_ok V _ _ both_pure_facts IP HP)].
  unfold BMKNW. destruct w; [rewrite BMKN1_eq | rewrite BMKN2_eq]; exact (kept_m_ok segs V m _ _ _ IW HM).
Qed.

(* the reserved-and-mapped total the computed states carry (the vDSO pair and the bigger head) *)
Definition BTOTSZ : Z := Eval vm_compute in
  Z.max (Z.max (a_totsz (stS1 0)) (a_totsz (stS1 1))) (Z.max (a_totsz (stS2 0)) (a_totsz (stS2 1))).
(* the stack window below sp the start state states (AsanPlanCore's [KWr (SA e_sp0 (-6144513)) (ELit 6144513)]) *)
Definition STKA : zexp := ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-6144513)).

(* the argv pointer cells as the start state states them (AsanPlanCore: [KWord (SA e_sp0 8) 8 (e_str0 r)] and
   [kw_argv1 (e_argv1w r)]), in the facts' terms; the bridge checks them against the computed main-entry state *)
Definition zof0 (e : expr) : zexp := match zexp_of e with Some z => z | None => ZLit 0 end.
Definition bargv (r : Z) : list mfact :=
  [MRo (mkaddr (zof0 e_sp0) 8) 8 (zof0 (e_str0 r)); MRo (mkaddr (zof0 e_sp0) 16) 8 (zof0 (e_argv1w r))].
Lemma zv_sp0 : forall V, zv V (zof0 e_sp0) = 32768 * V 0%nat + 16 * V 6%nat + 4096 * V 10%nat.
Proof.
  intros V. match goal with |- context [zof0 ?e] => let x := eval vm_compute in (zof0 e) in change (zof0 e) with x end.
  cbn [zv]. lia.
Qed.
Lemma zv_str0 : forall V r, 0 <= r <= 1 ->
  zv V (zof0 (e_str0 r)) = 32768 * V 0%nat + 16 * V 6%nat + 4096 * V 10%nat + 8 * V 1%nat + 8 * V 2%nat
                           + 8 * V 11%nat + V 4%nat + 472 + 32 * r.
Proof.
  intros V r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia;
    match goal with |- context [zof0 ?e] => let x := eval vm_compute in (zof0 e) in change (zof0 e) with x end;
    cbn [zv]; lia.
Qed.
Lemma zv_argv1 : forall V r, 0 <= r <= 1 -> 2 <= V 1%nat < 2 ^ 64 ->
  zv V (zof0 (e_argv1w r)) = 32768 * V 0%nat + 16 * V 6%nat + 4096 * V 10%nat + 8 * V 1%nat + 8 * V 2%nat
                             + 8 * V 11%nat + V 4%nat + 472 + 32 * r + V 3%nat + 1.
Proof.
  intros V r Hr Ha. assert (r = 0 \/ r = 1) as [-> | ->] by lia;
    match goal with |- context [zof0 ?e] => let x := eval vm_compute in (zof0 e) in change (zof0 e) with x end;
    cbn [zv]; unfold MainExport.two64; rewrite (Z.mod_small 1 (2 ^ 64)) by lia; rewrite (Z.mod_small (V 1%nat) (2 ^ 64)) by lia;
    rewrite (proj2 (Z.ltb_lt 1 (V 1%nat))) by lia; cbn [Z.b2z]; lia.
Qed.

Lemma bsegs_BSEGS : BSEGS = bsegs. Proof. reflexivity. Qed.
Lemma bph_BPH : BPH = b_phdrs. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Record bmodel (V : nat -> Z) (sp : word) (fs : Fs.Fs) (mo : Model) : Prop := BMODEL {
  bm_halted   : m_halted mo = None;
  bm_reader   : m_channel_reader mo = true;   (* 08b1429: check_write/check_writev branch on the channel reader (SIGPIPE arm) *)
  bm_fds      : m_fds mo = [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
                            (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))];
  bm_fs       : m_fs mo = fs;
  (* LPS 727298f3: the run's reservations are the image's and the vDSO pair, above the ASan
     shadow ([AsanPlanSound.co_res]) *)
  bm_reserved : exists rx : list (word * word),
                  vm_reserved (m_vmmaps mo) = segments_reserved bsegs ++ rx
                  /\ Forall (resx_entry_ok BOTH) rx /\ (length rx <= n_resx BOTH)%nat
                  /\ sum_sizes rx <= resx_bytes BOTH;
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
  bm_totsz    : ivs_sum (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) <= BTOTSZ;
  (* [comment removed for export] *)
  bm_nonlazy  : nonlazy_bytes mo <= both_eager;
  bm_abytes   : ivz_bytes (allow_of ASHOFF V both_vis) <= both_abytes;
  bm_budget   : nonlazy_bytes mo + ivz_bytes (allow_of ASHOFF V both_vis) <= target_alloc_limit;
  bm_allow_wf : ivz_wf (allow_of ASHOFF V both_vis);
  bm_mat_nodup : List.NoDup (m_vm_materialized mo);
  bm_mat      : forall p, In p (m_vm_materialized mo) ->
                  bv_unsigned p mod 4096 = 0 /\ page_in_ranges p (m_vm_lazy mo) = true /\ aallowed (allow_of ASHOFF V both_vis) p;
  (* LPS 727298f3: the mappings miss the reserved ledger, the vDSO pair included ([AsanPlanSound.co_mres]) *)
  bm_mres     : Forall (fun iv => Forall (iv_disjoint iv) (vm_reserved (m_vmmaps mo))) (vm_maps (m_vmmaps mo))
}.

(* LPS 727298f3: Linux's stack block.  The arch_align_stack pad [Wpad] sits between the AT_RANDOM
   bytes and argv[0]; the string area runs from [STR0_of] (argv[0]) to the stack VMA's end
   ([ed_top]).  [hidden_arg] is [AsanInit.argH0]'s two ranges in the entry's own terms. *)
Definition Wpad (en : ExecEntry) (inp : ProcInput) : Z :=
  Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) (en_sp en) (ed_top (en_draw en)) (in_argv inp) (in_envp inp) (in_execfn inp)).
Definition STR0_of (en : ExecEntry) (inp : ProcInput) : Z :=
  bv_unsigned (en_sp en) + Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)) + Wpad en inp.

(* [comment removed for export] *)
Definition hidden_arg (en : ExecEntry) (inp : ProcInput) (a : Z) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
  (usp + 8 * argc + 16 <= a < usp + 8 * argc + 8 * envc + 24)
  \/ (STR0_of en inp <= a < bv_unsigned (ed_top (en_draw en))).

(* LPS 727298f3: the argv pointer cells, in the launch's terms: argv[0] points at the string area's start
   [STR0_of], which is the launch's string base (the stack VMA's end less the strings and their 8-byte end
   marker, InitMem.str_base), and argv[1], when there is one, right after argv[0]'s string *)
Definition argv_cells (en : ExecEntry) (inp : ProcInput) (m : word -> option byte) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let sb := bv_unsigned (ed_top (en_draw en)) - 8 - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp)) in
  STR0_of en inp = sb
  /\ bytes_at bsegs m (usp + 8) (word_to_le_bytes 8 (Z_to_bv 64 sb))
  /\ (2 <= Z.of_nat (length (in_argv inp)) ->
      bytes_at bsegs m (usp + 16) (word_to_le_bytes 8 (Z_to_bv 64 (sb + Z.of_nat (length (nth 0 (in_argv inp) [])) + 1)))).

(* [comment removed for export] *)
Definition bshadow (a : Z) : Prop := (0x7fff7000 <= a < 0x8fff7000) \/ (0x2008fff7000 <= a < 0x10007fff8000).
Definition BSHADOWS : list (Z * Z) := [(0x7fff7000, 0x8fff7000); (0x2008fff7000, 0x10007fff8000)].
Definition bshadow_vis (V : nat -> Z) (a : Z) : Prop :=
  exists bn, In bn both_vis_app /\ ASHOFF + zv V (fst bn) / 8 <= a < ASHOFF + (zv V (fst bn) + zv V (snd bn)) / 8.
(* [comment removed for export] *)
Definition bshadow0 (V : nat -> Z) (m : word -> option byte) : Prop :=
  forall a, bshadow a -> ~ bshadow_vis V a -> m (wa a) = Some (Z_to_bv 8 0).

(* the run's CONFIG_RSEQ flag as the plan's 0 or 1 (model commit 0c15dd4) *)
Definition RZ_of (inp : ProcInput) : Z := rseq_z (kb_rseq (in_kernel inp)).

Definition bmain_at (en : ExecEntry) (inp : ProcInput) (ms : machine_state) (mo : Model) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
  exists (w : bool) (V : nat -> Z) (m : word -> option byte),
    ms = MS (mkR (Z_to_bv 64 BRA) (Z_to_bv 64 (usp - 48)) (Z_to_bv 64 BGP) (Z_to_bv 64 BTP)
                 (Z_to_bv 64 (V 1128%nat)) (Z_to_bv 64 (V 1129%nat)) (Z_to_bv 64 (V 1130%nat))
                 (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (usp + 8))
                 (Z_to_bv 64 (usp + 8 * argc + 16)) (Z_to_bv 64 0x6000000000000000)
                 (Z_to_bv 64 (V 1131%nat)) (Z_to_bv 64 (V 1132%nat)) (Z_to_bv 64 (V 1133%nat)) (Z_to_bv 64 (V 1134%nat))
                 (Z_to_bv 64 BMAIN) (Z_to_bv 64 (usp + 8 * argc + 16))
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 (V 1135%nat)) (Z_to_bv 64 (V 1136%nat)) (Z_to_bv 64 (V 1137%nat)) (Z_to_bv 64 (V 1138%nat)))
            bvmap_empty (Z_to_bv 64 BMAIN) (Z_to_bv 32 0) None m (seg_rom bsegs)
    /\ (forall n, 0 <= V n < 2 ^ 64)
    (* [comment removed for export] *)
    /\ (V 0%nat = usp / 32768 /\ V 6%nat = usp mod 4096 / 16 /\ V 10%nat = usp mod 32768 / 4096
        /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp
        /\ V 1%nat = argc /\ V 2%nat = envc
        /\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) [])) /\ V 7%nat = Z.of_nat (length (nth 1 (in_argv inp) []))
        /\ V 4%nat = Wpad en inp /\ V 5%nat = bv_unsigned (en_brk en) / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
        /\ V 9%nat = bv_unsigned (in_hwcap inp))
    /\ Forall (mfact_ok bsegs V m) (bmf (RZ_of inp) w)
    /\ Forall (pfact_ok V) (bpf (RZ_of inp) w)
    /\ mem_inv bsegs m
    (* LPS 727298f3: the stack every launch zero-maps below the entry sp ([InitMem.im_stack_depth]) *)
    /\ stk bsegs m (usp - 6144513) usp
    /\ (forall a, hidden_arg en inp a ->
          m (wa a) = wrap_mem inp (en_mmap_base en) b_phdrs (Z_to_bv 64 (Z.of_N b_init_pc)) (en_sp en) (en_draw en) (wa a))
    /\ argv_cells en inp m
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
