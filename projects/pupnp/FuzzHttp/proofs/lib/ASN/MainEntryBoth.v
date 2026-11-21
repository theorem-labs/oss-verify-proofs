(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the stack window below sp; the launch's input, mmap base and entry draw; the CONFIG_RSEQ value; the launch's reader of the standard channels). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import
  PropExec ShapeAlg SpinAlg AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit BothStartup StartupHSBoth StartupHS2Both BothBoot
  RegsEqv0 SrzEqv MainExport MainRename MainFactsBoth.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require PlanRegen AsanNodesAux.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require RegsEquiv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import B0Img.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Notation nonlazy_bytes := eager_used (only parsing).

Definition BMAIN : Z := 0x8605c.
Definition BRA : Z := 0x94fe8.
Definition BGP : Z := 0x10800.
Definition BTP : Z := 0x5e75b0.
Definition BIMG_LO : Z := 0x10000.
Definition BIMG_HI : Z := 0x609000.
Definition ACEIL : Z := 0x7fff7f800000.
Definition KHIGH : Z := 0x10007fff8000.
Definition ASHOFF : Z := 0x7fff8000.
Definition ABAND_LO : Z := 0x7fff7000.
Definition ABAND_LEN : Z := 0x100000001000.
(* the main phase's brk variable, in the main phase's (recorded) numbering *)
Definition V_VMBRK : nat := 452.

Lemma bsegs_BSEGS : BSEGS = bsegs. Proof. reflexivity. Qed.
Lemma bph_BPH : BPH = b_phdrs. Proof. reflexivity. Qed.

Record bmodel (V : nat -> Z) (sp : word) (fs : Fs.Fs) (mo : Model) : Prop := BMODEL {
  bm_halted   : m_halted mo = None;
  bm_fds      : m_fds mo = [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
                            (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))];
  bm_fs       : m_fs mo = fs;
  (* the image's reservations and the launch's (the vDSO pair), as [cs_ok]'s [co_res] *)
  bm_reserved : exists rx : list (word * word),
                  vm_reserved (m_vmmaps mo) = segments_reserved bsegs ++ rx
                  /\ Forall (resx_entry_ok BOTH) rx /\ (length rx <= n_resx BOTH)%nat /\ sum_sizes rx <= resx_bytes BOTH;
  bm_mres     : Forall (fun iv => Forall (iv_disjoint iv) (vm_reserved (m_vmmaps mo))) (vm_maps (m_vmmaps mo));
  bm_limit    : vm_limit (m_vmmaps mo) = target_alloc_limit;
  bm_brk      : vm_brk (m_vmmaps mo) = Z_to_bv 64 (V V_VMBRK);
  bm_start_brk : bv_unsigned (vm_start_brk (m_vmmaps mo)) <= V V_VMBRK;

  bm_top      : vm_init_sp (m_vmmaps mo) = sp;
  bm_usp      : 0x7fff80000000 <= bv_unsigned sp /\ bv_unsigned sp <= 0x800000000000 /\ bv_unsigned sp mod 16 = 0;

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
  bm_totsz    : ivs_sum (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) <= both_totsz;

  bm_nonlazy  : nonlazy_bytes mo <= both_eager;
  bm_abytes   : ivz_bytes (allow_of ASHOFF V both_vis) <= both_abytes;
  bm_budget   : nonlazy_bytes mo + ivz_bytes (allow_of ASHOFF V both_vis) <= target_alloc_limit;
  bm_allow_wf : ivz_wf (allow_of ASHOFF V both_vis);
  bm_mat_nodup : List.NoDup (m_vm_materialized mo);
  bm_mat      : forall p, In p (m_vm_materialized mo) ->
                  bv_unsigned p mod 4096 = 0 /\ page_in_ranges p (m_vm_lazy mo) = true /\ aallowed (allow_of ASHOFF V both_vis) p;

  bm_lzwf     : Forall (lzwf (vm_maps (m_vmmaps mo))) (m_vm_lazy mo);
  bm_wf       : BackingAlgebra.model_ivs_wf mo;
  bm_seps     : APS.seps (vm_maps (m_vmmaps mo));
  bm_tid      : m_tid mo <> None /\ (forall t, m_tid mo = Some t -> 0 < bv_unsigned t < PID_MAX_ENVELOPE);

  bm_noaccess_pos : Forall (fun iv => 0 < bv_unsigned (snd iv)) (vm_noaccess (m_vmmaps mo));
  (* LPS 727298f3: the standard channels have a reader (cs_ok's co_rdr) *)
  bm_rdr      : m_channel_reader mo = true
}.

(* V 4: the [arch_align_stack] pad between the AT_RANDOM bytes and argv[0] (AsanInit's W) *)
Definition Wblk (en : ExecEntry) (inp : ProcInput) : Z :=
  Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) (en_sp en) (ed_top (en_draw en))
                          (in_argv inp) (in_envp inp) (in_execfn inp)).

(* argv[0]'s first byte, sp + C + W (AsanInit's STR0) *)
Definition str0 (en : ExecEntry) (inp : ProcInput) : Z :=
  bv_unsigned (en_sp en)
  + Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
  + Wblk en inp.

(* the envp pointer array with its NULL, and the string area from argv[0] to the stack VMA's end
   (AsanInit's argH0) *)
Definition hidden_arg (en : ExecEntry) (inp : ProcInput) (a : Z) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
  (usp + 8 * argc + 16 <= a < usp + 8 * argc + 8 * envc + 24)
  \/ (str0 en inp <= a < bv_unsigned (ed_top (en_draw en))).

Definition bshadow (a : Z) : Prop := (0x7fff7000 <= a < 0x8fff7000) \/ (0x2008fff7000 <= a < 0x10007fff8000).
Definition BSHADOWS : list (Z * Z) := [(0x7fff7000, 0x8fff7000); (0x2008fff7000, 0x10007fff8000)].
Definition bshadow_vis (V : nat -> Z) (a : Z) : Prop :=
  exists bn, In bn both_vis_app /\ ASHOFF + zv V (fst bn) / 8 <= a < ASHOFF + (zv V (fst bn) + zv V (snd bn)) / 8.

Definition bshadow0 (V : nat -> Z) (m : word -> option byte) : Prop :=
  forall a, bshadow a -> ~ bshadow_vis V a -> m (wa a) = Some (Z_to_bv 8 0).

Definition both_mem_facts_w (w : bool) : list mfact := if w then both_mem_facts_w1 else both_mem_facts_w2.
Definition both_pure_facts_w (w : bool) : list pfact := if w then both_pure_facts_w1 else both_pure_facts_w2.

Definition b0_H0 (V : nat -> Z) (mo : Model) (a : word) : bool :=
  (page_in_ranges (page_base a) (m_vm_lazy mo) && negb (page_allowedb (allow_of ASHOFF V both_vis) (page_base a)))%bool.

(* the register file the main phase starts from, in the LPS 727298f3 run's numbering; [bmain_at]
   names its variables in the main phase's numbering ([vgB]) *)
Definition main_regs : list expr := Eval vm_compute in s_regs (a_ss bS21_0).

Definition bmain_at (en : ExecEntry) (inp : ProcInput) (ms : machine_state) (mo : Model) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
  exists (w : bool) (V : nat -> Z) (m : word -> option byte),
    ms = MS (mkR (Z_to_bv 64 BRA) (Z_to_bv 64 (usp - 48)) (Z_to_bv 64 BGP) (Z_to_bv 64 BTP)
                 (Z_to_bv 64 (V 1817%nat)) (Z_to_bv 64 (V 1818%nat)) (Z_to_bv 64 (V 1819%nat))
                 (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (usp + 8))
                 (Z_to_bv 64 (usp + 8 * argc + 16)) (Z_to_bv 64 0x6000000000000000)
                 (Z_to_bv 64 (V 1820%nat)) (Z_to_bv 64 (V 1821%nat)) (Z_to_bv 64 (V 1822%nat)) (Z_to_bv 64 (V 1823%nat))
                 (Z_to_bv 64 BMAIN) (Z_to_bv 64 (usp + 8 * argc + 16))
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 (V 1824%nat)) (Z_to_bv 64 (V 1825%nat)) (Z_to_bv 64 (V 1826%nat)) (Z_to_bv 64 (V 1827%nat)))
            bvmap_empty (Z_to_bv 64 BMAIN) (Z_to_bv 32 0) None m (seg_rom bsegs)
    /\ (forall n, 0 <= V n < 2 ^ 64)

    /\ (V 0%nat = usp / 32768 /\ V 6%nat = usp mod 4096 / 16 /\ V 10%nat = usp mod 32768 / 4096
        /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp
        /\ V 1%nat = argc /\ V 2%nat = envc
        /\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) [])) /\ V 7%nat = Z.of_nat (length (nth 1 (in_argv inp) []))
        /\ V 4%nat = Wblk en inp /\ V 5%nat = bv_unsigned (en_brk en) / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
        /\ V 9%nat = bv_unsigned (in_hwcap inp))
    /\ Forall (mfact_ok bsegs V m) (both_mem_facts ++ both_mem_facts_w w)
    /\ Forall (pfact_ok V) (both_pure_facts ++ both_pure_facts_w w)
    /\ mem_inv bsegs m
    /\ stk bsegs m (usp - 6144512) usp
    /\ bytes_at bsegs m (usp + 8) (le8 (Z_to_bv 64 (str0 en inp)))
    /\ bytes_at bsegs m (usp + 16)
         (le8 (Z_to_bv 64 (Z.b2z (1 <? argc) * (str0 en inp + Z.of_nat (length (nth 0 (in_argv inp) [])) + 1))))
    /\ (forall a, hidden_arg en inp a ->
          m (wa a) = wrap_mem inp (en_mmap_base en) b_phdrs (Z_to_bv 64 (Z.of_N b_init_pc)) (en_sp en) (en_draw en) (wa a))
    /\ bshadow0 V m

    /\ Forall (mfact_ok bsegs V (mrestrict (b0_H0 V mo) m)) (both_mem_facts ++ both_mem_facts_w w)
    /\ bmodel V (en_sp en) (in_fs inp) mo.

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

(* ------------------------------------------------------------------------- *)
(* The launch's own cells at the main phase's entry                           *)
(* ------------------------------------------------------------------------- *)

(* the entry stack pointer as the export reads it ([zexp_of e_sp0]) *)
Definition ZSP : zexp := ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))).

(* argv[0]'s and argv[1]'s pointer words and the zero window below sp, in the LPS 727298f3 run's
   numbering at CONFIG_RSEQ value [r] (their values name the launch layout, which depends on [r]) *)
Definition alaunch_facts (r : Z) : list mfact :=
  match zexp_of (e_str0 r), zexp_of (e_argv1w r) with
  | Some v1, Some v2 =>
      [MRo (ZAdd ZSP (ZLit 8)) 8 v1; MRo (ZAdd ZSP (ZLit 16)) 8 v2; MWr (ZAdd ZSP (ZLit (-6144513))) 6144513]
  | _, _ => []
  end.

Lemma alaunch_ok : forall E (FULL : word -> option byte) r v1 v2,
  zexp_of (e_str0 r) = Some v1 -> zexp_of (e_argv1w r) = Some v2 ->
  Forall (mfact_ok bsegs (uev E) FULL)
         [MRo (ZAdd ZSP (ZLit 8)) 8 v1; MRo (ZAdd ZSP (ZLit 16)) 8 v2; MWr (ZAdd ZSP (ZLit (-6144513))) 6144513] ->
  bytes_at bsegs FULL (zv (uev E) ZSP + 8) (le8 (edenot E (e_str0 r)))
  /\ bytes_at bsegs FULL (zv (uev E) ZSP + 16) (le8 (edenot E (e_argv1w r)))
  /\ wr_at bsegs FULL (zv (uev E) ZSP - 6144513) 6144513.
Proof.
  intros E FULL r v1 v2 H1 H2 HF.
  pose proof (Forall_inv HF) as F1. pose proof (Forall_inv (Forall_inv_tail HF)) as F2.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HF))) as F3.
  cbn [mfact_ok zv] in F1, F2, F3.
  rewrite (zexp_of_sound E _ _ H1) in F1. rewrite (zexp_of_sound E _ _ H2) in F2.
  split; [exact F1|]. split; [exact F2|].
  replace (zv (uev E) ZSP - 6144513) with (zv (uev E) ZSP + -6144513) by lia. exact F3.
Qed.

(* ------------------------------------------------------------------------- *)
(* The main hand-off states' side conditions, each checked by computation    *)
(* ------------------------------------------------------------------------- *)

Definition bridge_ok (r : Z) (w : bool) (hs : acs) : Prop :=
  s_regs (a_ss hs) = main_regs /\ pc hs = BMAIN /\ a_fd hs = FdStd /\ a_brk hs = EVar (vgB V_VMBRK)
  /\ a_tidset hs = true
  /\ forallb (fun f => mjust (kn hs) BIMG_LO BIMG_HI (mfsh vgB f)) (both_mem_facts ++ both_mem_facts_w w) = true
  /\ forallb (fun f => pjust (kn hs) (pfsh vgB f)) (both_pure_facts ++ both_pure_facts_w w) = true
  /\ vis_match (var_ranges (kn hs)) (a_vis hs) (map (bnsh vgB) both_vis_app) = true
  /\ vis_match (var_ranges (kn hs)) (a_ghost hs) (map (bnsh vgB) both_ghost) = true
  /\ ledger_xmatch (var_ranges (kn hs)) (a_maps hs) (map (lesh vgB) both_ledger) = true
  /\ Nat.eqb (length (alaunch_facts r)) 3 = true
  /\ forallb (mjustify (kn hs) (var_ranges (kn hs)) BIMG_LO BIMG_HI) (alaunch_facts r) = true
  /\ (a_totsz hs <=? both_totsz) = true /\ (a_eager hs <=? both_eager) = true /\ (a_abytes hs <=? both_abytes) = true.

Lemma bridge_ok_10 : bridge_ok 0 true bS21_0.
Proof. unfold bridge_ok. repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity. Qed.
Lemma bridge_ok_20 : bridge_ok 0 false bS22_0.
Proof. unfold bridge_ok. repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity. Qed.
Lemma bridge_ok_11 : bridge_ok 1 true bS21_1.
Proof. unfold bridge_ok. repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity. Qed.
Lemma bridge_ok_21 : bridge_ok 1 false bS22_1.
Proof. unfold bridge_ok. repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity. Qed.

Section Bridge.
  Variable sp brk0 mbase : word.
  Variable rdraw : EntryDraw.
  Variable inp : ProcInput.
  Hypothesis HL : launch_ok BSEGS BOTH BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp.

  Definition en0 : ExecEntry := mkEntry sp brk0 mbase rdraw.

  #[local] Abbreviation SINV := (SINV0 BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp).
  #[local] Abbreviation argH := (argH0 sp rdraw inp).
  #[local] Abbreviation E0a := (AsanInit.E0 sp rdraw brk0 inp).
  #[local] Abbreviation LIM := AsanInit.LIMIT.
  #[local] Abbreviation RZ := (rseq_z (kb_rseq (in_kernel inp))).

  Let AH := argH0_high_l BSEGS BOTH BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp HL.

  Lemma sinv_usp : forall E M, SINV E M -> uE E e_sp0 = bv_unsigned sp.
  Proof.
    intros E M [HE _].
    transitivity (uE E0a e_sp0); [| exact (u_e_sp0_l BSEGS BOTH BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp HL)].
    unfold e_sp0, uE. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot].
    rewrite !HE by (unfold NX0, V_S1, V_S2, V_SP; lia). reflexivity.
  Qed.

  (* a main hand-off state at CONFIG_RSEQ value [r] whose side conditions hold gives the main
     phase's entry: its valuation is the run's, read in the main phase's numbering ([vgB]) *)
  Theorem bmain_bridge_w : forall (r : Z) (w : bool) (hs : acs), RZ = r -> bridge_ok r w hs ->
    forall E R FULL mo,
    cs_ok BSEGS BOTH LIM SINV argH (in_fs inp) E hs R FULL mo ->
    exists ms, cfg_eqv (cfg_of BSEGS R (pc hs) FULL mo) (mkCfg ms mo) /\ bmain_at en0 inp ms mo.
  Proof.
    intros r w hs ERZ BOK E R FULL mo HC.
    destruct BOK as (Hregs & Hpc & Hfd & Hbrk0 & Htids & MJ & PJ & VJa & VJg & LJ & LFN & LFJ & Ct & Ce & Ca).
    apply Z.leb_le in Ct. apply Z.leb_le in Ce. apply Z.leb_le in Ca.
    rewrite Hpc.
    set (V := fun n => uev E (vgB n)).

    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as HSINV. pose proof HSINV as [Hev Hhid].
    pose proof (sinv_usp E FULL HSINV) as USP.
    pose proof (main_pins_l BSEGS BOTH BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp HL)
      as (U0 & U6 & U10 & U1 & U2 & U3 & U7 & U4 & U5 & U8 & U9).
    pose proof (main_launch_l BSEGS BOTH BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp HL)
      as (LO & HI & Hal & AC & EC & UST0 & UST1).
    unfold APS.uE in U0, U6, U10, U1, U2, U3, U7, U4, U5, U8, U9.
    cbn [edenot] in U0, U6, U10, U1, U2, U3, U7, U4, U5, U8, U9.
    (* below the run's first fresh variable the two numberings agree *)
    assert (VG0 : forall n, (n < 11)%nat -> vgB n = n).
    { intros n Hn. unfold vgB, PlanRegen.tshift, VTBL_B. cbn [PlanRegen.tbl_d].
      destruct (Nat.leb 11 n) eqn:E11; [apply Nat.leb_le in E11; lia | lia]. }
    assert (PIN : forall n z, (n < 11)%nat -> bv_unsigned (ev E0a n) = z -> uev E n = z /\ V n = z).
    { intros n z Hn Hz.
      assert (Ev : uev E n = z) by (unfold uev; rewrite (Hev n) by (unfold NX0; lia); exact Hz).
      split; [exact Ev|]. unfold V. cbv beta. rewrite (VG0 n Hn). exact Ev. }
    destruct (PIN 0%nat _ ltac:(lia) U0) as (Q0 & P0). destruct (PIN 6%nat _ ltac:(lia) U6) as (Q6 & P6).
    destruct (PIN 10%nat _ ltac:(lia) U10) as (Q10 & P10). destruct (PIN 1%nat _ ltac:(lia) U1) as (Q1 & P1).
    destruct (PIN 2%nat _ ltac:(lia) U2) as (Q2 & P2). destruct (PIN 3%nat _ ltac:(lia) U3) as (Q3 & P3).
    destruct (PIN 7%nat _ ltac:(lia) U7) as (Q7 & P7). destruct (PIN 4%nat _ ltac:(lia) U4) as (Q4 & P4).
    destruct (PIN 5%nat _ ltac:(lia) U5) as (Q5 & P5). destruct (PIN 8%nat _ ltac:(lia) U8) as (Q8 & P8).
    destruct (PIN 9%nat _ ltac:(lia) U9) as (Q9 & P9).
    clear U0 U6 U10 U1 U2 U3 U7 U4 U5 U8 U9.
    assert (PSP : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = bv_unsigned sp).
    { rewrite P0, P6, P10. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (QSP : 32768 * uev E 0%nat + 4096 * uev E 10%nat + 16 * uev E 6%nat = bv_unsigned sp) by lia.
    assert (VR : forall n, 0 <= V n < 2 ^ 64) by (intros n; unfold V; apply uev_range).

    pose proof (co_top _ _ _ _ _ _ _ _ _ _ _ HC) as TOP. rewrite USP in TOP.
    assert (ATOP : atop mo = bv_unsigned sp - 8388608) by (unfold atop; rewrite TOP; reflexivity).

    assert (HIDrom : forall a, APS.hid BOTH argH E hs mo a = true -> seg_rom bsegs a = None).
    { intros a Ha. apply (APS.seg_rom_off_hull BSEGS BOTH both_in_hull).
      unfold APS.hid in Ha. apply orb_prop in Ha as [Ha|Ha].
      - pose proof (AH E a Ha) as Hc. unfold APS.in_hull. cbn [img_lo img_hi BOTH]. unfold CEIL in Hc.
        apply andb_false_iff. right. apply Z.ltb_ge. lia.
      - apply negb_true_iff in Ha. unfold APS.vis in Ha. apply orb_false_iff in Ha as [Ha _]. apply orb_false_iff in Ha as [Ha _]. exact Ha. }
    assert (HULLvis : forall a, BIMG_LO <= bv_unsigned a < BIMG_HI -> APS.hid BOTH argH E hs mo a = false).
    { intros a Ha. apply (APS.hid_hull BOTH both_hull_ok argH AH). unfold APS.in_hull. cbn [img_lo img_hi BOTH]. unfold BIMG_LO, BIMG_HI in Ha.
      apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }

    (* the launch's cells: argv[0]'s and argv[1]'s pointer words and the zero window below sp *)
    assert (LC : bytes_at bsegs FULL (bv_unsigned sp + 8) (le8 (Z_to_bv 64 (str0 en0 inp)))
                 /\ bytes_at bsegs FULL (bv_unsigned sp + 16)
                      (le8 (Z_to_bv 64 (Z.b2z (1 <? Z.of_nat (length (in_argv inp)))
                                        * (str0 en0 inp + Z.of_nat (length (nth 0 (in_argv inp) [])) + 1))))
                 /\ wr_at bsegs FULL (bv_unsigned sp - 6144513) 6144513).
    { assert (R01 : r = 0 \/ r = 1).
      { rewrite <- ERZ. unfold rseq_z. destruct (kb_rseq (in_kernel inp)); [right|left]; reflexivity. }
      assert (AG : forall e, AsanNodesAux.nb_lt NX0 e = true -> edenot E e = edenot E0a e).
      { intros e He. apply (AsanNodesAux.edenot_ev_agree NX0 E E0a e He). intros n Hn. exact (Hev n Hn). }
      assert (S0 : edenot E (e_str0 r) = Z_to_bv 64 (str0 en0 inp)).
      { rewrite AG by (destruct R01 as [-> | ->]; vm_compute; reflexivity).
        rewrite <- ERZ. rewrite <- (Z_to_bv_bv_unsigned (edenot E0a (e_str0 RZ))). f_equal. exact UST0. }
      assert (S1 : edenot E (e_argv1w r)
                   = Z_to_bv 64 (Z.b2z (1 <? Z.of_nat (length (in_argv inp)))
                                 * (str0 en0 inp + Z.of_nat (length (nth 0 (in_argv inp) [])) + 1))).
      { rewrite AG by (destruct R01 as [-> | ->]; vm_compute; reflexivity).
        rewrite <- ERZ. rewrite <- (Z_to_bv_bv_unsigned (edenot E0a (e_argv1w RZ))). f_equal. exact UST1. }
      assert (EZ : zv (uev E) ZSP = bv_unsigned sp) by (unfold ZSP; cbn [zv]; lia).
      revert LFJ LFN. unfold alaunch_facts.
      destruct (zexp_of (e_str0 r)) as [v1|] eqn:Z1; [|intros _ LFN; cbn in LFN; discriminate LFN].
      destruct (zexp_of (e_argv1w r)) as [v2|] eqn:Z2; [|intros _ LFN; cbn in LFN; discriminate LFN].
      intros LFJ _.
      pose proof (export_sound bsegs E (APS.hid BOTH argH E hs mo) FULL (kn hs) BIMG_LO BIMG_HI
                    (co_know _ _ _ _ _ _ _ _ _ _ _ HC) HIDrom HULLvis _ [] LFJ eq_refl) as [LF _].
      destruct (alaunch_ok E FULL r v1 v2 Z1 Z2 LF) as (C1 & C2 & C3).
      rewrite EZ, S0 in C1. rewrite EZ, S1 in C2. rewrite EZ in C3.
      split; [exact C1|]. split; [exact C2| exact C3]. }

    eexists. split; cycle 1.
    {
      exists w, V, FULL. split; [reflexivity|].
      split; [exact VR|].
      split; [repeat split; assumption|].

      pose proof (export_sound_g vgB bsegs E (APS.hid BOTH argH E hs mo) FULL (kn hs) BIMG_LO BIMG_HI
                    (co_know _ _ _ _ _ _ _ _ _ _ _ HC) HIDrom HULLvis _ _ MJ PJ) as [HMF HPF].
      fold V in HMF, HPF.
      pose proof (proj1 (Forall_app _ _ _) HMF) as [HMFc _].
      pose proof (proj1 (Forall_app _ _ _) HPF) as [HPFc _].
      split; [exact HMF|]. split; [exact HPF|].

      split.
      { intros a b Hab. rewrite b_ro_addr.
        destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); [|reflexivity].
        destruct (Z.ltb_spec0 (bv_unsigned a) 0xaa000); [|reflexivity].
        exfalso. pose proof (mimg_cover bsegs V FULL both_mem_facts 0x10000 0xaa000 HMFc ltac:(vm_compute; reflexivity) (bv_unsigned a) ltac:(lia)) as X.
        unfold wa in X. rewrite Z_to_bv_bv_unsigned in X. congruence. }

      destruct LC as (LC1 & LC2 & LC3).
      split.
      { cbn [en0 en_sp].
        assert (SW : stk bsegs FULL (bv_unsigned sp - 6144513) (bv_unsigned sp)).
        { apply wr_at_stk; [replace (bv_unsigned sp - (bv_unsigned sp - 6144513)) with 6144513 by lia; exact LC3|].
          intros a Ha. apply ref_find_segment_none; [lia|]. lia. }
        exact (proj2 (stk_split bsegs FULL _ (bv_unsigned sp - 6144512) _ SW ltac:(lia))). }
      split; [cbn [en0 en_sp]; exact LC1|].
      split; [cbn [en0 en_sp]; exact LC2|].

      split.
      { intros a Ha.
        pose proof (u64_range (ed_top rdraw)) as TR.
        unfold hidden_arg, str0, Wblk in Ha. cbn [en0 en_sp en_draw en_mmap_base] in Ha |- *.
        rewrite (Hhid (wa a)); [reflexivity|].
        unfold argH0. cbv zeta. rewrite wa_unsigned by lia.
        apply orb_true_intro. destruct Ha as [Ha|Ha]; [left|right]; apply andb_true_intro; split;
          first [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }

      pose proof (var_ranges_sound BSEGS E _ (kn hs) (co_know _ _ _ _ _ _ _ _ _ _ _ HC)) as HVR.
      pose proof (vis_match_sound E _ _ _ HVR VJa) as HVISa0. pose proof (vis_match_sound E _ _ _ HVR VJg) as HVISg0.
      pose proof (vis_rel_bnsh vgB E _ _ HVISa0) as HVISa. pose proof (vis_rel_bnsh vgB E _ _ HVISg0) as HVISg.
      fold V in HVISa, HVISg.
      pose proof (Forall2_app HVISa0 HVISg0) as HVIS0. rewrite <- map_app in HVIS0.
      pose proof (ledger_den_sound E _ HVR _ _ _ LJ (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)) as HLD0.
      pose proof (proj1 (ledger_den_lesh vgB (uev E) both_ledger _) HLD0) as HLD.
      pose proof (ledger_kinds_sound E _ HVR _ _ mo LJ (co_none _ _ _ _ _ _ _ _ _ _ _ HC) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC)) as HKD0.
      pose proof (Forall_lentry_kind_ok_lesh vgB (uev E) mo both_ledger HKD0) as HKD.
      fold V in HLD, HKD.

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
        -
          unfold APS.hid. apply orb_true_intro. right. apply negb_true_iff. unfold APS.vis. rewrite Ua.
          rewrite Klz. cbn [negb].
          replace (APS.in_hull BOTH a) with false.
          2:{ symmetry. unfold APS.in_hull. cbn [img_lo img_hi BOTH]. apply andb_false_iff. right. apply Z.ltb_ge. unfold bshadow in Hsh. lia. }
          replace (atop mo <=? a) with false by (symmetry; apply Z.leb_gt; rewrite ATOP; unfold bshadow in Hsh; lia).
          cbn [orb]. replace (APS.in_allow BOTH E hs a) with false; [destruct (APS.in_ivs _ _ && _)%bool; reflexivity|].
          symmetry. unfold APS.in_allow. apply orb_false_intro.
          +
            unfold APS.in_vis. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Xp).
            apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
            destruct (Forall2_In_l _ _ _ _ HVISa Hp) as (bn & Hbn & E1 & E2 & E3). unfold APS.uE in X1, X2. rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2.
            apply (shad_clear_sound V _ both_pure_facts bn a HVRp HPFc (proj1 (forallb_forall _ _) CLRv bn Hbn) HSS). lia.
          +
            unfold APS.in_sh. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Xp).
            apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. unfold APS.sh_lo, APS.sh_hi, APS.uE in X1, X2.
            destruct (Forall2_In_l _ _ _ _ HVISa Hp) as (bn & Hbn & E1 & E2 & E3). rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2.
            apply Hnv. exists bn. split; [exact Hbn|]. change (shadow_off BOTH) with ASHOFF in X1, X2. lia.
        - exact Kmap.
        - apply Bool.not_true_iff_false. intros X. apply Kna. apply (proj1 (in_ivs_APS _ _)). exact X.
        - exact Klz.
        -
          unfold APS.in_ghost. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Xp).
          apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. unfold APS.uE in X1, X2.
          destruct (Forall2_In_l _ _ _ _ HVISg Hp) as (bn & Hbn & E1 & E2 & E3). rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2.
          apply (shad_clear_sound V _ both_pure_facts bn a HVRp HPFc (proj1 (forallb_forall _ _) CLRg bn Hbn) HSS). lia. }

      pose proof (allowA_allow_of BOTH E _ _ HVIS0) as HAL.
      rewrite (allow_of_bnsh vgB) in HAL.
      change (shadow_off BOTH) with ASHOFF in HAL.
      change (flat_map (allow1 BOTH E) (a_vis hs ++ a_ghost hs)) with (allowA BOTH E hs) in HAL.
      change (both_vis_app ++ both_ghost) with both_vis in HAL.
      fold V in HAL.

      split.
      { assert (H0hid : forall a, b0_H0 V mo a = true -> APS.hid BOTH argH E hs mo a = true).
        { intros a Ha. unfold b0_H0 in Ha. apply andb_prop in Ha as [Hlz Hna]. apply negb_true_iff in Hna.
          destruct (APS.hid BOTH argH E hs mo a) eqn:Hh; [reflexivity|]. exfalso.
          pose proof (APS.lazy_cover_cs BSEGS BOTH LIM bHS2_0 XN0 XE0 XB0 both_hull_ok SINV argH (in_fs inp) NX0 E hs R FULL mo HC a Hlz Hh) as X.
          rewrite HAL in X. congruence. }
        assert (KOKr : know_ok bsegs E (mrestrict (APS.hid BOTH argH E hs mo) (mrestrict (b0_H0 V mo) FULL)) (kn hs)).
        { replace (mrestrict (APS.hid BOTH argH E hs mo) (mrestrict (b0_H0 V mo) FULL)) with (mrestrict (APS.hid BOTH argH E hs mo) FULL);
            [exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC)|].
          apply FunctionalExtensionality.functional_extensionality. intros a. unfold mrestrict.
          destruct (APS.hid BOTH argH E hs mo a) eqn:Hh; [reflexivity|].
          destruct (b0_H0 V mo a) eqn:Hz; [rewrite (H0hid a Hz) in Hh; discriminate Hh| reflexivity]. }
        exact (proj1 (export_sound_g vgB bsegs E (APS.hid BOTH argH E hs mo) (mrestrict (b0_H0 V mo) FULL) (kn hs) BIMG_LO BIMG_HI
                        KOKr HIDrom HULLvis _ _ MJ PJ)). }
      assert (USPW : vm_init_sp (m_vmmaps mo) = sp) by (apply bv_eq; exact TOP).
      destruct HC. cbn [en0 en_sp]. rewrite Hfd in co_fds0. rewrite Hbrk0 in co_brk0.
      constructor.
      + exact co_halt0.
      + exact co_fds0.
      + exact co_fs0.
      + exact co_res0.
      + exact co_mres0.
      + exact co_limit0.
      + rewrite co_brk0. cbn [edenot]. symmetry. apply Z_to_bv_bv_unsigned.
      + rewrite co_brk0 in co_sbrk0. cbn [edenot] in co_sbrk0. exact co_sbrk0.
      + exact USPW.
      + split; [exact LO|]. split; [lia| exact Hal].
      + exact HLD.
      + exact HKD.
      + apply seps_ivs_sep. exact co_seps0.
      + eapply Forall_impl; [|exact co_bounds0]. cbv beta. intros iv (B1 & B2 & B3 & B4 & B5 & B6).
        unfold hull_clear in B5. cbn [img_lo img_hi BOTH] in B5. rewrite ATOP in B6. unfold BIMG_LO, BIMG_HI. repeat split; assumption.
      + eapply Forall_impl; [|exact co_lazyb0]. cbv beta. intros iv (B5 & B6).
        unfold hull_clear in B5. cbn [img_lo img_hi BOTH] in B5. rewrite ATOP in B6. unfold BIMG_LO, BIMG_HI. split; assumption.
      + destruct co_wf0 as (_ & Wn & _). apply Forall_forall. intros iv Hiv. exact (Wn iv Hiv).
      + intros z Hz. apply (proj1 (in_ivs_APS _ _)). apply co_nasub0. apply (proj2 (in_ivs_APS _ _)). exact Hz.
      + exact (Z.le_trans _ _ _ co_totsz0 Ct).
      + exact (Z.le_trans _ _ _ co_eager0 Ce).
      + rewrite <- HAL. exact (Z.le_trans _ _ _ co_abytes0 Ca).
      + rewrite <- HAL. pose proof (minv_budget _ _ co_minv0) as B. rewrite co_limit0 in B. exact B.
      + rewrite <- HAL. exact (APS.A_wf_allowA BOTH bHS2_0 XN0 XE0 XB0 NX0 E hs).
      + exact (minv_nodup _ _ co_minv0).
      + intros p Hp. split; [exact (minv_aligned _ _ co_minv0 p Hp)|]. split; [exact (minv_lazy _ _ co_minv0 p Hp)|].
        rewrite <- HAL. apply page_allowedb_aallowed. exact (minv_allowed _ _ co_minv0 p Hp).
      + exact co_lzwf0.
      + exact co_wf0.
      + exact co_seps0.
      + destruct co_tidv0 as [T1 T2]. split; [exact (T1 Htids) | exact T2].
      + exact co_napos0.
      + exact co_rdr0. }
    -
      unfold cfg_of. split; [|reflexivity]. cbn [cfg_ms].
      split; [| split; [apply regs_eqv_refl| repeat split; reflexivity]].
      cbn [ms_regs ASN.PropExec.mkst MS].
      intros rr Hr. destruct (OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib.RegsEquiv.reg_of_nat rr) as (n & -> & Hn).
      pose proof (is_x0_of_nat n Hn Hr) as Hn1.
      rewrite (regs_ok_nth E _ R (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) n Hn1). rewrite reg_get_mkR by exact Hn1. rewrite Hregs.
      destruct n as [|n]; [cbv in Hr; discriminate|].
      cbn [en0 en_sp in_argv in_envp].
      do 31 (destruct n as [|n];
        [ unfold main_regs; cbn [nth];
          first [ reflexivity
                | symmetry; apply Z_to_bv_bv_unsigned
                | erewrite <- (zexp_of_sound E) by reflexivity; cbn [zv]; unfold BMAIN, BRA, BGP, BTP; f_equal; lia ]
        |]). lia.
  Qed.

  Variable T : TSet.
  Hypothesis T_nil : T [].
  Hypothesis MAINA : forall ms mo, bmain_at en0 inp ms mo -> srealizes bsegs (mkCfg ms mo) T.

  (* both main hand-off states of one CONFIG_RSEQ value reach the main phase *)
  Lemma main_holes : forall (r : Z) (HS2 : nat -> option acs) (s1 s2 : acs), RZ = r ->
    (forall h ch, HS2 h = Some ch -> ch = s1 \/ ch = s2) -> bridge_ok r true s1 -> bridge_ok r false s2 ->
    holes_stmt BSEGS BOTH LIM HS2 SINV argH (fun _ _ _ => T) (in_fs inp).
  Proof.
    intros r HS2 s1 s2 ERZ HS12 B1 B2 h ch Hh E R FULL mo HC.
    destruct (HS12 h ch Hh) as [-> | ->].
    - destruct (bmain_bridge_w r true s1 ERZ B1 E R FULL mo HC) as (ms & Heqv & Hat).
      apply (srealizes_eqv BSEGS (mkCfg ms mo) T (MAINA ms mo Hat)). apply cfg_eqv_sym. exact Heqv.
    - destruct (bmain_bridge_w r false s2 ERZ B2 E R FULL mo HC) as (ms & Heqv & Hat).
      apply (srealizes_eqv BSEGS (mkCfg ms mo) T (MAINA ms mo Hat)). apply cfg_eqv_sym. exact Heqv.
  Qed.

  Theorem both_main_boot :
    srealizes bsegs (init_config bsegs AsanUbsan.M.init_pc b_phdrs sp brk0 mbase rdraw target_alloc_limit inp) T.
  Proof.
    change bsegs with BSEGS. change b_phdrs with BPH. change target_alloc_limit with AsanInit.LIMIT.
    apply (both_boot sp rdraw brk0 mbase inp HL (fun _ _ => T)).
    - intros; reflexivity.
    - intros; exact T_nil.
    - intros ERZ. exact (main_holes 0 bHS2_0 bS21_0 bS22_0 ERZ (PlanRegen.hs2_some 1 bS21_0 2 bS22_0) bridge_ok_10 bridge_ok_20).
    - intros ERZ. exact (main_holes 1 bHS2_1 bS21_1 bS22_1 ERZ (PlanRegen.hs2_some 1 bS21_1 2 bS22_1) bridge_ok_11 bridge_ok_21).
  Qed.
End Bridge.
