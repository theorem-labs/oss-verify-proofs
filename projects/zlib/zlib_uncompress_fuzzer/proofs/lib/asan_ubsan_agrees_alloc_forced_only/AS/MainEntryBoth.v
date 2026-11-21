(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import
  PropExec ShapeAlg SpinAlg AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit BothStartup StartupHSBoth727 AsanRenum BothBoot
  AsanNodesAux RegsEqv0 SrzEqv MainExport MainFactsBoth.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import AcctCore TopLevelGen.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import TopLevel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.


Definition BMAIN : Z := 0x8c4a8.
Definition BRA : Z := 0xbd530.
Definition BGP : Z := 0x10800.
Definition BTP : Z := 0x65ccf8.
Definition BIMG_LO : Z := 0x10000.
Definition BIMG_HI : Z := 0x67f000.
Definition ACEIL : Z := 0x7fff7f800000.
Definition KHIGH : Z := 0x10007fff8000.
Definition ASHOFF : Z := 0x7fff8000.
Definition ABAND_LO : Z := 0x7fff7000.
Definition ABAND_LEN : Z := 0x100000001000.
Definition V_VMBRK : nat := 452.

Lemma bsegs_BSEGS : BSEGS = bsegs. Proof. reflexivity. Qed.
Lemma bph_BPH : BPH = b_phdrs. Proof. reflexivity. Qed.


Record bmodel (V : nat -> Z) (sp : word) (fs : Fs.Fs) (mo : Model) : Prop := BMODEL {
  bm_halted   : m_halted mo = None;
  bm_fds      : m_fds mo = [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
                            (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))];
  bm_fs       : m_fs mo = fs;
  bm_reserved : exists rx, vm_reserved (m_vmmaps mo) = segments_reserved bsegs ++ rx
                  /\ Forall (APS.resx_entry_ok BOTH) rx /\ (length rx <= 2)%nat /\ APS.sum_sizes rx <= 81920
                  /\ incl (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) (vm_reserved (m_vmmaps mo));
  bm_limit    : AsanInit.LIMIT <= vm_limit (m_vmmaps mo);
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
  bm_budget   : nonlazy_bytes mo + ivz_bytes (allow_of ASHOFF V both_vis) <= AsanInit.LIMIT;
  bm_allow_wf : ivz_wf (allow_of ASHOFF V both_vis);
  bm_mat_nodup : List.NoDup (m_vm_materialized mo);
  bm_mat      : forall p, In p (m_vm_materialized mo) ->
                  bv_unsigned p mod 4096 = 0 /\ page_in_ranges p (m_vm_lazy mo) = true /\ aallowed (allow_of ASHOFF V both_vis) p;
  (* every map is apart from every reserved range (cs_ok co_mres; AMI's third
     conjunct at ) *)
  bm_mres     : Forall (fun iv => Forall (APS.iv_disjoint iv) (vm_reserved (m_vmmaps mo))) (vm_maps (m_vmmaps mo));
  (* the channel reader (cs_ok co_rdr), which
     minv's last conjunct asks for at the main entry *)
  bm_rdr      : m_channel_reader mo = true
}.

(* the launch block's padding (AsanInit's start variable V 4) and the
   argument memory the start-up leaves untouched: the envp array, and the strings from the first argv string up to
   the stack top (AsanInit.argH0's two ranges). r30q2's Wblk (words after a 10-pair auxv) cannot be stated at . *)
Definition Wpad (en : ExecEntry) (inp : ProcInput) : Z :=
  Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) (en_sp en) (ed_top (en_draw en)) (in_argv inp) (in_envp inp) (in_execfn inp)).

Definition hidden_arg (en : ExecEntry) (inp : ProcInput) (a : Z) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
  (usp + 8 * argc + 16 <= a < usp + 8 * argc + 8 * envc + 24)
  \/ (usp + Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)) + Wpad en inp <= a
      < bv_unsigned (ed_top (en_draw en))).

Definition bshadow (a : Z) : Prop := (0x7fff7000 <= a < 0x8fff7000) \/ (0x2008fff7000 <= a < 0x10007fff8000).
Definition BSHADOWS : list (Z * Z) := [(0x7fff7000, 0x8fff7000); (0x2008fff7000, 0x10007fff8000)].
Definition bshadow_vis (V : nat -> Z) (a : Z) : Prop :=
  exists bn, In bn both_vis_app /\ ASHOFF + zv V (fst bn) / 8 <= a < ASHOFF + (zv V (fst bn) + zv V (snd bn)) / 8.
Definition bshadow0 (V : nat -> Z) (m : word -> option byte) : Prop :=
  forall a, bshadow a -> ~ bshadow_vis V a -> m (wa a) = Some (Z_to_bv 8 0).

Definition both_mem_facts_w (w : bool) : list mfact := if w then both_mem_facts_w1 else both_mem_facts_w2.
Definition both_pure_facts_w (w : bool) : list pfact := if w then both_pure_facts_w1 else both_pure_facts_w2.

Definition bmain_at (en : ExecEntry) (inp : ProcInput) (ms : machine_state) (mo : Model) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
  exists (w : bool) (V : nat -> Z) (m : word -> option byte),
    ms = MS (mkR (Z_to_bv 64 BRA) (Z_to_bv 64 (usp - 48)) (Z_to_bv 64 BGP) (Z_to_bv 64 BTP)
                 (Z_to_bv 64 (V 1032%nat)) (Z_to_bv 64 (V 1033%nat)) (Z_to_bv 64 (V 1034%nat))
                 (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (usp + 8))
                 (Z_to_bv 64 (usp + 8 * argc + 16)) (Z_to_bv 64 0x6000000000000000)
                 (Z_to_bv 64 (V 1035%nat)) (Z_to_bv 64 (V 1036%nat)) (Z_to_bv 64 (V 1037%nat)) (Z_to_bv 64 (V 1038%nat))
                 (Z_to_bv 64 BMAIN) (Z_to_bv 64 (usp + 8 * argc + 16))
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 (V 1039%nat)) (Z_to_bv 64 (V 1040%nat)) (Z_to_bv 64 (V 1041%nat)) (Z_to_bv 64 (V 1042%nat)))
            bvmap_empty (Z_to_bv 64 BMAIN) (Z_to_bv 32 0) None m (seg_rom bsegs)
    /\ (forall n, 0 <= V n < 2 ^ 64)
    /\ (V 0%nat = usp / 32768 /\ V 6%nat = usp mod 4096 / 16 /\ V 10%nat = usp mod 32768 / 4096
        /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp
        /\ V 1%nat = argc /\ V 2%nat = envc
        /\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) [])) /\ V 7%nat = Z.of_nat (length (nth 1 (in_argv inp) []))
        /\ V 4%nat = Wpad en inp /\ V 5%nat = bv_unsigned (en_brk en) / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
        /\ V 9%nat = bv_unsigned (in_hwcap inp)
        (* the launch block's parity, AsanInit's V 11 *)
        /\ V 11%nat = Z.of_nat (block_items (in_argv inp) (in_envp inp) mod 2))
    /\ Forall (mfact_ok bsegs V m) (both_mem_facts ++ both_mem_facts_w w)
    /\ Forall (pfact_ok V) (both_pure_facts ++ both_pure_facts_w w)
    (* argv[0] / argv[1], by the kernel build's rseq bit *)
    /\ Forall (mfact_ok bsegs V m) (both_argv_facts (rseq_z (kb_rseq (in_kernel inp))))
    /\ mem_inv bsegs m
    (* the stack known writable below sp is ASTK = 6144513 bytes *)
    /\ stk bsegs m (usp - ASTK) usp
    /\ (forall a, hidden_arg en inp a ->
          m (wa a) = wrap_mem inp (en_mmap_base en) b_phdrs (Z_to_bv 64 (Z.of_N Tgt_zlib_uncompress_fuzzer_both.M.init_pc))
                       (en_sp en) (en_draw en) (wa a))
    /\ bshadow0 V m
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


(* the plans' rename (AsanRenum.rv 15 4) and the main-entry exports. The lists keep the r30q2
   numbering (MainFactsAsan); the states are read through V := uev E o rv 15 4. *)
Lemma zv_rz : forall V e, zv V (rz e) = zv (fun n => V (rv 15 4 n)) e.
Proof. intros V e. induction e; cbn [rz zv]; try reflexivity; rewrite ?IHe1, ?IHe2; reflexivity. Qed.

Lemma mfact_ok_rmf : forall segs V m f, mfact_ok segs V m (rmf f) <-> mfact_ok segs (fun n => V (rv 15 4 n)) m f.
Proof. intros segs V m f. destruct f; cbn [rmf mfact_ok]; rewrite ?zv_rz; reflexivity. Qed.

Lemma pfact_ok_rpf : forall V f, pfact_ok V (rpf f) <-> pfact_ok (fun n => V (rv 15 4 n)) f.
Proof. intros V f. destruct f; cbn [rpf pfact_ok]; rewrite ?zv_rz; reflexivity. Qed.

Lemma Forall_mfact_rmf : forall segs V m l,
  Forall (mfact_ok segs V m) (map rmf l) -> Forall (mfact_ok segs (fun n => V (rv 15 4 n)) m) l.
Proof. intros segs V m l H. rewrite Forall_map in H. eapply Forall_impl; [|exact H]. intros f Hf. apply mfact_ok_rmf. exact Hf. Qed.

Lemma Forall_pfact_rpf : forall V l, Forall (pfact_ok V) (map rpf l) -> Forall (pfact_ok (fun n => V (rv 15 4 n))) l.
Proof. intros V l H. rewrite Forall_map in H. eapply Forall_impl; [|exact H]. intros f Hf. apply pfact_ok_rpf. exact Hf. Qed.

Lemma vis_rename : forall E ps vis,
  Forall2 (fun (p : expr * expr) (bn : zexp * zexp) =>
             bv_unsigned (edenot E (fst p)) = zv (uev E) (fst bn) /\ bv_unsigned (edenot E (snd p)) = zv (uev E) (snd bn)
             /\ 0 <= zv (uev E) (snd bn)) ps (rvis vis) ->
  Forall2 (fun (p : expr * expr) (bn : zexp * zexp) =>
             bv_unsigned (edenot E (fst p)) = zv (fun n => uev E (rv 15 4 n)) (fst bn)
             /\ bv_unsigned (edenot E (snd p)) = zv (fun n => uev E (rv 15 4 n)) (snd bn)
             /\ 0 <= zv (fun n => uev E (rv 15 4 n)) (snd bn)) ps vis.
Proof.
  intros E ps. induction ps as [|p ps IH]; intros [|bn vis] H; unfold rvis in H; cbn [map] in H; inversion H; subst.
  - constructor.
  - constructor; [|apply IH; unfold rvis; assumption].
    match goal with Hh : _ /\ _ |- _ => cbn [fst snd] in Hh; rewrite !zv_rz in Hh; exact Hh end.
Qed.

Lemma ledger_den_rle : forall V l maps, ledger_den V (map rle l) maps -> ledger_den (fun n => V (rv 15 4 n)) l maps.
Proof.
  intros V l. induction l as [|e l IH]; intros maps H; [exact H|].
  destruct e as [b n k|n]; cbn [map rle ledger_den] in H |- *.
  - destruct H as (maps' & -> & H'). exists maps'. rewrite zv_rz. split; [reflexivity| apply IH; exact H'].
  - destruct H as [H | (iv & maps' & -> & Hsz & H')]; [left; apply IH; exact H|].
    right. exists iv, maps'. split; [reflexivity|]. split; [exact Hsz| apply IH; exact H'].
Qed.

Lemma kinds_rle : forall V mo l,
  Forall (lentry_kind_ok V mo) (map rle l) -> Forall (lentry_kind_ok (fun n => V (rv 15 4 n)) mo) l.
Proof.
  intros V mo l H. rewrite Forall_map in H. eapply Forall_impl; [|exact H]. intros e He.
  destruct e as [b n k|n]; [destruct k|]; cbn [rle lentry_kind_ok] in *; rewrite ?zv_rz in He; exact He.
Qed.

Lemma allow_of_rvis : forall off U l, allow_of off U (rvis l) = allow_of off (fun n => U (rv 15 4 n)) l.
Proof.
  intros off U l. unfold allow_of, rvis. induction l as [|[b n] l IH]; [reflexivity|].
  cbn [map flat_map fst snd]. cbv zeta. rewrite !zv_rz. f_equal. exact IH.
Qed.

Lemma rv_small : forall n, (n < 15)%nat -> rv 15 4 n = n.
Proof. intros n Hn. unfold rv. destruct (Nat.ltb_spec n 15); [reflexivity| lia]. Qed.

Section Bridge.
  Variable sp brk0 mbase : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nof sigm : word.
  Variable hw : word.
  Variable abt : bool.
  Variable urnd : InputStream.
  (* the launch's kernel build, AT_EXECFN and SIGPIPE disposition (AsanInit's input) *)
  Variable kb : KernelBuild.
  Variable efn : list byte.
  Variable sigdef : bool.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  Definition en0 : ExecEntry := mkEntry sp brk0 mbase rdraw.
  Definition inp0 : ProcInput := AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef.
  (* asan_boot's launch premises; asan_side_ok discharges them from side_ok's own premises *)
  Hypothesis Hlaunch : valid_launch inp0.
  Hypothesis Hlau : entry_launch_ok_va Sv48 en0 inp0.

  #[local] Abbreviation APC0 := Tgt_zlib_uncompress_fuzzer_both.M.init_pc.
  #[local] Abbreviation SINV := (SINV0 BPH APC0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef).
  #[local] Abbreviation argH := (argH0 sp rdraw argv envp kb efn).
  #[local] Abbreviation E0a := (AsanInit.E0 sp rdraw brk0 mbase argv envp uid gid hw kb efn).
  #[local] Abbreviation LIM := AsanInit.LIMIT.
  #[local] Abbreviation RZK := (rseq_z (kb_rseq kb)).
  (* the run's tail, the vDSO pair (Run.run_segments) *)
  #[local] Abbreviation VS := (vdso_segments (in_kernel inp0) sp mbase).

  Let AH := argH0_high APC0 sp rdraw argv envp Hsp Hva kb efn.

  Lemma sinv_usp : forall E M, SINV E M -> uE E e_sp0 = bv_unsigned sp.
  Proof.
    intros E M [HE _].
    transitivity (uE E0a e_sp0);
      [| exact (AsanInit.u_e_sp0 BPH APC0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net Hsp Hva Hve Hfit
                  nof sigm abt urnd kb efn sigdef Hlau)].
    unfold e_sp0, uE. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot].
    rewrite !HE by (unfold NX0, V_S1, V_S2, V_SP; lia). reflexivity.
  Qed.

  Theorem bmain_bridge_w : forall (w : bool) (r : Z) (hs : acs),
    r = 0 \/ r = 1 -> r = RZK -> hs = hs727 w r ->
    forall E R FULL mo,
    cs_ok BSEGS BOTH LIM SINV argH fs E hs R FULL mo ->
    exists ms, cfg_eqv (cfg_of (BSEGS ++ VS) R (pc hs) FULL mo) (mkCfg (TopLevel.set_rom (seg_rom (BSEGS ++ VS)) ms) mo)
               /\ bmain_at en0 inp0 ms mo.
  Proof.
    intros w r hs Hr HrK Hhs E R FULL mo HC.
    pose proof (just727_ok w r Hr) as JUST. unfold just727 in JUST. cbv zeta in JUST. rewrite <- Hhs in JUST.
    apply andb_prop in JUST as [JUST Cab]. apply andb_prop in JUST as [JUST Cea].
    apply andb_prop in JUST as [JUST Cyl]. apply andb_prop in JUST as [JUST Ctot].
    apply andb_prop in JUST as [JUST LJ]. apply andb_prop in JUST as [JUST VJg].
    apply andb_prop in JUST as [JUST VJa]. apply andb_prop in JUST as [MJ PJ].
    apply Z.eqb_eq in Cab, Cea, Cyl, Ctot.
    assert (Hpc : pc hs = BMAIN) by (rewrite Hhs; destruct w; destruct Hr as [-> | ->]; reflexivity).
    assert (Hfd : a_fd hs = FdStd) by (rewrite Hhs; destruct w; destruct Hr as [-> | ->]; reflexivity).
    assert (Hbrk0 : a_brk hs = EVar 456) by (rewrite Hhs; destruct w; destruct Hr as [-> | ->]; reflexivity).
    assert (Hregs : s_regs (a_ss hs) = s_regs (a_ss HS2_1_r0)) by (rewrite Hhs; destruct w; destruct Hr as [-> | ->]; reflexivity).
    rewrite Hpc.
    pose (V := fun n => uev E (rv 15 4 n)).
    assert (HV : forall n, (n < 15)%nat -> V n = uev E n) by (intros n Hn; unfold V; rewrite rv_small by exact Hn; reflexivity).
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as HSINV. pose proof HSINV as [Hev Hhid].
    pose proof (sinv_usp E FULL HSINV) as USP.
    pose proof (AsanInit.uE0 BPH APC0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net Hsp Hva Hve Hfit
                  nof sigm abt urnd kb efn sigdef Hlau) as (U0 & U6 & U1 & U2 & U3 & U4 & U5 & U11).
    pose proof (AsanInit.uE0_sp BPH APC0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net Hsp Hva Hve Hfit
                  nof sigm abt urnd kb efn sigdef Hlau) as U10.
    pose proof (AsanInit.uE0_L1 APC0 sp rdraw brk0 mbase argv envp uid gid hw Hva kb efn) as U7.
    pose proof (AsanInit.uE0_uid sp rdraw brk0 mbase argv envp uid gid hw kb efn) as U8.
    pose proof (AsanInit.uE0_hw sp rdraw brk0 mbase argv envp uid gid hw kb efn) as U9.
    unfold APS.uE in U0, U6, U1, U2, U3, U4, U5, U11, U7, U8, U9, U10.
    cbn [edenot] in U0, U6, U1, U2, U3, U4, U5, U11, U7, U8, U9, U10.
    assert (PIN : forall n z, (n < 15)%nat -> bv_unsigned (ev E0a n) = z -> uev E n = z).
    { intros n z Hn Hz. unfold uev. rewrite (Hev n) by (unfold NX0; lia). exact Hz. }
    pose proof (PIN 0%nat _ ltac:(lia) U0) as P0. pose proof (PIN 6%nat _ ltac:(lia) U6) as P6.
    pose proof (PIN 1%nat _ ltac:(lia) U1) as P1. pose proof (PIN 2%nat _ ltac:(lia) U2) as P2.
    pose proof (PIN 3%nat _ ltac:(lia) U3) as P3. pose proof (PIN 4%nat _ ltac:(lia) U4) as P4.
    pose proof (PIN 5%nat _ ltac:(lia) U5) as P5. pose proof (PIN 7%nat _ ltac:(lia) U7) as P7.
    pose proof (PIN 8%nat _ ltac:(lia) U8) as P8. pose proof (PIN 9%nat _ ltac:(lia) U9) as P9.
    pose proof (PIN 10%nat _ ltac:(lia) U10) as P10. pose proof (PIN 11%nat _ ltac:(lia) U11) as P11.
    clear U0 U6 U1 U2 U3 U4 U5 U7 U8 U9 U10 U11.
    assert (Hal : bv_unsigned sp mod 16 = 0) by (pose proof Hsp as (_ & _ & H); exact H).
    pose proof (AsanInit.usp_lo sp Hsp) as LO.
    pose proof (AsanInit.usp_hi BPH APC0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net Hva Hve Hfit
                  nof sigm abt urnd kb efn sigdef Hlau) as HI.
    pose proof (AsanInit.len_av APC0 sp rdraw argv envp Hva kb efn) as LA.
    pose proof (AsanInit.len_ev APC0 sp rdraw argv envp Hve kb efn) as LE.
    assert (PSP : 32768 * uev E 0%nat + 4096 * uev E 10%nat + 16 * uev E 6%nat = bv_unsigned sp).
    { rewrite P0, P6, P10. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (VR : forall n, 0 <= V n < 2 ^ 64) by (intros n; unfold V; apply uev_range).
    pose proof (co_top _ _ _ _ _ _ _ _ _ _ _ HC) as TOP. rewrite USP in TOP.
    assert (ATOP : atop mo = bv_unsigned sp - 8388608) by (unfold atop; rewrite TOP; reflexivity).
    eexists. split; cycle 1.
    {
      exists w, V, FULL. split; [reflexivity|].
      split; [exact VR|].
      split; [rewrite !HV by lia; repeat split; assumption|].
      assert (HIDrom : forall a, APS.hid BOTH argH E hs mo a = true -> seg_rom bsegs a = None).
      { intros a Ha. apply (APS.seg_rom_off_hull BSEGS BOTH both_in_hull).
        unfold APS.hid in Ha. apply orb_prop in Ha as [Ha|Ha].
        - pose proof (AH E a Ha) as Hc. unfold APS.in_hull. cbn [img_lo img_hi BOTH]. unfold CEIL in Hc.
          apply andb_false_iff. right. apply Z.ltb_ge. lia.
        - apply negb_true_iff in Ha. unfold APS.vis in Ha. apply orb_false_iff in Ha as [Ha _]. apply orb_false_iff in Ha as [Ha _]. exact Ha. }
      assert (HULLvis : forall a, BIMG_LO <= bv_unsigned a < BIMG_HI -> APS.hid BOTH argH E hs mo a = false).
      { intros a Ha. apply (APS.hid_hull BOTH both_hull_ok argH AH). unfold APS.in_hull. cbn [img_lo img_hi BOTH]. unfold BIMG_LO, BIMG_HI in Ha.
        apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
      (* the justification at export_sound's own form, so that no list is unified against an evar *)
      assert (MJ' : forallb (mjustify (kn hs) (var_ranges (kn hs)) BIMG_LO BIMG_HI) (map rmf (mlist727 w r)) = true) by exact MJ.
      assert (PJ' : forallb (pjustify (kn hs) (var_ranges (kn hs))) (map rpf (plist727 w)) = true) by exact PJ.
      pose proof (export_sound bsegs E (APS.hid BOTH argH E hs mo) FULL (kn hs) BIMG_LO BIMG_HI
                    (co_know _ _ _ _ _ _ _ _ _ _ _ HC) HIDrom HULLvis (map rmf (mlist727 w r)) (map rpf (plist727 w)) MJ' PJ') as [HMF0 HPF0].
      pose proof (Forall_mfact_rmf bsegs (uev E) FULL _ HMF0) as HMF. pose proof (Forall_pfact_rpf (uev E) _ HPF0) as HPF.
      fold V in HMF, HPF. clear HMF0 HPF0.
      (* the list names are unfolded before any conversion: converting a folded name against [app] reduces the lists *)
      unfold plist727 in HPF.
      unfold mlist727 in HMF. rewrite app_assoc in HMF. apply Forall_app in HMF as [HMFm HMFa].
      pose proof (proj1 (Forall_app _ _ _) HMFm) as [HMFc _].
      pose proof (proj1 (Forall_app _ _ _) HPF) as [HPFc _].
      split; [exact HMFm|]. unfold both_pure_facts_w. split; [exact HPF|].
      split; [rewrite HrK in HMFa; exact HMFa|].
      split.
      { intros a b Hab. rewrite a_ro_addr.
        destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); [|reflexivity].
        destruct (Z.ltb_spec0 (bv_unsigned a) 0xcd000); [|reflexivity].
        exfalso. pose proof (mimg_cover bsegs V FULL both_mem_facts 0x10000 0xcd000 HMFc ltac:(vm_compute; reflexivity) (bv_unsigned a) ltac:(lia)) as X.
        unfold wa in X. rewrite Z_to_bv_bv_unsigned in X. congruence. }
      (* the stack window is ASTK bytes below sp *)
      split.
      { pose proof (mwr_find bsegs V FULL both_mem_facts (ZAdd usp_z (ZLit (- ASTK))) ASTK
                      HMFc ltac:(vm_compute; reflexivity)) as W.
        unfold usp_z in W. cbn [zv] in W. rewrite !HV in W by lia.
        replace (32768 * uev E 0%nat + (16 * uev E 6%nat + 4096 * uev E 10%nat) + - ASTK) with (bv_unsigned sp - ASTK) in W by lia.
        cbn [en0 en_sp].
        apply wr_at_stk; [replace (bv_unsigned sp - (bv_unsigned sp - ASTK)) with ASTK by lia; exact W|].
        intros a Ha. apply ref_find_segment_none; unfold ASTK in *; lia. }
      (* the argument memory is AsanInit's argH0 ranges *)
      split.
      { intros a Ha. apply Hhid.
        assert (RK : kb_rseq (in_kernel inp0) = kb_rseq kb) by reflexivity.
        unfold hidden_arg, Wpad in Ha. rewrite RK in Ha.
        cbn [en0 inp0 AsanInit.inp en_sp en_draw in_argv in_envp in_execfn] in Ha.
        pose proof (bv_unsigned_in_range 64 (ed_top rdraw)) as TR. unfold bv_modulus in TR.
        unfold argH0. cbv zeta. rewrite wa_unsigned by (destruct Ha as [Ha|Ha]; lia).
        apply orb_true_intro. destruct Ha as [Ha|Ha]; [left|right]; apply andb_true_intro; split;
          first [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
      pose proof (var_ranges_sound BSEGS E _ (kn hs) (co_know _ _ _ _ _ _ _ _ _ _ _ HC)) as HVR.
      pose proof (vis_match_sound E _ _ _ HVR VJa) as HVISa0. pose proof (vis_match_sound E _ _ _ HVR VJg) as HVISg0.
      pose proof (vis_rename E _ _ HVISa0) as HVISa. pose proof (vis_rename E _ _ HVISg0) as HVISg.
      fold V in HVISa, HVISg.
      pose proof (Forall2_app HVISa HVISg) as HVIS. change (both_vis_app ++ both_ghost) with both_vis in HVIS.
      pose proof (ledger_den_sound E _ HVR _ _ _ LJ (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)) as HLD0.
      pose proof (ledger_kinds_sound E _ HVR _ _ mo LJ (co_none _ _ _ _ _ _ _ _ _ _ _ HC) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC)) as HKD0.
      pose proof (ledger_den_rle (uev E) _ _ HLD0) as HLD. pose proof (kinds_rle (uev E) mo _ HKD0) as HKD.
      fold V in HLD, HKD. clear HLD0 HKD0.
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
      pose proof (allowA_allow_of BOTH E _ _ (Forall2_app HVISa0 HVISg0)) as HAL.
      replace (rvis both_vis_app ++ rvis both_ghost) with (rvis both_vis) in HAL by (unfold rvis, both_vis; rewrite map_app; reflexivity).
      rewrite allow_of_rvis in HAL. fold V in HAL.
      change (shadow_off BOTH) with ASHOFF in HAL. change (flat_map (allow1 BOTH E) (a_vis hs ++ a_ghost hs)) with (allowA BOTH E hs) in HAL.
      assert (USPW : vm_init_sp (m_vmmaps mo) = sp) by (apply bv_eq; exact TOP).
      destruct HC. cbn [inp0 AsanInit.inp in_fs en0 en_sp]. rewrite Hfd in co_fds0. rewrite Hbrk0 in co_brk0.
      constructor.
      + exact co_halt0.
      + exact co_fds0.
      + exact co_fs0.
      + (* cs_ok's reservation tail and vDSO pair *)
        destruct co_res0 as (rx & R1 & R2 & R3 & R4 & _). exists rx.
        split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. exact co_vdso0.
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
      + rewrite <- Ctot. exact co_totsz0.
      + rewrite <- Cea. exact co_eager0.
      + rewrite <- Cab, <- HAL. exact co_abytes0.
      + rewrite <- HAL. apply (Z.le_trans _ (both_eager + both_abytes));
          [apply Z.add_le_mono; [rewrite <- Cea; exact co_eager0 | rewrite <- Cab; exact co_abytes0] | vm_compute; discriminate].
      + rewrite <- HAL. exact (A_wf_allowA' BOTH E hs).
      + exact (minv_nodup _ _ co_minv0).
      + intros p Hp. split; [exact (minv_aligned _ _ co_minv0 p Hp)|]. split; [exact (minv_lazy _ _ co_minv0 p Hp)|].
        rewrite <- HAL. apply page_allowedb_aallowed. exact (minv_allowed _ _ co_minv0 p Hp).
      + exact co_mres0.
      + exact co_rdr0. }
    -
      unfold cfg_of. split; [|reflexivity]. cbn [cfg_ms]. unfold TopLevel.set_rom.
      split; [| split; [apply regs_eqv_refl| repeat split; reflexivity]].
      cbn [ms_regs AS.PropExec.mkst MS].
      intros r0 Hr0. destruct (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib.RegsEquiv.reg_of_nat r0) as (n & -> & Hn).
      pose proof (is_x0_of_nat n Hn Hr0) as Hn1.
      rewrite (regs_ok_nth E _ R (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) n Hn1). rewrite reg_get_mkR by exact Hn1. rewrite Hregs.
      destruct n as [|n]; [cbv in Hr0; discriminate|].
      cbn [en0 inp0 AsanInit.inp en_sp in_argv in_envp].
      do 31 (destruct n as [|n];
        [ cbn [nth HS2_1_r0 a_ss s_regs];
          first [ reflexivity
                | symmetry; apply Z_to_bv_bv_unsigned
                | erewrite <- (zexp_of_sound E) by reflexivity; cbn [zv]; unfold BMAIN, BRA, BGP, BTP; f_equal; lia ]
        |]). lia.
  Qed.

  Variable T : TSet.
  Hypothesis T_nil : T [].
  (* the main body over the run's list at the run's ROM *)
  Hypothesis MAINA : forall ms mo, bmain_at en0 inp0 ms mo ->
    srealizes (bsegs ++ VS) (mkCfg (TopLevel.set_rom (seg_rom (bsegs ++ VS)) ms) mo) T.

  (* the boot is over the run's list asegs ++ VS (asan_boot's VSEGS premises: the pair is
     not executable, TopLevel.vdso_nonexec, and reserves nothing, TopLevel.run_segments_reserved at segs = []) *)
  Theorem both_main_boot_lim : forall lim, AsanInit.LIMIT <= lim ->
    srealizes (bsegs ++ VS) (init_config (bsegs ++ VS) Tgt_zlib_uncompress_fuzzer_both.M.init_pc b_phdrs sp brk0 mbase rdraw lim inp0) T.
  Proof.
    intros lim Hlim. change bsegs with BSEGS. change b_phdrs with BPH.
    assert (Hr : RZK = 0 \/ RZK = 1) by (unfold rseq_z; destruct (kb_rseq kb); [right|left]; reflexivity).
    apply (both_boot sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd lim Hlim kb efn sigdef
             Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hlaunch Hlau (fun _ _ => T) (fun _ _ _ _ => eq_refl) (fun _ _ => T_nil)
             VS (vdso_nonexec (in_kernel inp0) sp mbase) (run_segments_reserved [] inp0 sp mbase)).
    intros h ch Hh E R FULL mo HC.
    destruct h as [|[|[|h]]]; cbn [HS727_2 Nat.eqb] in Hh; try discriminate Hh; injection Hh as <-.
    + destruct (bmain_bridge_w true RZK _ Hr eq_refl eq_refl E R FULL mo HC) as (ms & Heqv & Hat).
      apply (srealizes_eqv (BSEGS ++ VS) (mkCfg (TopLevel.set_rom (seg_rom (BSEGS ++ VS)) ms) mo) T (MAINA ms mo Hat)).
      apply cfg_eqv_sym. exact Heqv.
    + destruct (bmain_bridge_w false RZK _ Hr eq_refl eq_refl E R FULL mo HC) as (ms & Heqv & Hat).
      apply (srealizes_eqv (BSEGS ++ VS) (mkCfg (TopLevel.set_rom (seg_rom (BSEGS ++ VS)) ms) mo) T (MAINA ms mo Hat)).
      apply cfg_eqv_sym. exact Heqv.
  Qed.

  Theorem both_main_boot :
    srealizes (bsegs ++ VS) (init_config (bsegs ++ VS) Tgt_zlib_uncompress_fuzzer_both.M.init_pc b_phdrs sp brk0 mbase rdraw target_alloc_limit inp0) T.
  Proof. apply both_main_boot_lim. vm_compute. discriminate. Qed.
End Bridge.


(* the run reads asegs ++ the vDSO pair (Run.run_segments), so the main body's
   hypothesis and the conclusion are over that list.  The launch's input is AsanInit.inp at kb := in_kernel inp
   (valid_input_either: in_kernel inp = recorded_kernel (in_kernel inp)), fs := in_fs inp (fs_seed_tmp image tmp,
   which AsanInit.inp's empty tmp reduces back to), Sv48, the channel reader and no SIGPIPE death. *)
Theorem both_side_srz_lim : forall (T : tfam) (lim : Z), AsanInit.LIMIT <= lim ->
  (forall en inp, valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp ->
      T inp en [] /\ forall ms mo, bmain_at en inp ms mo ->
        srealizes (bsegs ++ vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en))
          (mkCfg (TopLevel.set_rom (seg_rom (bsegs ++ vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en))) ms) mo) (T inp en)) ->
  forall en inp, valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp ->
    srealizes (bsegs ++ vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en))
      (init_config (bsegs ++ vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en))
         b_init_pc b_phdrs (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp) (T inp en).
Proof.
  intros T lim Hlim HT. intros [sp brk0 mbase rdraw] inp Hv Hi.
  destruct (HT _ _ Hv Hi) as [Tnil MAINA].
  rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in Hv.
  destruct Hv as (Hsp & Hbrk & Hmb & Hfit & Hlau).
  pose proof Hi as (Hva & Hve & Hfs & Hkeys & Hreal & [Huid Hgid] & Hnof & Hsigm & Hhw & Hvasz & Hurnd & Hlaunch
                    & Hrdr & Hsigt & Hkern).
  destruct inp as [argv envp ifs stdin uid gid groups net nof sigm hw abt vasz urnd tmp kern efn rdr sigdef sigt].
  cbn [in_argv in_envp in_uid in_hwcap in_va_size in_channel_reader in_sigpipe_terminal in_kernel en_sp en_brk
       en_mmap_base en_draw] in *.
  subst vasz rdr sigt.
  rewrite Hkern in Tnil, MAINA, Hlaunch, Hlau |- *.
  exact (both_main_boot_lim sp brk0 mbase rdraw argv envp (fs_seed_tmp ifs tmp) stdin uid gid groups net nof sigm hw abt urnd
           kern efn sigdef Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hlaunch Hlau _ Tnil MAINA lim Hlim).
Qed.

Theorem both_side_ok : forall T : tfam,
  (forall en inp, valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp ->
      T inp en [] /\ forall ms mo, bmain_at en inp ms mo ->
        srealizes (bsegs ++ vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en))
          (mkCfg (TopLevel.set_rom (seg_rom (bsegs ++ vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en))) ms) mo) (T inp en)) ->
  side_ok bsegs b_init_pc b_phdrs target_alloc_limit T.
Proof.
  intros T HT. apply side_ok_of_srealizes. intros en inp Hv Hi. cbv zeta. unfold run_segments.
  exact (both_side_srz_lim T target_alloc_limit ltac:(vm_compute; discriminate) HT en inp Hv Hi).
Qed.
