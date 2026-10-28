(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanStartup StartupHS2Asan AsanBoot
  RegsEqv0 SrzEqv MainExport MainFactsAsan.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import AcctCore TopLevelGen.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib Require Import TopLevel.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition BMAIN : Z := 0x82588.           (* [comment removed for export] *)
Definition BRA : Z := 0xb6724.             (* [comment removed for export] *)
Definition BGP : Z := 0x10800.             (* [comment removed for export] *)
Definition BTP : Z := 0x602cb0.            (* [comment removed for export] *)
Definition BIMG_LO : Z := 0x10000.         (* [comment removed for export] *)
Definition BIMG_HI : Z := 0x625000.
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
  bm_reserved : vm_reserved (m_vmmaps mo) = segments_reserved bsegs;
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
                  bv_unsigned p mod 4096 = 0 /\ page_in_ranges p (m_vm_lazy mo) = true /\ aallowed (allow_of ASHOFF V both_vis) p
}.

(* [comment removed for export] *)
Definition Wblk (en : ExecEntry) (inp : ProcInput) : Z :=
  (Z.of_nat (length (build_stack_bytes b_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en))) - 16
   - (8 * Z.of_nat (length (in_argv inp)) + 8 * Z.of_nat (length (in_envp inp)) + 184)) / 8.

(* [comment removed for export] *)
Definition hidden_arg (en : ExecEntry) (inp : ProcInput) (a : Z) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
  (usp + 8 * argc + 16 <= a < usp + 8 * argc + 8 * envc + 24)
  \/ (usp + 8 * argc + 8 * envc + 184 <= a < usp + 8 * argc + 8 * envc + 184 + 8 * Wblk en inp).

(* [comment removed for export] *)
Definition bshadow (a : Z) : Prop := (0x7fff7000 <= a < 0x8fff7000) \/ (0x2008fff7000 <= a < 0x10007fff8000).
Definition BSHADOWS : list (Z * Z) := [(0x7fff7000, 0x8fff7000); (0x2008fff7000, 0x10007fff8000)].
Definition bshadow_vis (V : nat -> Z) (a : Z) : Prop :=
  exists bn, In bn both_vis_app /\ ASHOFF + zv V (fst bn) / 8 <= a < ASHOFF + (zv V (fst bn) + zv V (snd bn)) / 8.
(* [comment removed for export] *)
Definition bshadow0 (V : nat -> Z) (m : word -> option byte) : Prop :=
  forall a, bshadow a -> ~ bshadow_vis V a -> m (wa a) = Some (Z_to_bv 8 0).

(* [comment removed for export] *)
Definition both_mem_facts_w (w : bool) : list mfact := if w then both_mem_facts_w1 else both_mem_facts_w2.
Definition both_pure_facts_w (w : bool) : list pfact := if w then both_pure_facts_w1 else both_pure_facts_w2.

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
        /\ V 4%nat = Wblk en inp /\ V 5%nat = bv_unsigned (en_brk en) / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
        /\ V 9%nat = bv_unsigned (in_hwcap inp))
    /\ Forall (mfact_ok bsegs V m) (both_mem_facts ++ both_mem_facts_w w)
    /\ Forall (pfact_ok V) (both_pure_facts ++ both_pure_facts_w w)
    /\ mem_inv bsegs m
    /\ stk bsegs m (usp - 8388608) usp
    /\ (forall a, hidden_arg en inp a ->
          m (wa a) = wrap_mem b_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) (wa a))
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
  Variable urnd : InputStream.   (* [comment removed for export] *)
  Variable tmp : Fs.Fs.          (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  Definition en0 : ExecEntry := mkEntry sp brk0 mbase rdraw.
  Definition inp0 : ProcInput := AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp.

  #[local] Abbreviation SINV := (SINV0 BPH sp rdraw brk0 argv envp uid hw).
  #[local] Abbreviation argH := (argH0 BPH sp rdraw argv envp uid hw).
  #[local] Abbreviation E0a := (AsanInit.E0 BPH sp rdraw brk0 argv envp uid hw).
  #[local] Abbreviation LIM := AsanInit.LIMIT.

  Let AH := argH0_high BPH sp rdraw argv envp uid hw Hsp Hva.

  (* [comment removed for export] *)
  Lemma sinv_usp : forall E M, SINV E M -> uE E e_sp0 = bv_unsigned sp.
  Proof.
    intros E M [HE _].
    transitivity (uE E0a e_sp0); [| exact (AsanInit.u_e_sp0 BPH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit)].
    unfold e_sp0, uE. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot].
    rewrite !HE by (unfold NX0, V_S1, V_S2, V_SP; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem bmain_bridge_w : forall (w : bool) (hs : acs),
    s_regs (a_ss hs) = s_regs (a_ss HS_both2_1) -> pc hs = BMAIN -> a_fd hs = FdStd -> a_brk hs = EVar V_VMBRK ->
    forallb (mjustify (kn hs) (var_ranges (kn hs)) BIMG_LO BIMG_HI) (both_mem_facts ++ both_mem_facts_w w) = true ->
    forallb (pjustify (kn hs) (var_ranges (kn hs))) (both_pure_facts ++ both_pure_facts_w w) = true ->
    vis_match (var_ranges (kn hs)) (a_vis hs) both_vis_app = true /\ vis_match (var_ranges (kn hs)) (a_ghost hs) both_ghost = true ->
    ledger_xmatch (var_ranges (kn hs)) (a_maps hs) both_ledger = true ->
    a_totsz hs = both_totsz /\ a_ylo hs = both_ylo /\ a_eager hs = both_eager /\ a_abytes hs = both_abytes ->
    forall E R FULL mo,
    cs_ok BSEGS ASAN LIM SINV argH (fs_seed_tmp fs tmp) E hs R FULL mo ->
    exists ms, cfg_eqv (cfg_of BSEGS R (pc hs) FULL mo) (mkCfg ms mo) /\ bmain_at en0 inp0 ms mo.
  Proof.
    intros w hs Hregs Hpc Hfd Hbrk0 MJ PJ VJ LJ CONSTS E R FULL mo HC. rewrite Hpc.
    set (V := uev E).
    (* [comment removed for export] *)
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as HSINV. pose proof HSINV as [Hev Hhid].
    pose proof (sinv_usp E FULL HSINV) as USP.
    pose proof (AsanInit.uE0 BPH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as (U0 & U6 & U1 & U2 & U3 & U4 & U5).
    pose proof (AsanInit.uE0_sp BPH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U10.
    pose proof (AsanInit.uE0_L1 BPH sp rdraw brk0 argv envp uid hw Hva) as U7.
    pose proof (AsanInit.uE0_uid BPH sp rdraw brk0 argv envp uid hw) as U8.
    pose proof (AsanInit.uE0_hw BPH sp rdraw brk0 argv envp uid hw) as U9.
    unfold APS.uE in U0, U6, U1, U2, U3, U4, U5, U7, U8, U9, U10. cbn [edenot] in U0, U6, U1, U2, U3, U4, U5, U7, U8, U9, U10.
    assert (PIN : forall n z, (n < 11)%nat -> bv_unsigned (ev E0a n) = z -> V n = z).
    { intros n z Hn Hz. unfold V, uev. rewrite (Hev n) by (unfold NX0; lia). exact Hz. }
    pose proof (PIN 0%nat _ ltac:(lia) U0) as P0. pose proof (PIN 6%nat _ ltac:(lia) U6) as P6.
    pose proof (PIN 1%nat _ ltac:(lia) U1) as P1. pose proof (PIN 2%nat _ ltac:(lia) U2) as P2.
    pose proof (PIN 3%nat _ ltac:(lia) U3) as P3. pose proof (PIN 4%nat _ ltac:(lia) U4) as P4.
    pose proof (PIN 5%nat _ ltac:(lia) U5) as P5. pose proof (PIN 7%nat _ ltac:(lia) U7) as P7.
    pose proof (PIN 8%nat _ ltac:(lia) U8) as P8. pose proof (PIN 9%nat _ ltac:(lia) U9) as P9.
    pose proof (PIN 10%nat _ ltac:(lia) U10) as P10.
    clear U0 U6 U1 U2 U3 U4 U5 U7 U8 U9 U10.
    assert (Hal : bv_unsigned sp mod 16 = 0) by (pose proof Hsp as (_ & _ & H); exact H).
    pose proof (AsanInit.usp_lo sp Hsp) as LO.
    pose proof (AsanInit.usp_hi BPH sp rdraw argv envp uid hw Hva Hve Hfit) as HI.
    assert (PSP : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = bv_unsigned sp).
    { rewrite P0, P6, P10. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (VR : forall n, 0 <= V n < 2 ^ 64) by (intros n; apply uev_range).
    (* [comment removed for export] *)
    pose proof (co_top _ _ _ _ _ _ _ _ _ _ _ HC) as TOP. rewrite USP in TOP.
    assert (ATOP : atop mo = bv_unsigned sp - 8388608) by (unfold atop; rewrite TOP; reflexivity).
    eexists. split; cycle 1.
    { (* [comment removed for export] *)
      exists w, V, FULL. split; [reflexivity|].
      split; [exact VR|].
      split; [repeat split; assumption|].
      (* [comment removed for export] *)
      assert (HIDrom : forall a, APS.hid ASAN argH E hs mo a = true -> seg_rom bsegs a = None).
      { intros a Ha. apply (APS.seg_rom_off_hull BSEGS ASAN both_in_hull).
        unfold APS.hid in Ha. apply orb_prop in Ha as [Ha|Ha].
        - pose proof (AH E a Ha) as Hc. unfold APS.in_hull. cbn [img_lo img_hi ASAN]. unfold CEIL in Hc.
          apply andb_false_iff. right. apply Z.ltb_ge. lia.
        - apply negb_true_iff in Ha. unfold APS.vis in Ha. apply orb_false_iff in Ha as [Ha _]. apply orb_false_iff in Ha as [Ha _]. exact Ha. }
      assert (HULLvis : forall a, BIMG_LO <= bv_unsigned a < BIMG_HI -> APS.hid ASAN argH E hs mo a = false).
      { intros a Ha. apply (APS.hid_hull ASAN both_hull_ok argH AH). unfold APS.in_hull. cbn [img_lo img_hi ASAN]. unfold BIMG_LO, BIMG_HI in Ha.
        apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
      pose proof (export_sound bsegs E (APS.hid ASAN argH E hs mo) FULL (kn hs) BIMG_LO BIMG_HI
                    (co_know _ _ _ _ _ _ _ _ _ _ _ HC) HIDrom HULLvis _ _ MJ PJ) as [HMF HPF].
      pose proof (proj1 (Forall_app _ _ _) HMF) as [HMFc _].
      pose proof (proj1 (Forall_app _ _ _) HPF) as [HPFc _].
      split; [exact HMF|]. split; [exact HPF|].
      (* [comment removed for export] *)
      split.
      { intros a b Hab. rewrite a_ro_addr.
        destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); [|reflexivity].
        destruct (Z.ltb_spec0 (bv_unsigned a) 0xc6000); [|reflexivity].
        exfalso. pose proof (mimg_cover bsegs V FULL both_mem_facts 0x10000 0xc6000 HMFc ltac:(vm_compute; reflexivity) (bv_unsigned a) ltac:(lia)) as X.
        unfold wa in X. rewrite Z_to_bv_bv_unsigned in X. congruence. }
      (* [comment removed for export] *)
      split.
      { pose proof (mwr_find bsegs V FULL both_mem_facts
                      (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 8388608
                      HMFc ltac:(vm_compute; reflexivity)) as W.
        cbn [zv] in W. fold V in W.
        replace (32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat) + -8388608) with (bv_unsigned sp - 8388608) in W by lia.
        cbn [en0 en_sp].
        apply wr_at_stk; [replace (bv_unsigned sp - (bv_unsigned sp - 8388608)) with 8388608 by lia; exact W|].
        intros a Ha. apply ref_find_segment_none; [lia|]. lia. }
      (* [comment removed for export] *)
      split.
      { intros a Ha. cbn [en0 inp0 AsanInit.inp mkProcInput en_sp en_draw in_argv in_envp in_uid in_hwcap]. apply Hhid.
        pose proof (AsanInit.usp_fit BPH sp rdraw argv envp uid hw Hfit) as F.
        pose proof (AsanInit.W_range BPH sp rdraw argv envp uid hw Hva Hve) as (W1 & W2 & W3).
        pose proof (AsanInit.len_av BPH sp rdraw argv envp uid hw Hva) as LA. pose proof (AsanInit.len_ev BPH sp rdraw argv envp uid hw Hve) as LE.
        unfold hidden_arg, Wblk in Ha. cbn [en0 inp0 AsanInit.inp mkProcInput en_sp en_draw in_argv in_envp in_uid in_hwcap] in Ha.
        try rewrite <- bph_BPH in Ha.
        unfold argH0. rewrite wa_unsigned by lia.
        apply orb_true_intro. destruct Ha as [Ha|Ha]; [left|right]; apply andb_true_intro; split;
          first [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
      (* [comment removed for export] *)
      pose proof (var_ranges_sound BSEGS E _ (kn hs) (co_know _ _ _ _ _ _ _ _ _ _ _ HC)) as HVR.
      destruct VJ as [VJa VJg].
      pose proof (vis_match_sound E _ _ _ HVR VJa) as HVISa. pose proof (vis_match_sound E _ _ _ HVR VJg) as HVISg.
      pose proof (Forall2_app HVISa HVISg) as HVIS. change (both_vis_app ++ both_ghost) with both_vis in HVIS.
      pose proof (ledger_den_sound E _ HVR _ _ _ LJ (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)) as HLD.
      pose proof (ledger_kinds_sound E _ HVR _ _ mo LJ (co_none _ _ _ _ _ _ _ _ _ _ _ HC) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC)) as HKD.
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
        (* [comment removed for export] *)
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
          replace (APS.in_hull ASAN a) with false.
          2:{ symmetry. unfold APS.in_hull. cbn [img_lo img_hi ASAN]. apply andb_false_iff. right. apply Z.ltb_ge. unfold bshadow in Hsh. lia. }
          replace (atop mo <=? a) with false by (symmetry; apply Z.leb_gt; rewrite ATOP; unfold bshadow in Hsh; lia).
          cbn [orb]. replace (APS.in_allow ASAN E hs a) with false; [destruct (APS.in_ivs _ _ && _)%bool; reflexivity|].
          symmetry. unfold APS.in_allow. apply orb_false_intro.
          + (* [comment removed for export] *)
            unfold APS.in_vis. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Xp).
            apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
            destruct (Forall2_In_l _ _ _ _ HVISa Hp) as (bn & Hbn & E1 & E2 & E3). unfold APS.uE in X1, X2. rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2. fold V in X1, X2.
            apply (shad_clear_sound V _ both_pure_facts bn a HVRp HPFc (proj1 (forallb_forall _ _) CLRv bn Hbn) HSS). lia.
          + (* [comment removed for export] *)
            unfold APS.in_sh. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Xp).
            apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. unfold APS.sh_lo, APS.sh_hi, APS.uE in X1, X2.
            destruct (Forall2_In_l _ _ _ _ HVISa Hp) as (bn & Hbn & E1 & E2 & E3). rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2. fold V in X1, X2.
            apply Hnv. exists bn. split; [exact Hbn|]. change (shadow_off ASAN) with ASHOFF in X1, X2. lia.
        - exact Kmap.
        - apply Bool.not_true_iff_false. intros X. apply Kna. apply (proj1 (in_ivs_APS _ _)). exact X.
        - exact Klz.
        - (* [comment removed for export] *)
          unfold APS.in_ghost. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Xp).
          apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. unfold APS.uE in X1, X2.
          destruct (Forall2_In_l _ _ _ _ HVISg Hp) as (bn & Hbn & E1 & E2 & E3). rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2. fold V in X1, X2.
          apply (shad_clear_sound V _ both_pure_facts bn a HVRp HPFc (proj1 (forallb_forall _ _) CLRg bn Hbn) HSS). lia. }
      (* [comment removed for export] *)
      pose proof (allowA_allow_of ASAN E _ _ HVIS) as HAL. change (shadow_off ASAN) with ASHOFF in HAL. change (flat_map (allow1 ASAN E) (a_vis hs ++ a_ghost hs)) with (allowA ASAN E hs) in HAL.
      fold V in HAL.
      pose proof CONSTS as (Ct & Cy & Ce & Ca).
      assert (USPW : vm_init_sp (m_vmmaps mo) = sp) by (apply bv_eq; exact TOP).
      destruct HC. cbn [inp0 AsanInit.inp in_fs in_image_fs in_tmp en0 en_sp]. rewrite Hfd in co_fds0. rewrite Hbrk0 in co_brk0.
      constructor.
      + exact co_halt0.
      + exact co_fds0.
      + exact co_fs0.
      + exact co_res0.
      + exact co_limit0.
      + rewrite co_brk0. cbn [edenot]. symmetry. apply Z_to_bv_bv_unsigned.
      + rewrite co_brk0 in co_sbrk0. cbn [edenot] in co_sbrk0. exact co_sbrk0.
      + exact USPW.
      + split; [exact LO|]. split; [lia| exact Hal].
      + exact HLD.
      + exact HKD.
      + apply seps_ivs_sep. exact co_seps0.
      + eapply Forall_impl; [|exact co_bounds0]. cbv beta. intros iv (B1 & B2 & B3 & B4 & B5 & B6).
        unfold hull_clear in B5. cbn [img_lo img_hi ASAN] in B5. rewrite ATOP in B6. unfold BIMG_LO, BIMG_HI. repeat split; assumption.
      + eapply Forall_impl; [|exact co_lazyb0]. cbv beta. intros iv (B5 & B6).
        unfold hull_clear in B5. cbn [img_lo img_hi ASAN] in B5. rewrite ATOP in B6. unfold BIMG_LO, BIMG_HI. split; assumption.
      + destruct co_wf0 as (_ & Wn & _). apply Forall_forall. intros iv Hiv. exact (Wn iv Hiv).
      + intros z Hz. apply (proj1 (in_ivs_APS _ _)). apply co_nasub0. apply (proj2 (in_ivs_APS _ _)). exact Hz.
      + exact co_napos0.
      + rewrite <- Ct. exact co_totsz0.
      + rewrite <- Ce. exact co_eager0.
      + rewrite <- Ca, <- HAL. exact co_abytes0.
      + rewrite <- HAL. pose proof (minv_budget _ _ co_minv0) as B. rewrite co_limit0 in B. exact B.
      + rewrite <- HAL. exact (APS.A_wf_allowA ASAN HS_both2 XN0 XE0 XB0 NX0 E hs).
      + exact (minv_nodup _ _ co_minv0).
      + intros p Hp. split; [exact (minv_aligned _ _ co_minv0 p Hp)|]. split; [exact (minv_lazy _ _ co_minv0 p Hp)|].
        rewrite <- HAL. apply page_allowedb_aallowed. exact (minv_allowed _ _ co_minv0 p Hp). }
    - (* [comment removed for export] *)
      unfold cfg_of. split; [|reflexivity]. cbn [cfg_ms].
      split; [| split; [apply regs_eqv_refl| repeat split; reflexivity]].
      cbn [ms_regs AS.PropExec.mkst MS].
      intros r Hr. destruct (OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.RegsEquiv.reg_of_nat r) as (n & -> & Hn).
      pose proof (is_x0_of_nat n Hn Hr) as Hn1.
      rewrite (regs_ok_nth E _ R (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) n Hn1). rewrite reg_get_mkR by exact Hn1. rewrite Hregs.
      destruct n as [|n]; [cbv in Hr; discriminate|].
      cbn [en0 inp0 AsanInit.inp mkProcInput en_sp in_argv in_envp].
      do 31 (destruct n as [|n];
        [ cbn [nth HS_both2_1 a_ss s_regs];
          first [ reflexivity
                | symmetry; apply Z_to_bv_bv_unsigned
                | erewrite <- (zexp_of_sound E) by reflexivity; cbn [zv]; fold V; unfold BMAIN, BRA, BGP, BTP; f_equal; lia ]
        |]). lia.
  Qed.

  (* [comment removed for export] *)
  Theorem bmain_bridge_1 : forall E R FULL mo,
    cs_ok BSEGS ASAN LIM SINV argH (fs_seed_tmp fs tmp) E HS_both2_1 R FULL mo ->
    exists ms, cfg_eqv (cfg_of BSEGS R (pc HS_both2_1) FULL mo) (mkCfg ms mo) /\ bmain_at en0 inp0 ms mo.
  Proof.
    exact (bmain_bridge_w true HS_both2_1 eq_refl eq_refl eq_refl eq_refl both_mem_facts_justified_w1 both_pure_facts_justified_w1
             both_vis_justified_w1 both_ledger_justified_w1 both_consts_w1).
  Qed.
  Theorem bmain_bridge_2 : forall E R FULL mo,
    cs_ok BSEGS ASAN LIM SINV argH (fs_seed_tmp fs tmp) E HS_both2_2 R FULL mo ->
    exists ms, cfg_eqv (cfg_of BSEGS R (pc HS_both2_2) FULL mo) (mkCfg ms mo) /\ bmain_at en0 inp0 ms mo.
  Proof.
    exact (bmain_bridge_w false HS_both2_2 eq_refl eq_refl eq_refl eq_refl both_mem_facts_justified_w2 both_pure_facts_justified_w2
             both_vis_justified_w2 both_ledger_justified_w2 both_consts_w2).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variable T : TSet.
  Hypothesis T_nil : T [].
  Hypothesis MAINA : forall ms mo, bmain_at en0 inp0 ms mo -> srealizes bsegs (mkCfg ms mo) T.

  Theorem both_main_boot :
    srealizes bsegs (init_config bsegs Asan.M.init_pc b_phdrs sp brk0 mbase rdraw target_alloc_limit inp0) T.
  Proof.
    change bsegs with BSEGS. change b_phdrs with BPH. change target_alloc_limit with AsanInit.LIMIT.
    apply (both_boot sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw (fun _ _ => T)).
    - intros; reflexivity.
    - intros; exact T_nil.
    - intros h ch Hh E R FULL mo HC. destruct h as [|[|[|h]]]; cbn in Hh; try discriminate Hh; injection Hh as <-.
      + destruct (bmain_bridge_1 E R FULL mo HC) as (ms & Heqv & Hat).
        apply (srealizes_eqv BSEGS (mkCfg ms mo) T (MAINA ms mo Hat)). apply cfg_eqv_sym. exact Heqv.
      + destruct (bmain_bridge_2 E R FULL mo HC) as (ms & Heqv & Hat).
        apply (srealizes_eqv BSEGS (mkCfg ms mo) T (MAINA ms mo Hat)). apply cfg_eqv_sym. exact Heqv.
  Qed.
End Bridge.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem both_side_ok : forall T : tfam,
  (forall en inp, valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp ->
      T inp en [] /\ forall ms mo, bmain_at en inp ms mo -> srealizes bsegs (mkCfg ms mo) (T inp en)) ->
  side_ok bsegs b_init_pc b_phdrs target_alloc_limit T.
Proof.
  intros T HT. apply side_ok_of_srealizes. intros [sp brk0 mbase rdraw] inp Hv Hi.
  destruct (HT _ _ Hv Hi) as [Tnil MAINA].
  rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in Hv.
  destruct Hv as (Hsp & Hbrk & Hmb & Hfit).
  pose proof Hi as (Hva & Hve & Hfs & Hkeys & [Huid Hgid] & Hnof & Hsigm & Hhw & Hvasz & Hurnd).   (* [comment removed for export] *)
  destruct inp as [argv envp fs stdin uid gid groups net nof sigm hw abt vasz urnd tmp].
  cbn in Hfit, Hva, Hve, Hfs, Huid, Hgid, Hhw, Hvasz. subst vasz.
  exact (both_main_boot sp brk0 mbase rdraw argv envp fs stdin uid gid groups net nof sigm hw abt urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw _ Tnil MAINA).
Qed.
