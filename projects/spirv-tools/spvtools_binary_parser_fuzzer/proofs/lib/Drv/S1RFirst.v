(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's mmap base; the model's channel reader as a premise of the writes; the first malloc's auxv read off the launch's entry block; the writable stack is the launch's 6144513 bytes below sp0). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk SimInv ShapeAlg ShapeLaws Nodes MmapSim FileSim AgentLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame RefNodes RefMemcpyLib RefLayout Hoare MemSplit SRealizes SNodes AllocCeil RunRandom LibIface LibBudget LibEff S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import SymDriveS2 RunsLib S1CxxTable StaticsGen S1Statics S1SpecConsts S1Spec S1BootDefs S1Start S1StartupFacts S1CxxLink S1MainEntry S1MainEntryN S1SxKn S1PilotOOM_defs S1KnCut2
  S1Cells S1AddrFacts S1RBase S1RKn DrvMallocT S1RFront S1_code_6545c_66064.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac reg_in :=
  first [ solve [ cbn [In]; repeat first [ left; reflexivity | right ] ]
        | solve [ cbn [In]; let HH := fresh "HH" in intros HH;
                  repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH ]
        | cbv; tauto ].

Lemma at_random_hi8 : forall r : bv 128,
  firstn 8 (skipn 8 (at_random_bytes r)) = word_to_le_bytes 8 (Z_to_bv 64 (rr_secret_of r)).
Proof.
  intros r. unfold rr_secret_of, word_to_le_bytes. rewrite Z_to_bv_bv_unsigned.
  pose proof (bv_unsigned_in_range _ r) as Hr. unfold bv_modulus in Hr.
  assert (Hu : bv_unsigned (bv_extract 64 64 r) = Z.shiftr (bv_unsigned r) 64).
  { rewrite bv_extract_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small.
    rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|]. change (2 ^ Z.of_N 64 * 2 ^ Z.of_N 64)%Z with (2 ^ Z.of_N 128)%Z. lia. }
  rewrite Hu. cbn [at_random_bytes skipn firstn Z_to_le_bytes].
  rewrite !Z.shiftr_shiftr by lia.
  repeat f_equal; apply bv_eq; rewrite bv_extract_unsigned, Z_to_bv_unsigned; reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition ivs_kimg (kn : list kentry) (ivs : list (Z * Z)) : bool :=
  forallb (fun iv : Z * Z => existsb (is_kimg_cov (fst iv) (snd iv - fst iv)) kn) ivs.

Section FXALL.
Context {fx : FPState}.

Lemma first_ok_steps : forall regs mem rom (p : Z),
  (0 < p < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 p -> getr regs 21 = Z_to_bv 64 65536 ->
  exists regs',
    msteps RSEGS (mkst regs (0x6563c : word) mem rom) (mkst regs' (0x656b4 : word) mem rom)
    /\ getr regs' 9 = Z_to_bv 64 p /\ getr regs' 19 = Z_to_bv 64 0 /\ getr regs' 22 = Z_to_bv 64 0xee4e9
    /\ (forall r : reg, r <> 9 -> r <> 10 -> r <> 19 -> r <> 22 -> r <> 23 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom p Hp Ha0 H21.
  eexists. split.
  - stepb_ft F_655fc D_655fc ltac:(rewrite Ha0; apply c_eq_0_false; rewrite u_small by lia; lia).
    stepn F_65600 D_65600.
    stepn F_65604 D_65604.
    stepn F_65608 D_65608.
    stepn F_6560c D_6560c.
    stepb_tk F_65610 D_65610 ltac:(rewrite H21; cond_compute).
    stepn F_65634 D_65634.
    stepn F_65638 D_65638.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try (rewrite Ha0; reflexivity); try (apply bv_eq; reflexivity).
    intros r H9 H10 H19 H22 H23. rewrite !getr_other by assumption. reflexivity.
Qed.

Lemma seg_rom_high : forall x : word, (0x122000 <= bv_unsigned x)%Z -> seg_rom RSEGS x = None.
Proof.
  intros x Hx. unfold seg_rom, memory_read. rewrite S1AddrFacts.fseg_off; [reflexivity | cbn; lia | lia].
Qed.

Lemma rdn_high_defined : forall M n (a : word) bs (x : word),
  rdn RSEGS M a n = Some bs -> (0x122000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n)%Z -> M x <> None.
Proof.
  intros M n. induction n as [|n IH]; intros a bs x H Ha Hn Hx; [lia|].
  cbn [rdn] in H. destruct (M a) as [b|] eqn:Ea.
  - destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [E|NE].
    + assert (x = a) by (apply bv_eq; exact E). subst x. rewrite Ea. discriminate.
    + destruct (rdn RSEGS M (a + 1) n) as [rest|] eqn:Er; [|discriminate].
      assert (U1 : bv_unsigned (a + 1)%bv = (bv_unsigned a + 1)%Z).
      { rewrite (w_add_nat a 1) || idtac. apply u_small || (rewrite u_small; [reflexivity|]); lia. }
      apply (IH (a + 1)%bv rest x Er); rewrite ?U1; lia.
  - rewrite seg_rom_high in H by lia. discriminate.
Qed.

Section First.
  Context {AC : AllocCeiling} {RRND : RunRandom} {AMB : Amb}.
  Variable MI : MallocIface SEGS L.
  Variable AINV0 : AS MI -> LibIface.mem -> Model -> Prop.
  Variables (TIGHT FRESH44 : AS MI -> Prop).
  Hypothesis DM : drv_mallocT MI AINV0 TIGHT FRESH44.

  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rdraw : EntryDraw.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
    (* LPS 75d69e00: [main_entry] takes the run's whole ProcInput and the mmap base
     in place of (argv, envp, uid, hwcap).  [mkProcInputC] (Amb.v:42) is the very
     input this Section's own conclusion runs -- [in_argv]/[in_envp]/[in_uid]/
     [in_hwcap] of it reduce to exactly the four the old spelling named -- so
     naming it here is the same statement, not a narrower one. *)
  Local Notation INP := (mkProcInputC [a0s; path] envv fs0 stdin0) (only parsing).
  Hypothesis ME : main_entry sp0 rdraw INP mbase tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.

  Variable mo1 : Model.
  Hypothesis M1v : m_vmmaps mo1 = m_vmmaps (S1RFront.model0 sp0 a0s path envv tid rdraw brk mbase fs0 stdin0).
  Hypothesis M1l : m_vm_lazy mo1 = [].
  Hypothesis M1h : m_halted mo1 = None.
  Hypothesis M1m : m_vm_materialized mo1 = [].
  Hypothesis M1fs : m_fs mo1 = fs0.
  Hypothesis M1fd2 : fd_lookup (m_fds mo1) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  (* LPS 727298f3: the heap invariant reads the kernel build (the vDSO pair, the
     placement's THP setting), so carrying it from [model0] to [mo1] needs the kernel too. *)
  Hypothesis M1k : m_kernel mo1 = m_kernel (S1RFront.model0 sp0 a0s path envv tid rdraw brk mbase fs0 stdin0).
  (* LPS 727298f3: the far end's reader bit, which [rst] carries round the read loop. *)
  Hypothesis M1r : m_channel_reader mo1 = true.

  Hypothesis HAC : (alloc_ceiling = bv_unsigned sp0 - 8388608)%Z.
  Hypothesis HRR : (rr_canary = bv_unsigned (canary rdraw))%Z.
  Hypothesis HRS : (rr_secret = rr_secret_of (ed_random rdraw))%Z.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  #[local] Notation model0 := (S1RFront.model0 sp0 a0s path envv tid rdraw brk mbase fs0 stdin0).
  #[local] Notation model1 := mo1.
  #[local] Notation P1 := (p1 a0s path envv rdraw).

  Lemma rimg_missb :
    Forall (fun iv : Z * Z => D_main_missb (fst iv) (Z.to_nat (snd iv - fst iv)) = true) rimg_ivs.
  Proof. unfold rimg_ivs. repeat (apply Forall_cons; [vm_compute; reflexivity|]). apply Forall_nil. Qed.

  Lemma mem0_clear : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x122000)%Z ->
    img_clear mem0 lo hi.
  Proof.
    intros lo hi Hb Hle Hhi i Hi. destruct (missb_parts lo _ Hb) as (_ & _ & Hlo0 & _).
    rewrite (main_entry_mem_data sp0 rdraw INP mbase tid regs0 mem0 ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none sp0 INP tid rdraw Hva).
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  Qed.

  Lemma mem0_rimg : Forall (fun iv => img_clear mem0 (fst iv) (snd iv)) rimg_ivs.
  Proof.
    apply Forall_forall. intros [lo hi] Hin. cbn [fst snd].
    pose proof (proj1 (Forall_forall _ _) rimg_missb _ Hin) as Hb. cbn [fst snd] in Hb.
    pose proof (proj1 (Forall_forall _ _) rimg_facts _ Hin) as F. cbn [fst snd] in F.
    apply mem0_clear; [exact Hb | lia | lia].
  Qed.

  Ltac Dcell L := unfold cell; apply (main_entry_rdn_D sp0 INP tid rdraw SPlo mbase regs0 mem0 ME); [lia | cbn; lia | apply (L sp0 INP tid rdraw Hva)].

  Lemma mem0_main_mem : drv_main_mem mem0.
  Proof.
    pose proof (main_know_ok sp0 a0s path envv tid rdraw regs0 mem0 Hva Hve Hvsp Htid ME) as HK0.
    constructor; unfold LIBC.
    - apply mem0_clear; [vm_compute; reflexivity | lia | lia].
    - apply mem0_clear; [vm_compute; reflexivity | lia | lia].
    - Dcell D_main_cdt.
    - unfold cell. krd HK0 0x120949%Z 1%nat H. exact H.
    - unfold cell. krd HK0 0x12094a%Z 1%nat H. exact H.
    - unfold cell. krd HK0 0x12094b%Z 1%nat H. exact H.
    - unfold cell. krd HK0 0x12094c%Z 4%nat H. exact H.
    - exists (bv_unsigned (auxvp sp0 a0s path envv)). split; [apply u64_range|].
      unfold cell. rewrite Z_to_bv_bv_unsigned. Dcell D_main_auxv.
    - unfold cell. krd HK0 0x120958%Z 8%nat H. exact H.
    - Dcell D_main_tlssize.
    - Dcell D_main_tlsalign.
    - unfold cell. krd HK0 0x120970%Z 8%nat H. exact H.
    - Dcell D_main_pagesize.
    - intros i Hi. exists (Z_to_bv 8 0). split; [|reflexivity].
      assert (Hk : exists k : nat, (k < 48)%nat /\ i = Z.of_nat k) by (exists (Z.to_nat i); split; lia).
      destruct Hk as (k & Hk & ->).
      do 48 (destruct k as [|k];
        [ lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
            let a' := eval vm_compute in a in replace a with a' by reflexivity;
            let H := fresh in krd HK0 a' 1%nat H; exact H end
        | ]). lia.
    - unfold cell. rewrite HRR, Z_to_bv_bv_unsigned. exact (main_entry_guard sp0 INP tid rdraw Hva SPlo mbase regs0 mem0 ME RSEGS).
    -   intros w Hi Hnrw.
      assert (Hw : (0x10000 <= bv_unsigned w < 0xee000)%Z).
      { apply img_iff in Hi. destruct (Z.lt_ge_cases (bv_unsigned w) 0xee000); [lia|]. exfalso. apply Hnrw.
        exists 0xee000%Z, 0x122000%Z. split; [left; reflexivity | lia]. }
      rewrite <- (Z_to_bv_bv_unsigned 64 w). apply (mem0_clear 0x10000 0xee4a0); [vm_compute; reflexivity | lia | lia | lia].
  Qed.

  Lemma model0_main_model : drv_main_model model0.
  Proof.
    destruct Hbrk as (Hb1 & Hb2 & Hb3).
    assert (RT : reserved_top (segments_reserved RSEGS) = 0x122000%Z) by (vm_compute; reflexivity).
    constructor.
    - reflexivity.
    - reflexivity.
    (* 08b1429: [State.init_model] ends the reserved ledger with the vDSO pair *)
    - exact (vm_reserved_init_model (segments_reserved RSEGS) brk mbase sp0 LIM
               (mkProcInputC [a0s; path] envv fs0 stdin0)).
    - reflexivity.
    - exact Hbrk.
    - change (vm_start_brk (m_vmmaps model0)) with brk. rewrite HAC. unfold brk_aslr_max in Hb2. lia.
    - change (vm_limit (m_vmmaps model0)) with LIM. apply LIM_ge.
    - reflexivity.
    - reflexivity.
  Qed.

  Section AtCall.
    Variables (vals : list word) (R : bvmap 5 word) (M : word -> option byte).
    Hypothesis HL : length vals = 38%nat.
    Hypothesis P0 : vals_ev vals 0 = sp0.
    Hypothesis P2 : vals_ev vals 2 = P1.
    Hypothesis P3 : vals_ev vals 3 = auxvp sp0 a0s path envv.
    Hypothesis P4 : vals_ev vals 4 = rnd rdraw.
    Hypothesis P5 : vals_ev vals 5 = tid.
    Hypothesis HK : know_ok RSEGS (ENV a0s path vals) M knA.
    Hypothesis HA : above_sp0 sp0 mem0 M.
    Hypothesis HG : mem_grows mem0 M.
    Hypothesis HO : forall a : word, (bv_unsigned a < bv_unsigned sp0 - 8388608)%Z \/ (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a.

    Lemma path_facts :
      rdn RSEGS M (Z_to_bv 64 (bv_unsigned P1)) (length path + 1) = Some (path ++ [Z_to_bv 8 0])
      /\ (bv_unsigned sp0 <= bv_unsigned P1)%Z /\ (bv_unsigned P1 + Z.of_nat (length path) + 1 < 2 ^ 63)%Z.
    Proof.
      clear HL P0 P2 P3 P4 P5 HK HG HO.
      (* [S1MainEntry.main_str] reads the launch facts from [ME]; [Hve] is not a parameter of it. *)
      destruct (main_str sp0 a0s path envv tid rdraw regs0 mem0 Hva Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
      cbn [nth] in Sr, Slo, Shi, Slen. fold (p1 a0s path envv rdraw) in Sr, Slo, Shi.
      rewrite Z_to_bv_bv_unsigned. split; [|lia].
      rewrite <- Sr. apply rdn_ext; [rewrite Nat2Z.inj_add; cbn [Z.of_nat Pos.of_succ_nat]; lia|].
      intros x Hx. apply HA. lia.
    Qed.

    Lemma rmem_at_call : rmem (bv_unsigned sp0) (bv_unsigned tid) (bv_unsigned P1) path M.
    Proof.
      clear HL P2 P3 P4.
      pose proof path_facts as (Sr & Slo & Shi).
      constructor.
      - apply Forall_forall. intros [lo hi] Hin. cbn [fst snd].
        pose proof (proj1 (Forall_forall _ _) rimg_facts _ Hin) as F. cbn [fst snd] in F.
        pose proof (proj1 (Forall_forall _ _) mem0_rimg _ Hin) as C. cbn [fst snd] in C.
        intros i Hi. rewrite HO by (rewrite u_small by lia; lia). apply C. exact Hi.
      - unfold cell. rewrite Z_to_bv_bv_unsigned.
        rewrite <- (main_entry_tid sp0 INP tid rdraw Hva SPlo mbase regs0 mem0 ME RSEGS).
        symmetry. apply rdn_ext; [rewrite u_small by lia; cbn; lia|]. intros x Hx. rewrite u_small in Hx by lia. symmetry. apply HO. cbn in Hx. lia.
      - unfold cell. krd HK 0x1005f0%Z 8%nat H. exact H.
      - unfold cell. krd HK 0x100688%Z 8%nat H. exact H.
      - eapply pins_same; [exact (main_entry_pins_sx sp0 rdraw INP mbase tid regs0 mem0 SPlo ME)|].
        intros a Ha. pose proof (D_RD_rw _ Ha) as (lo & hi & Hin & Hr). cbn in Hin. destruct Hin as [E|[]]. injection E as <- <-.
        apply HO. lia.
      - constructor; unfold cell;
          lazymatch goal with |- rdn _ _ (Z_to_bv 64 (bv_unsigned sp0 - ?k)) 8 = _ =>
            let H := fresh in
            krdv HK 0%nat (- k)%Z 8%nat H; [apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia|];
            unfold adenot, v_addi in H; cbn [a_base a_off edenot ev ENV] in H; rewrite P0 in H;
            replace (bv_unsigned sp0 + - k)%Z with (bv_unsigned sp0 - k)%Z in H by lia; rewrite H;
            first [ reflexivity
                  | rewrite alu_add; unfold v_add; do 3 f_equal; apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; cbn [bv_unsigned Z_to_bv]; rewrite ?Zplus_mod_idemp_r; f_equal; lia
                  | idtac ] end.
      - intros d m Hd Hm. eapply store_ok_mono; [exact HG|].
        apply (main_entry_store_ok_win sp0 rdraw INP mbase tid regs0 mem0 ME);
          rewrite ?stack_window_depth_val in *; rewrite u_small by lia;
          try unfold wok_lo; try unfold stack_window_reach; try unfold stack_max_size; lia.
      - exact Sr.
    Qed.
  End AtCall.

  #[local] Open Scope Z_scope.

  Record first_post (p : Z) (A : AS MI) (R : bvmap 5 word) (M : word -> option byte) (mo : Model) : Prop := {
    fp_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
    fp_gp : getr R 3 = Z_to_bv 64 0x10800;
    fp_tp : getr R 4 = Z_to_bv 64 0x1006b8;
    fp_s0 : getr R 8 = Z_to_bv 64 2;
    fp_s1 : getr R 9 = Z_to_bv 64 p;
    fp_s2 : getr R 18 = Z_to_bv 64 (bv_unsigned P1);
    fp_s3 : getr R 19 = Z_to_bv 64 0;
    fp_s4 : getr R 20 = Z_to_bv 64 3;
    fp_s5 : getr R 21 = Z_to_bv 64 65536;
    fp_s6 : getr R 22 = Z_to_bv 64 0xee4e9;
    fp_mem : rmem (bv_unsigned sp0) (bv_unsigned tid) (bv_unsigned P1) path M;
    fp_abs : rabs MI A M mo;
    fp_tight : TIGHT A;
    fp_live : live MI A = [(p, 65536%Z)];
    fp_t8 : exists t8, rdn RSEGS M (Z_to_bv 64 (bv_unsigned P1 + Z.of_nat (length path))) 8 = Some t8;
    fp_fds : m_fds mo = m_fds mo1;
    fp_rdr : m_channel_reader mo = true;
    fp_fs : m_fs mo = fs0
  }.

  Theorem first : forall KBODY,
    (forall p A R M mo, first_post p A R M mo ->
       srealizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x656b4) M (seg_rom RSEGS)) mo) KBODY) ->
    at_malloc1 sp0 a0s path envv tid rdraw mem0 mo1 KBODY.
  Proof.
    intros KBODY HLOOP vals R M HL P0 P1v P2 P3 P4 P5 HR HK HA HG HO.
    pose proof (path_facts M HA) as (Sr & Slo & Shi).
    edestruct (main_strN sp0 [a0s; path] envv tid rdraw regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(cbn; lia)) as (_ & _ & Shi2 & Slen & t8 & Ht8).
    cbn [nth] in Ht8, Shi2, Slen. fold (p1 a0s path envv rdraw) in Ht8, Shi2.
    assert (Ht8M : rdn RSEGS M (Z_to_bv 64 (bv_unsigned P1 + Z.of_nat (length path))) 8 = Some t8).
    { rewrite <- Ht8. apply rdn_ext; [rewrite u_small by lia; lia|]. intros x Hx. rewrite u_small in Hx by lia. apply HA. lia. }
    pose proof (rmem_at_call vals M P0 HK HA HG HO) as RM.
    destruct (dm_init _ _ _ _ DM mem0 model0 mem0_main_mem model0_main_model) as (A0 & AI0 & LV0 & CP0 & BG0 & OWN0 & TI0 & FR0).
    pose proof (dm_owned0 _ _ _ _ DM) as OWNC. pose proof HAC as Hcv. pose proof ac_bounds_lit as Hcb.
    assert (OWNC0 : forall a, owned MI A0 a -> ~ in_ranges (ly_img L) a -> (0 < a < alloc_ceiling)%Z)
      by (intros a Ho Hni; exact (OWNC A0 mem0 model0 a AI0 Ho Hni)).
    assert (AI1 : AINV0 A0 M model1).
    { apply (dm_frame0 _ _ _ _ DM A0 mem0 M model0 model1 AI0); [ | exact HG | exact M1v | rewrite M1l; reflexivity | exact M1k].
      intros a Ho. apply HO. pose proof (u64_range a).
      destruct (Classical_Prop.classic (in_ranges (ly_img L) (bv_unsigned a))) as [Hi|Hni].
      - apply img_iff in Hi. left. lia.
      - pose proof (OWNC0 _ Ho Hni). left. lia. }
    pose proof (dm_consts _ _ _ _ DM) as [MSc BIGc NMAXc RBc SCg SCn].
    pose proof (auxvp_u sp0 a0s path envv) as AU.
    repeat match type of AU with ?P -> _ => specialize (AU ltac:(assumption)) end. destruct AU as [Hau Hab].
    epose proof (rnd_u2 sp0 a0s path envv tid rdraw regs0 mem0) as RU.
    repeat match type of RU with ?P -> _ => specialize (RU ltac:(eassumption)) end. destruct RU as (Hr1 & Hr2 & Hr3 & Hr4).
    epose proof (rd_auxv_main sp0 a0s path envv tid rdraw regs0 mem0) as RA.
    repeat match type of RA with ?P -> _ => specialize (RA ltac:(eassumption)) end.
    eapply (dm_first _ _ _ _ DM fx A0 R M model1 65536 (bv_unsigned sp0 - 128) 0x6563c KBODY AI1).
    -
      (* LPS 727298f3: the launch's auxv ([StackLayout.auxv_entries]), read off the entry block
         ([S1MainEntry.rd_auxv_main]); [gpos] is a key's value position in it *)
      set (aw := fun j => bv_unsigned (nth j (RefLayout.auxv_words (launch_auxv INP sp0 mbase) RPH (0x6549c : word)
                   (in_uid INP) (in_gid INP) (in_hwcap INP)
                   (at_random_ptr sp0 (kb_rseq (in_kernel INP)) (in_argv INP) (in_envp INP))
                   (at_execfn_ptr (ed_top rdraw) (in_execfn INP))) (Z_to_bv 64 0))).
      set (gpos := fun k : Z => if Z.eqb k 33 then 1%nat else if Z.eqb k 40 then 3%nat else if Z.eqb k 41 then 5%nat
              else if Z.eqb k 42 then 7%nat else if Z.eqb k 43 then 9%nat else if Z.eqb k 44 then 11%nat
              else if Z.eqb k 45 then 13%nat else if Z.eqb k 46 then 15%nat else if Z.eqb k 47 then 17%nat
              else if Z.eqb k 51 then 19%nat else if Z.eqb k 17 then 25%nat else if Z.eqb k 7 then 33%nat
              else if Z.eqb k 8 then 35%nat else if Z.eqb k 9 then 37%nat else if Z.eqb k 13 then 43%nat
              else if Z.eqb k 14 then 45%nat else if Z.eqb k 31 then 51%nat else if Z.eqb k 27 then 53%nat
              else 55%nat).
      exists (bv_unsigned (auxvp sp0 a0s path envv)), (aw 27%nat), (aw 29%nat), (aw 31%nat), (aw 21%nat),
             (aw 23%nat), (aw 39%nat), (aw 41%nat), (aw 47%nat), (bv_unsigned (at_random_ptr sp0 (kb_rseq a_kernel) [a0s; path] envv)).
      split; [|split; [|split; [|split; [lia|split; [lia|split; [pose proof (u64_range (auxvp sp0 a0s path envv)); lia|split;[lia|split;[lia|]]]]]]]].
      + unfold cell, LIBC. rewrite Z_to_bv_bv_unsigned.
        assert (E0 : rdn RSEGS mem0 (Z_to_bv 64 (0x120948 + 8)) 8 = Some (word_to_le_bytes 8 (auxvp sp0 a0s path envv)))
          by (apply (main_entry_rdn_D sp0 INP tid rdraw SPlo mbase regs0 mem0 ME); [lia | cbn; lia | apply (D_main_auxv sp0 INP tid rdraw Hva)]).
        rewrite <- E0. apply rdn_ext; [rewrite u_small by lia; cbn; lia|]. intros x Hx. rewrite u_small in Hx by lia. apply HO. cbn in Hx. lia.
      + exists (kb_rseq a_kernel), (fun k => aw (gpos k)). intros i Hi.
        assert (Hj : (i < 2 * auxv_count (kb_rseq (in_kernel INP)))%nat)
          by (revert Hi; change (in_kernel INP) with a_kernel; unfold DrvMallocT.auxv_words, auxv_count;
              destruct (kb_rseq a_kernel); cbn [length app]; lia).
        assert (Hi58 : (i < 58)%nat) by (revert Hj; unfold auxv_count; destruct (kb_rseq (in_kernel INP)); lia).
        unfold cell.
        rewrite <- (rdn_ext RSEGS 8 mem0 M) by (try (rewrite u_small by lia; lia); intros x Hx; rewrite u_small in Hx by lia; symmetry; apply HO; lia).
        rewrite (RA i _ _ Hj eq_refl eq_refl). do 2 f_equal.
        assert (HLR : la_rseq (launch_auxv INP sp0 mbase) = kb_rseq a_kernel) by reflexivity.
        subst aw gpos. unfold RefLayout.auxv_words, auxv_entries. rewrite HLR.
        clear Hi Hi58. revert i Hj. change (in_kernel INP) with a_kernel.
        destruct (kb_rseq a_kernel); intros i Hj; cbn [auxv_count] in Hj.
        all: do 58 (destruct i as [|i];
               [cbn [nth flat_map app fst snd DrvMallocT.auxv_words Z.eqb Pos.eqb];
                first [rewrite Z_to_bv_bv_unsigned; reflexivity | reflexivity] |]).
        all: lia.
      +
        unfold cell. rewrite HRS.
        rewrite <- (rdn_ext RSEGS 8 mem0 M) by (try (rewrite u_small by lia; lia); intros x Hx; rewrite u_small in Hx by lia; symmetry; apply HO; lia).
        pose proof (Hr4 8%nat 8%nat ltac:(lia)) as H8. change (Z.of_nat 8) with 8%Z in H8. rewrite H8.
        rewrite at_random_hi8. reflexivity.
      + subst aw. repeat (apply Forall_cons; [apply u64_range|]). apply Forall_nil.
    - exact TI0.
    - reflexivity.
    - exact FR0.
    - exact LV0.
    - constructor; [exact M1h | exact M1l | exact M1m | rewrite M1v; rewrite HAC; reflexivity].
    - exact M1r.
    -   intros w Hi Hnrw.
      assert (Hw : (0x10000 <= bv_unsigned w < 0xee000)%Z).
      { apply img_iff in Hi. destruct (Z.lt_ge_cases (bv_unsigned w) 0xee000); [lia|]. exfalso. apply Hnrw.
        exists 0xee000%Z, 0x122000%Z. split; [left; reflexivity | lia]. }
      rewrite <- (Z_to_bv_bv_unsigned 64 w).
      pose proof (proj1 (Forall_forall _ _) (rm_img _ _ _ _ _ RM) (0x10000, 0xee4a0)%Z ltac:(unfold rimg_ivs; cbn; tauto)) as C.
      cbn [fst snd] in C. apply C. lia.
    -   constructor.
      + regv HR (1%bv : reg). reflexivity.
      + vm_compute. reflexivity.
      + lia.
      + regv HR (2%bv : reg). cbn [edenot ev ENV]. rewrite P0, alu_add. unfold v_add. apply bv_eq.
        rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, ?Zplus_mod_idemp_r; f_equal; lia.
      + rewrite Zminus_mod, SPal. reflexivity.
      + lia.
      + regv HR (3%bv : reg). reflexivity.
      + regv HR (4%bv : reg). reflexivity.
    - regv HR (10%bv : reg). reflexivity.
    - rewrite MSc. lia.
    - rewrite MSc. unfold stack_room.
      replace (Z_to_bv 64 (bv_unsigned sp0 - 128 - 8192)) with (Z_to_bv 64 (bv_unsigned sp0 - 8388608 + 8380288)) by (f_equal; lia).
      apply (rm_stack _ _ _ _ _ RM); lia.
    - rewrite MSc. intros a Ha Ho. unfold zwin in Ha.
      assert (Hni : ~ in_ranges (ly_img L) a) by (rewrite img_iff; lia).
      pose proof (OWNC0 a Ho Hni). lia.
    -
      intros A' R' M' mo' p AI' TI' MS' FS FDS RD1 KEPT A10 Hp LADD CP BG NEWT FR DEF.
      destruct LADD as [LV' _]. rewrite LV0 in LV'.
      destruct (ai_live_block MI A' M' mo' p 65536 AI' ltac:(rewrite LV'; left; reflexivity)) as (_ & Hal & _ & Hceil & Hby).
      assert (A21 : getr R' 21 = Z_to_bv 64 65536).
      { rewrite (KEPT 21%bv) by reg_in. regv HR (21%bv : reg). reflexivity. }
      destruct (first_ok_steps R' M' (seg_rom RSEGS) p ltac:(lia) A10 A21) as (R2 & MS2 & S9 & S19 & S22 & SK).
      replace (Z_to_bv 64 0x6563c) with (0x6563c%bv : word) by (apply bv_eq; reflexivity).
      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | exact MS2 |].
      replace (0x656b4%bv : word) with (Z_to_bv 64 0x656b4) by (apply bv_eq; reflexivity).
      rewrite MSc in FR.
      destruct (rstep_alloc0 MI (bv_unsigned sp0) (bv_unsigned tid) (bv_unsigned P1) path (conj (conj SPlo SPhi) SPal) (conj Slo Shi) HAC
                  A0 A' M M' mo' (fun a => p <= a < p + 65536)%Z (bv_unsigned sp0 - 128 - 8192) (bv_unsigned sp0 - 128)
                  RM OWN0 OWNC0 CP0 BG0 AI' MS' CP BG) as (RM' & RA' & AGR).
      + intros a Ho Hi. destruct (NEWT a Ho) as [H|[H _]]; [exact H | exfalso; exact (H Hi)].
      + intros a Ha. split; [lia|]. exact (proj1 (proj2 (Hby a Ha))).
      + lia.
      + lia.
      + intros a Hn. apply FR. intros [H|[H|[H|H]]]; apply Hn; [right; left | right; right; left | right; right; right; left | right; right; right; right]; exact H.
      + intros a Hd. destruct (DEF a Hd) as [H|[H|H]]; [left | right; left | right; right; right]; exact H.
      + apply (HLOOP p A' R2 M' mo'). constructor.
        * rewrite (SK 2%bv) by (intros E; discriminate E). rewrite (KEPT 2%bv) by reg_in.
          regv HR (2%bv : reg). cbn [edenot ev ENV]. rewrite P0, alu_add. unfold v_add. apply bv_eq.
          rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, ?Zplus_mod_idemp_r; f_equal; lia.
        * rewrite (SK 3%bv) by (intros E; discriminate E). rewrite (KEPT 3%bv) by reg_in. regv HR (3%bv : reg). reflexivity.
        * rewrite (SK 4%bv) by (intros E; discriminate E). rewrite (KEPT 4%bv) by reg_in. regv HR (4%bv : reg). reflexivity.
        * rewrite (SK 8%bv) by (intros E; discriminate E). rewrite (KEPT 8%bv) by reg_in. regv HR (8%bv : reg). reflexivity.
        * exact S9.
        * rewrite (SK 18%bv) by (intros E; discriminate E). rewrite (KEPT 18%bv) by reg_in. regv HR (18%bv : reg).
          cbn [edenot ev ENV]. rewrite P2, Z_to_bv_bv_unsigned. reflexivity.
        * exact S19.
        * rewrite (SK 20%bv) by (intros E; discriminate E). rewrite (KEPT 20%bv) by reg_in. regv HR (20%bv : reg). reflexivity.
        * rewrite (SK 21%bv) by (intros E; discriminate E). exact A21.
        * exact S22.
        * exact RM'.
        * exact RA'.
        * exact TI'.
        * exact LV'.
        * exists t8. rewrite <- Ht8M. apply rdn_ext; [rewrite u_small by lia; lia|]. intros x Hx. rewrite u_small in Hx by lia.
          apply FR. intros [H|[H|[H|H]]].
          -- destruct (NEWT _ H) as [Ho|[_ Hn]].
             ++ pose proof (OWNC0 _ Ho ltac:(rewrite img_iff; lia)). lia.
             ++ rewrite Z_to_bv_bv_unsigned in Hn.
                exact (rdn_high_defined M 8 _ t8 x Ht8M ltac:(rewrite u_small by lia; lia) ltac:(rewrite u_small by lia; lia)
                         ltac:(rewrite u_small by lia; lia) Hn).
          -- lia.
          -- unfold zwin in H. lia.
          -- exact (high_not_errno (bv_unsigned x) ltac:(lia) H).
        * exact FDS.
        * rewrite RD1. exact M1r.
        * rewrite FS. exact M1fs.
  Qed.

End First.
End FXALL.
