(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: both Walk sections take the launch's (inp, mb, entry, sp, brk, rnd) and entry_launch_ok_va in place of entry_stack_fits, usp_fit follows from length_entry_stack_image_launch, the argv strings start at usp + CHD + PAD, phase1 and phase2 are proved per CONFIG_RSEQ value from that value's entry table and the window floor sp - 6144512, and the #[using] attributes are dropped. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk StepTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanStartLoops. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanStartLoops.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlan AxSymExec3F. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import EntryKn StdioSymDrive.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import EntryGlue.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boot1_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* PORT NOTE (LPS f1006fe8 -> 75d69e00).  This section is re-threaded onto
   the entry-image tuple [(inp, mb, ph, entry, sp, rnd)] that
   E2/Musl/InitMem.v's [Section Layout] fixes and that Lib/EntryKn.v and
   Common/RefLayout__Common.v already use.  Three things moved.

   1. ARITY.  [Run.entry_stack_image] takes SIX arguments
      (75d69e00:theories/LinuxProcessSem/Run.v:1344) and
      [StackLayout.build_stack_bytes] TWELVE (StackLayout.v:483); argv,
      envp, the exec file name, uid, gid, hwcap and CONFIG_RSEQ are all
      read off [inp].  [Run.entry_stack_image_top] is DELETED -- the
      image IS the block -- so [bsb] is the image, as
      Common/RefLayout__Common.v:186 writes it.

   2. THE SPAN BOUND IS DELETED, NOT RE-THREADED.
      [PropExec.build_stack_bytes_within_span] no longer exists at
      75d69e00 and the model records WHY
      (75d69e00:theories/Common/PropExec.v:2527-2532): its bound is FALSE
      for the kernel's block, because an [arch_align_stack] pad near 4095
      bytes lays a block longer than [Run.entry_stack_span], and the span
      counts neither the strings' NULs nor the exec file name.
      Re-threading its arguments would restate a falsehood, so [usp_fit]
      is re-derived from the EQUALITY
      [PropExec.length_entry_stack_image_launch]
      (Common/PropExec__Common.v:2461, model theories/Common/PropExec.v:2534
      -- the image's length is EXACTLY [ed_top - sp]) together with the
      cap [Run.valid_stack_top_va] puts on [ed_top].  That is the route
      E2/Musl/AmoStep__Musl.v:236-245 and Lib/EntryKn.v:263-271 already
      take.  Its premise is [Run.entry_launch_ok_va], [valid_entry_va]'s
      fifth conjunct (Run.v:3723-3738), so the old [Hfit] is replaced by
      [Hlau] (which implies it, Run.entry_launch_ok_va_fits) and a [brk].

   3. THE STRING BASE.  [PN] was [usp + 8*argc + 8*envc + 184]: the old
      head's size, [160] for ten auxv pairs plus [24] for argc and the two
      NULs.  At 75d69e00 the head is [CHD = block_head_size rseq argv envp]
      (StackLayout.v:399, = E2/Musl/InitMem.v's [struct_size],
      InitMem.v:392), the sixteen AT_RANDOM bytes sit at the TOP of that
      head rather than above the strings, and the strings start at
      [usp + CHD + PAD] with [PAD = block_pad_len ...] (StackLayout.v:439).
      So [PN = usp + CHD + PAD], which is [EntryKn.u_e_str0]'s own value.
      NO byte count is named: [CHD] and [PAD] stay parametric in
      [kb_rseq (in_kernel inp)], which [Run.valid_input]'s conjunct 17
      leaves free, and the only bounds used are
      [Run.block_head_size_bounds] (Run.v:3889) and the two lemmas above.

   The [#[using=...]] attributes are dropped throughout, as Lib/EntryKn.v
   and Common/ArgvEnv__Common.v did at this revision: every one of them
   named section variables that no longer exist. *)
Section Walk.
  Variable inp : ProcInput.
  Variable mb : word.
  Variable entry : word.
  Variables sp brk : word.
  Variable rnd : EntryDraw.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mb rnd) inp.
  Hypothesis Huid : valid_id (in_uid inp).

  (* [comment removed for export] *)
  Definition E7 : env := E0 inp mb entry sp rnd.
  Definition MEM0 : word -> option byte := M0 inp mb PH entry sp rnd.
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length (in_argv inp)).
  Let envc := Z.of_nat (length (in_envp inp)).
  (* CHD and PAD: the head's size and the [arch_align_stack] pad.  Neither
     names a byte count and both are parametric in CONFIG_RSEQ.  The head
     is spelt [CHD] rather than [C] because two proofs below introduce a
     disjunct named [C] ([intros [C|C]]), and a section binder of that
     name would make those [intros] fail with "C is already used". *)
  Let CHD := Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)).
  Let PAD := Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) sp (ed_top rnd)
                         (in_argv inp) (in_envp inp) (in_execfn inp)).

  (* [comment removed for export] *)
  Definition above_ok (M : word -> option byte) : Prop :=
    forall x : word, usp <= bv_unsigned x -> M x = MEM0 x.

  Lemma usp_lo : 0x7fff80000000 <= usp.
  Proof. destruct Hsp as (H & _ & _). unfold sp_window_lo in H. exact H. Qed.
  Lemma usp_hi : usp <= 0x800000000000.
  Proof. destruct Hsp as (_ & H & _). unfold sp_window_hi in H. exact H. Qed.
  Lemma usp_al : usp mod 16 = 0.
  Proof. destruct Hsp as (_ & _ & H). exact H. Qed.
  Lemma len_av : 1 <= argc <= 1024. Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  Lemma len_ev : 0 <= envc <= 256. Proof. unfold envc. destruct Hve as [H _]. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma kx_ok : know_ok SEGS E7 MEM0 kx.
  Proof. unfold kx. constructor. Qed.

  (* the window floor is at or below sp - 6144512 ([StoreOk.stack_window_lo_valid]) *)
  Lemma Hwlo_sp : (stack_window_lo (in_kernel inp) mb rnd <= bv_unsigned sp - 6144512)%Z.
  Proof.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk.stack_window_lo_valid inp sp brk mb rnd Hvl Hlau) as B.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk.stack_window_reach, stack_max_size in B. lia.
  Qed.

  (* one entry table per CONFIG_RSEQ value; [rs] is the launch's own *)
  Lemma KN0_ok : forall rs, kb_rseq (in_kernel inp) = rs -> know_ok SEGS E7 MEM0 (KN0r rs).
  Proof.
    intros rs Hrs. unfold KN0r, E7, MEM0. eapply kn0_ok_b; try eassumption.
    all: first [ exact img_hull | exact rw_window | exact kx_ok | exact Hwlo_sp ].
  Qed.

  Lemma R0_ok : regs_ok E7 sr_init (R0 sp).
  Proof. unfold E7. apply regs0_ok. Qed.

  (* The image IS the block at 75d69e00, so [bsb] is the image. *)
  Let bsb := entry_stack_image inp mb PH entry sp rnd.
  Let stk := stack_to_mem sp (entry_stack_image inp mb PH entry sp rnd).

  (* See point 2 of the port note: the deleted span bound is replaced by
     the EQUALITY, not re-threaded. *)
  Lemma usp_fit : usp + Z.of_nat (length bsb) <= 2 ^ 47.
  Proof.
    unfold bsb.
    rewrite (length_entry_stack_image_launch Sv48 inp mb PH entry sp brk rnd Hlau).
    destruct Hlau as (Htop & _ & _).
    unfold valid_stack_top_va in Htop. destruct Htop as (_ & Htople & _).
    cbn [va_stack_top] in Htople. unfold usp, sp_window_hi in *. lia.
  Qed.
  Lemma Hhi' : bv_unsigned sp <= sp_window_hi. Proof. pose proof usp_hi. unfold sp_window_hi, usp in *. lia. Qed.
  Lemma Hlo' : sp_window_lo <= bv_unsigned sp. Proof. pose proof usp_lo. unfold sp_window_lo, usp in *. lia. Qed.

  Lemma rdn_above : forall M (a : word) n,
    above_ok M -> usp <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
    rdn SEGS M a n = rdn SEGS stk a n.
  Proof.
    intros M a n HA Ha Hn. unfold stk.
    rewrite <- (rdn_wrap_stack_above SEGS inp mb PH entry sp rnd a n) by (unfold usp in *; lia).
    apply rdn_ext; [exact Hn|]. intros x Hx. rewrite (HA x) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma above_ok_block : forall M log,
    above_ok M -> log_below_b 0%nat [] log = true -> above_ok (mem_denot E7 M log).
  Proof.
    intros M log HA Hb x Hx. pose proof usp_lo. pose proof usp_hi.
    rewrite (mem_denot_above E7 M log 0%nat [] usp x Hb); try (cbn [ev E7 E0 vals_ev vals0 nth]; unfold usp in *; lia).
    - apply HA. exact Hx.
    - constructor.
  Qed.

  (* [comment removed for export] *)
  Ltac vmc := lazymatch goal with |- log_below_b _ _ _ = true => vmeq_refl end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ENVP : Z := usp + 8 * argc + 16.

  Lemma ENVP_range : 0 <= ENVP /\ ENVP + 8 * Z.of_nat (length (in_envp inp)) + 16 < 2 ^ 64.
  Proof.
    assert (NW : usp + Z.of_nat (length bsb) < 2 ^ 64)
      by (unfold usp, bsb; eapply lay_bsb_nw; first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
    assert (AB : (auxv_off (in_argv inp) (in_envp inp)
                  + auxv_size (kb_rseq (in_kernel inp)) + 16 <= length bsb)%nat)
      by (unfold bsb; eapply auxv_off_bound; first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
    pose proof usp_lo. unfold auxv_off in AB. unfold ENVP, usp, argc. lia.
  Qed.

  Lemma envp_slot_eq : forall k,
    (sp + nat_to_word (envp_off (in_argv inp) + 8 * k))%bv = Z_to_bv 64 (ENVP + 8 * Z.of_nat k).
  Proof.
    intros k. apply bv_eq. rewrite word_add_nat. f_equal. f_equal. unfold envp_off, ENVP, usp, argc. lia.
  Qed.

  Lemma phase1_t : kb_rseq (in_kernel inp) = true -> exists R M,
      msteps SEGS (mkst (R0 sp) (Z_to_bv 64 A_start) MEM0 ROM) (mkst R (Z_to_bv 64 A_envloop_exit) M ROM)
      /\ regs_ok E7 SR2_t R /\ know_ok SEGS E7 M KN1_t /\ above_ok M /\ mem_grows MEM0 M.
  Proof.
    intros Hrs. pose proof R0_ok as HR. pose proof (KN0_ok true Hrs) as HK.
    pose proof usp_lo as SL. pose proof usp_fit as SF. pose proof len_av as LA. pose proof len_ev as LE.
    pose proof ENVP_range as ER.
    (* [comment removed for export] *)
    ms_block_with HR HK FUEL [A_envloop] noscr NX0 R1 HR1 HK1 MS1.
    lazymatch type of HK1 with know_ok _ _ ?m _ => set (M1 := m) in * end.
    assert (A1 : above_ok M1).
    { unfold M1. apply above_ok_block; [intros x Hx; reflexivity | vmc]. }
    assert (G1 : mem_grows MEM0 M1) by (unfold M1; apply mem_denot_grows).
    clearbody M1.
    (* [comment removed for export] *)
    destruct (fetchd_some _ _ envloop_code_0) as (w1 & F1 & E1 & D1).
    destruct (fetchd_some _ _ envloop_code_4) as (w2 & F2 & E2 & D2).
    destruct (fetchd_some _ _ envloop_code_8) as (w3 & F3 & E3 & D3).
    assert (He9 : getr R1 9%bv = Z_to_bv 64 (ENVP + 8 * Z.of_nat 0)).
    { rewrite (HR1 9%bv). change (sr_get _ 9%bv) with e_envp. apply bv_eq.
      rewrite u_small by (unfold ENVP; lia).
      assert (U : bv_unsigned (edenot E7 e_envp) = usp + 8 * argc + 16)
        by (unfold E7, usp, argc; eapply u_e_envp; first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
      rewrite U. unfold ENVP, usp, argc. lia. }
    destruct (env_loop SEGS A_envloop w1 w2 w3 ltac:(unfold A_envloop; lia) F1 F2 F3 E1 E2 E3 D1 D2 D3
                M1 ROM ENVP (length (in_envp inp))
                (cat_envp_ptr (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp)) ER)
      with (n := length (in_envp inp)) (k := 0%nat) (regs := R1)
      as (R2 & MS2 & P9 & P10 & Pag).
    - (* [comment removed for export] *) intros k Hk. split.
      + assert (RP : rdn SEGS stk (sp + nat_to_word (envp_off (in_argv inp) + 8 * k)) 8%nat
                     = Some (word_le8 (cat_envp_ptr (ed_top rnd) (in_argv inp) (in_envp inp)
                                         (in_execfn inp) k)))
          by (unfold stk; eapply read_envp_ptr_k;
              first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH | exact Hk]).
        rewrite <- n_to_le_8_spec, <- RP, envp_slot_eq.
        apply rdn_above; [exact A1 | rewrite u_small; unfold ENVP in *; lia | rewrite u_small; unfold ENVP in *; change (Z.of_nat 8) with 8; lia].
      + eapply cat_envp_ptr_nz; first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH | exact Hk].
    - (* [comment removed for export] *)
      assert (RN : rdn SEGS stk
                     (sp + nat_to_word (envp_off (in_argv inp) + 8 * length (in_envp inp))) 8%nat
                   = Some (word_le8 (Z_to_bv 64 0)))
        by (unfold stk; eapply read_envp_null;
            first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
      rewrite <- n_to_le_8_spec, <- RN, envp_slot_eq.
      apply rdn_above; [exact A1 | rewrite u_small; unfold ENVP in *; lia | rewrite u_small; unfold ENVP in *; change (Z.of_nat 8) with 8; lia].
    - lia.
    - exact He9.
    - (* [comment removed for export] *)
      exists R2, M1. split; [|split; [|split; [exact HK1 | split; [exact A1 | exact G1]]]].
      + eapply msteps_trans; [exact MS1|]. rewrite envloop_exit_eq. exact MS2.
      + unfold SR2_t. apply (regs_ok_upd2 E7 _ R1 R2 9%bv 10%bv); try exact HR1;
          try (intros HH; apply (f_equal bv_unsigned) in HH; discriminate HH).
        * rewrite P9. symmetry. apply bv_eq.
          assert (U : bv_unsigned (edenot E7 e_auxv) = usp + 8 * argc + 8 * envc + 24)
            by (unfold E7, usp, argc, envc; eapply u_e_auxv;
                first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
          rewrite U. rewrite u_small by (unfold ENVP in *; lia). unfold ENVP, usp, argc. lia.
        * rewrite P10. reflexivity.
        * intros r Hra Hrb. apply Pag. intros [C|C]; [apply Hra | apply Hrb]; exact C.
  Qed.

  Lemma phase1_f : kb_rseq (in_kernel inp) = false -> exists R M,
      msteps SEGS (mkst (R0 sp) (Z_to_bv 64 A_start) MEM0 ROM) (mkst R (Z_to_bv 64 A_envloop_exit) M ROM)
      /\ regs_ok E7 SR2_f R /\ know_ok SEGS E7 M KN1_f /\ above_ok M /\ mem_grows MEM0 M.
  Proof.
    intros Hrs. pose proof R0_ok as HR. pose proof (KN0_ok false Hrs) as HK.
    pose proof usp_lo as SL. pose proof usp_fit as SF. pose proof len_av as LA. pose proof len_ev as LE.
    pose proof ENVP_range as ER.
    (* [comment removed for export] *)
    ms_block_with HR HK FUEL [A_envloop] noscr NX0 R1 HR1 HK1 MS1.
    lazymatch type of HK1 with know_ok _ _ ?m _ => set (M1 := m) in * end.
    assert (A1 : above_ok M1).
    { unfold M1. apply above_ok_block; [intros x Hx; reflexivity | vmc]. }
    assert (G1 : mem_grows MEM0 M1) by (unfold M1; apply mem_denot_grows).
    clearbody M1.
    (* [comment removed for export] *)
    destruct (fetchd_some _ _ envloop_code_0) as (w1 & F1 & E1 & D1).
    destruct (fetchd_some _ _ envloop_code_4) as (w2 & F2 & E2 & D2).
    destruct (fetchd_some _ _ envloop_code_8) as (w3 & F3 & E3 & D3).
    assert (He9 : getr R1 9%bv = Z_to_bv 64 (ENVP + 8 * Z.of_nat 0)).
    { rewrite (HR1 9%bv). change (sr_get _ 9%bv) with e_envp. apply bv_eq.
      rewrite u_small by (unfold ENVP; lia).
      assert (U : bv_unsigned (edenot E7 e_envp) = usp + 8 * argc + 16)
        by (unfold E7, usp, argc; eapply u_e_envp; first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
      rewrite U. unfold ENVP, usp, argc. lia. }
    destruct (env_loop SEGS A_envloop w1 w2 w3 ltac:(unfold A_envloop; lia) F1 F2 F3 E1 E2 E3 D1 D2 D3
                M1 ROM ENVP (length (in_envp inp))
                (cat_envp_ptr (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp)) ER)
      with (n := length (in_envp inp)) (k := 0%nat) (regs := R1)
      as (R2 & MS2 & P9 & P10 & Pag).
    - (* [comment removed for export] *) intros k Hk. split.
      + assert (RP : rdn SEGS stk (sp + nat_to_word (envp_off (in_argv inp) + 8 * k)) 8%nat
                     = Some (word_le8 (cat_envp_ptr (ed_top rnd) (in_argv inp) (in_envp inp)
                                         (in_execfn inp) k)))
          by (unfold stk; eapply read_envp_ptr_k;
              first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH | exact Hk]).
        rewrite <- n_to_le_8_spec, <- RP, envp_slot_eq.
        apply rdn_above; [exact A1 | rewrite u_small; unfold ENVP in *; lia | rewrite u_small; unfold ENVP in *; change (Z.of_nat 8) with 8; lia].
      + eapply cat_envp_ptr_nz; first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH | exact Hk].
    - (* [comment removed for export] *)
      assert (RN : rdn SEGS stk
                     (sp + nat_to_word (envp_off (in_argv inp) + 8 * length (in_envp inp))) 8%nat
                   = Some (word_le8 (Z_to_bv 64 0)))
        by (unfold stk; eapply read_envp_null;
            first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
      rewrite <- n_to_le_8_spec, <- RN, envp_slot_eq.
      apply rdn_above; [exact A1 | rewrite u_small; unfold ENVP in *; lia | rewrite u_small; unfold ENVP in *; change (Z.of_nat 8) with 8; lia].
    - lia.
    - exact He9.
    - (* [comment removed for export] *)
      exists R2, M1. split; [|split; [|split; [exact HK1 | split; [exact A1 | exact G1]]]].
      + eapply msteps_trans; [exact MS1|]. rewrite envloop_exit_eq. exact MS2.
      + unfold SR2_f. apply (regs_ok_upd2 E7 _ R1 R2 9%bv 10%bv); try exact HR1;
          try (intros HH; apply (f_equal bv_unsigned) in HH; discriminate HH).
        * rewrite P9. symmetry. apply bv_eq.
          assert (U : bv_unsigned (edenot E7 e_auxv) = usp + 8 * argc + 8 * envc + 24)
            by (unfold E7, usp, argc, envc; eapply u_e_auxv;
                first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
          rewrite U. rewrite u_small by (unfold ENVP in *; lia). unfold ENVP, usp, argc. lia.
        * rewrite P10. reflexivity.
        * intros r Hra Hrb. apply Pag. intros [C|C]; [apply Hra | apply Hrb]; exact C.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* The strings start at [usp + CHD + PAD], not at the old head's size:
     see point 3 of the port note. *)
  Definition PN : Z := usp + CHD + PAD.
  Let s0 : list byte := nth 0 (in_argv inp) [].

  Definition is_kblob_k (k : nat) (K : kentry) : bool :=
    match K with KBlob _ _ k' => Nat.eqb k k' | _ => false end.

  Lemma s0_len : Z.of_nat (length s0) <= 131071.
  Proof. unfold s0. destruct Hva as (H1 & _ & H3 & _). destruct (in_argv inp) as [|a t]; [cbn in H1; lia|]. cbn. inversion H3. lia. Qed.

  Lemma s0_nonul : ~ In (Z_to_bv 8 0) s0.
  Proof. unfold s0. destruct Hva as (H1 & _ & _ & H4 & _). destruct (in_argv inp) as [|a t]; [cbn in H1; lia|]. cbn. inversion H4. assumption. Qed.

  Lemma PN_range : 0 <= PN /\ PN + Z.of_nat (length s0) + 2 < 2 ^ 48.
  Proof.
    pose proof usp_lo. pose proof usp_fit as SF.
    assert (AE : usp + CHD + PAD + Z.of_nat (length s0) + 1 <= usp + Z.of_nat (length bsb))
      by (unfold usp, CHD, PAD, s0, bsb; eapply argv0_end_le;
          first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
    unfold PN, usp, CHD, PAD, s0 in *. lia.
  Qed.

  Lemma x11_after_B2_t : sr_get SR2e_t 11%bv = mkAlu ALU_ADD e_str0 (ELit 1).
  Proof. vmeq_refl. Qed.
  Lemma x11_after_B2_f : sr_get SR2e_f 11%bv = mkAlu ALU_ADD e_str0 (ELit 1).
  Proof. vmeq_refl. Qed.

  Lemma phase2_t : forall R M,
    regs_ok E7 SR2_t R -> know_ok SEGS E7 M KN1_t -> above_ok M -> mem_grows MEM0 M ->
    exists R' M', msteps SEGS (mkst R (Z_to_bv 64 A_envloop_exit) M ROM) (mkst R' (Z_to_bv 64 A_pnloop_exit) M' ROM)
      /\ regs_ok E7 SR3_t R' /\ know_ok SEGS E7 M' KN3_t /\ above_ok M' /\ mem_grows MEM0 M'.
  Proof.
    intros R M HR HK HA HG.
    pose proof usp_lo as SL. pose proof usp_fit as SF. pose proof len_av as LA. pose proof len_ev as LE.
    pose proof PN_range as PR. pose proof s0_len as SLEN.
    assert (US0 : bv_unsigned (edenot E7 e_str0) = usp + CHD + PAD)
      by (unfold E7, usp, CHD, PAD; eapply u_e_str0;
          first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
    assert (US1 : bv_unsigned (edenot E7 e_str1) = usp + CHD + PAD + Z.of_nat (length s0) + 1)
      by (unfold E7, usp, CHD, PAD, s0; eapply u_e_str1;
          first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
    (* [comment removed for export] *)
    ms_block_with HR HK FUEL [A_pnloop] noscr NX0 R2 HR2 HK2 MS2.
    lazymatch type of HK2 with know_ok _ _ ?m _ => set (M2 := m) in * end.
    assert (A2 : above_ok M2).
    { unfold M2. apply above_ok_block; [exact HA | vmc]. }
    assert (G2 : mem_grows MEM0 M2) by (unfold M2; eapply mem_grows_trans; [exact HG | apply mem_denot_grows]).
    clearbody M2. clear HR HK HA HG.
    (* [comment removed for export] *)
    destruct (fetchd_some _ _ pnloop_code_m8) as (w0 & F0 & NE0 & D0).
    destruct (fetchd_some _ _ pnloop_code_m4) as (w1 & F1 & NE1 & D1).
    destruct (fetchd_some _ _ pnloop_code_0) as (w2 & F2 & NE2 & D2).
    destruct (fetchd_some _ _ pnloop_code_4) as (w3 & F3 & NE3 & D3).
    destruct (fetchd_some _ _ pnloop_code_8) as (w4 & F4 & NE4 & D4).
    (* [comment removed for export] *)
    assert (Hrd : forall j, (j <= length s0)%nat -> rdn SEGS M2 (Z_to_bv 64 (PN + Z.of_nat j)) 1 = Some [byte_at s0 j]).
    { let i := kidx KN2_t (is_kblob_k K_ARGV0) in
      pose proof (know_nth SEGS E7 M2 KN2_t i _ HK2 eq_refl) as KB.
      cbn [kentry_ok] in KB. destruct KB as (Hfl & Hlen & Hby).
      lazymatch type of Hlen with _ = elenZ E7 ?n =>
        assert (Elen : elenZ E7 n = Z.of_nat (length s0) + 1)
          by (rewrite <- Hlen; unfold E7, E0; cbn [eb blobs0 K_ARGV0 K_RND Nat.eqb]; rewrite length_app; cbn [length]; unfold s0; lia)
      end.
      lazymatch type of Hby with (forall i, _ -> M2 (Z_to_bv 64 (?st + i)) = _) =>
        assert (Est : st = PN)
      end.
      { unfold estart. cbn [a_base a_off].
        assert (Hak : snd e_strb = 16) by (vm_compute; reflexivity).
        assert (Hab : split_lit e_str0 = (fst e_strb, snd e_strb))
          by (unfold e_strb; destruct (split_lit e_str0); reflexivity).
        assert (Hsu : bv_unsigned (edenot E7 (fst e_strb)) + snd e_strb
                      = bv_unsigned (edenot E7 e_str0)).
        { unfold E7. eapply split_u;
            [ exact Hab
            | rewrite Hak; lia
            | unfold EntryKn.uE; fold E7; rewrite US0, Hak; pose proof usp_lo; unfold CHD, PAD; lia ]. }
        (* the chain's blob start is [e_strb] in normal form *)
        rewrite Hak in Hsu. let b := eval vm_compute in (fst e_strb) in change (fst e_strb) with b in Hsu.
        rewrite Hsu, US0. unfold PN. reflexivity. }
      intros j Hj. cbn [rdn].
      rewrite Est, Elen in Hby. rewrite (Hby (Z.of_nat j)) by lia. rewrite Nat2Z.id.
      unfold byte_at. unfold E7, E0. cbn [eb blobs0 K_ARGV0 K_RND Nat.eqb]. reflexivity. }
    assert (Hst : store_ok SEGS M2 (Z_to_bv 64 A_progname) 8 = true).
    { let i := kidx KN2_t (is_kwr_cov (ELit 0) A_progname 8) in
      eapply (kwr_store_ok_lit SEGS E7 M2 KN2_t i); [exact HK2 | reflexivity | ..]; unfold A_progname; lia. }
    destruct (pn_loop SEGS A_pnloop w0 w1 w2 w3 w4 ltac:(unfold A_pnloop; lia) F0 F1 F2 F3 F4 NE0 NE1 NE2 NE3 NE4 D0 D1 D2 D3 D4
                M2 ROM A_progname PN s0 ltac:(unfold A_progname; lia) ltac:(lia) ltac:(pose proof usp_lo; unfold A_progname, PN, usp, CHD, PAD; lia) s0_nonul Hrd Hst
                s0 0%nat R2 M2 eq_refl ltac:(lia))
      as (R3 & M3 & MS3 & (P11 & P13 & Pag) & (C1 & C2)).
    - rewrite (HR2 10%bv). reflexivity.
    - rewrite (HR2 11%bv). change (sr_get _ 11%bv) with (mkAlu ALU_ADD e_str0 (ELit 1)). rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. unfold v_add.
      apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite US0.
      change (1 mod 2 ^ 64) with 1. rewrite !Z.mod_small by (unfold PN, usp, CHD, PAD in *; lia). unfold PN. lia.
    - rewrite (HR2 12%bv). reflexivity.
    - apply cellrel_refl.
    - (* [comment removed for export] *)
      exists R3, M3. split; [|split; [|split; [|split]]].
      + eapply msteps_trans; [exact MS2|]. rewrite pnloop_exit_eq. exact MS3.
      + unfold SR3_t. apply (regs_ok_upd2 E7 _ R2 R3 11%bv 13%bv); try exact HR2;
          try (intros HH; apply (f_equal bv_unsigned) in HH; discriminate HH).
        * rewrite P11. symmetry. apply bv_eq. rewrite US1. rewrite u_small by (unfold PN, usp, CHD, PAD in *; lia).
          unfold PN. lia.
        * rewrite P13. reflexivity.
        * intros r Hra Hrb. apply Pag. intros [C|C]; [apply Hra | apply Hrb]; exact C.
      + unfold KN3_t. apply (know_change_keep SEGS E7 M2 M3); [exact HK2 | | exact C2].
        intros x Hx. apply C1. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx.
        rewrite !u_small in Hx by (unfold A_progname; lia). lia.
      + intros x Hx. rewrite C1; [apply A2; exact Hx|]. unfold A_progname. right. unfold usp in *. lia.
      + eapply mem_grows_trans; [exact G2 | exact C2].
  Qed.

  Lemma phase2_f : forall R M,
    regs_ok E7 SR2_f R -> know_ok SEGS E7 M KN1_f -> above_ok M -> mem_grows MEM0 M ->
    exists R' M', msteps SEGS (mkst R (Z_to_bv 64 A_envloop_exit) M ROM) (mkst R' (Z_to_bv 64 A_pnloop_exit) M' ROM)
      /\ regs_ok E7 SR3_f R' /\ know_ok SEGS E7 M' KN3_f /\ above_ok M' /\ mem_grows MEM0 M'.
  Proof.
    intros R M HR HK HA HG.
    pose proof usp_lo as SL. pose proof usp_fit as SF. pose proof len_av as LA. pose proof len_ev as LE.
    pose proof PN_range as PR. pose proof s0_len as SLEN.
    assert (US0 : bv_unsigned (edenot E7 e_str0) = usp + CHD + PAD)
      by (unfold E7, usp, CHD, PAD; eapply u_e_str0;
          first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
    assert (US1 : bv_unsigned (edenot E7 e_str1) = usp + CHD + PAD + Z.of_nat (length s0) + 1)
      by (unfold E7, usp, CHD, PAD, s0; eapply u_e_str1;
          first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
    (* [comment removed for export] *)
    ms_block_with HR HK FUEL [A_pnloop] noscr NX0 R2 HR2 HK2 MS2.
    lazymatch type of HK2 with know_ok _ _ ?m _ => set (M2 := m) in * end.
    assert (A2 : above_ok M2).
    { unfold M2. apply above_ok_block; [exact HA | vmc]. }
    assert (G2 : mem_grows MEM0 M2) by (unfold M2; eapply mem_grows_trans; [exact HG | apply mem_denot_grows]).
    clearbody M2. clear HR HK HA HG.
    (* [comment removed for export] *)
    destruct (fetchd_some _ _ pnloop_code_m8) as (w0 & F0 & NE0 & D0).
    destruct (fetchd_some _ _ pnloop_code_m4) as (w1 & F1 & NE1 & D1).
    destruct (fetchd_some _ _ pnloop_code_0) as (w2 & F2 & NE2 & D2).
    destruct (fetchd_some _ _ pnloop_code_4) as (w3 & F3 & NE3 & D3).
    destruct (fetchd_some _ _ pnloop_code_8) as (w4 & F4 & NE4 & D4).
    (* [comment removed for export] *)
    assert (Hrd : forall j, (j <= length s0)%nat -> rdn SEGS M2 (Z_to_bv 64 (PN + Z.of_nat j)) 1 = Some [byte_at s0 j]).
    { let i := kidx KN2_f (is_kblob_k K_ARGV0) in
      pose proof (know_nth SEGS E7 M2 KN2_f i _ HK2 eq_refl) as KB.
      cbn [kentry_ok] in KB. destruct KB as (Hfl & Hlen & Hby).
      lazymatch type of Hlen with _ = elenZ E7 ?n =>
        assert (Elen : elenZ E7 n = Z.of_nat (length s0) + 1)
          by (rewrite <- Hlen; unfold E7, E0; cbn [eb blobs0 K_ARGV0 K_RND Nat.eqb]; rewrite length_app; cbn [length]; unfold s0; lia)
      end.
      lazymatch type of Hby with (forall i, _ -> M2 (Z_to_bv 64 (?st + i)) = _) =>
        assert (Est : st = PN)
      end.
      { unfold estart. cbn [a_base a_off].
        assert (Hak : snd e_strb = 16) by (vm_compute; reflexivity).
        assert (Hab : split_lit e_str0 = (fst e_strb, snd e_strb))
          by (unfold e_strb; destruct (split_lit e_str0); reflexivity).
        assert (Hsu : bv_unsigned (edenot E7 (fst e_strb)) + snd e_strb
                      = bv_unsigned (edenot E7 e_str0)).
        { unfold E7. eapply split_u;
            [ exact Hab
            | rewrite Hak; lia
            | unfold EntryKn.uE; fold E7; rewrite US0, Hak; pose proof usp_lo; unfold CHD, PAD; lia ]. }
        (* the chain's blob start is [e_strb] in normal form *)
        rewrite Hak in Hsu. let b := eval vm_compute in (fst e_strb) in change (fst e_strb) with b in Hsu.
        rewrite Hsu, US0. unfold PN. reflexivity. }
      intros j Hj. cbn [rdn].
      rewrite Est, Elen in Hby. rewrite (Hby (Z.of_nat j)) by lia. rewrite Nat2Z.id.
      unfold byte_at. unfold E7, E0. cbn [eb blobs0 K_ARGV0 K_RND Nat.eqb]. reflexivity. }
    assert (Hst : store_ok SEGS M2 (Z_to_bv 64 A_progname) 8 = true).
    { let i := kidx KN2_f (is_kwr_cov (ELit 0) A_progname 8) in
      eapply (kwr_store_ok_lit SEGS E7 M2 KN2_f i); [exact HK2 | reflexivity | ..]; unfold A_progname; lia. }
    destruct (pn_loop SEGS A_pnloop w0 w1 w2 w3 w4 ltac:(unfold A_pnloop; lia) F0 F1 F2 F3 F4 NE0 NE1 NE2 NE3 NE4 D0 D1 D2 D3 D4
                M2 ROM A_progname PN s0 ltac:(unfold A_progname; lia) ltac:(lia) ltac:(pose proof usp_lo; unfold A_progname, PN, usp, CHD, PAD; lia) s0_nonul Hrd Hst
                s0 0%nat R2 M2 eq_refl ltac:(lia))
      as (R3 & M3 & MS3 & (P11 & P13 & Pag) & (C1 & C2)).
    - rewrite (HR2 10%bv). reflexivity.
    - rewrite (HR2 11%bv). change (sr_get _ 11%bv) with (mkAlu ALU_ADD e_str0 (ELit 1)). rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. unfold v_add.
      apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite US0.
      change (1 mod 2 ^ 64) with 1. rewrite !Z.mod_small by (unfold PN, usp, CHD, PAD in *; lia). unfold PN. lia.
    - rewrite (HR2 12%bv). reflexivity.
    - apply cellrel_refl.
    - (* [comment removed for export] *)
      exists R3, M3. split; [|split; [|split; [|split]]].
      + eapply msteps_trans; [exact MS2|]. rewrite pnloop_exit_eq. exact MS3.
      + unfold SR3_f. apply (regs_ok_upd2 E7 _ R2 R3 11%bv 13%bv); try exact HR2;
          try (intros HH; apply (f_equal bv_unsigned) in HH; discriminate HH).
        * rewrite P11. symmetry. apply bv_eq. rewrite US1. rewrite u_small by (unfold PN, usp, CHD, PAD in *; lia).
          unfold PN. lia.
        * rewrite P13. reflexivity.
        * intros r Hra Hrb. apply Pag. intros [C|C]; [apply Hra | apply Hrb]; exact C.
      + unfold KN3_f. apply (know_change_keep SEGS E7 M2 M3); [exact HK2 | | exact C2].
        intros x Hx. apply C1. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx.
        rewrite !u_small in Hx by (unfold A_progname; lia). lia.
      + intros x Hx. rewrite C1; [apply A2; exact Hx|]. unfold A_progname. right. unfold usp in *. lia.
      + eapply mem_grows_trans; [exact G2 | exact C2].
  Qed.

  Lemma phase1 : forall rs, kb_rseq (in_kernel inp) = rs -> exists R M,
      msteps SEGS (mkst (R0 sp) (Z_to_bv 64 A_start) MEM0 ROM) (mkst R (Z_to_bv 64 A_envloop_exit) M ROM)
      /\ regs_ok E7 (SR2r rs) R /\ know_ok SEGS E7 M (KN1r rs) /\ above_ok M /\ mem_grows MEM0 M.
  Proof using Hsp Hva Hve Hvl Hlau Huid. intros [] Hrs; [exact (phase1_t Hrs) | exact (phase1_f Hrs)]. Qed.

  Lemma phase2 : forall rs R M,
    regs_ok E7 (SR2r rs) R -> know_ok SEGS E7 M (KN1r rs) -> above_ok M -> mem_grows MEM0 M ->
    exists R' M', msteps SEGS (mkst R (Z_to_bv 64 A_envloop_exit) M ROM) (mkst R' (Z_to_bv 64 A_pnloop_exit) M' ROM)
      /\ regs_ok E7 (SR3r rs) R' /\ know_ok SEGS E7 M' (KN3r rs) /\ above_ok M' /\ mem_grows MEM0 M'.
  Proof using Hsp Hva Hve Hvl Hlau. intros []; [exact phase2_t | exact phase2_f]. Qed.

End Walk.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanStartLoops.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boot1_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* The port note above this file's first [Section Walk] applies verbatim
   to this one: the entry-image tuple, the DELETED
   [build_stack_bytes_within_span] replaced by the EQUALITY
   [length_entry_stack_image_launch], and [PN] moved from the old head's
   size to [usp + CHD + PAD]. *)
Section Walk.
  Variable inp : ProcInput.
  Variable mb : word.
  Variable entry : word.
  Variables sp brk : word.
  Variable rnd : EntryDraw.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mb rnd) inp.
  Hypothesis Huid : valid_id (in_uid inp).

  (* [comment removed for export] *)
  Definition E7 : env := E0 inp mb entry sp rnd.
  Definition MEM0 : word -> option byte := M0 inp mb PH entry sp rnd.
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length (in_argv inp)).
  Let envc := Z.of_nat (length (in_envp inp)).
  (* CHD and PAD: the head's size and the [arch_align_stack] pad.  Neither
     names a byte count and both are parametric in CONFIG_RSEQ.  [CHD]
     rather than [C]: two proofs below do [intros [C|C]]. *)
  Let CHD := Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)).
  Let PAD := Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) sp (ed_top rnd)
                         (in_argv inp) (in_envp inp) (in_execfn inp)).

  (* [comment removed for export] *)
  Definition above_ok (M : word -> option byte) : Prop :=
    forall x : word, usp <= bv_unsigned x -> M x = MEM0 x.

  Lemma usp_lo : 0x7fff80000000 <= usp.
  Proof. destruct Hsp as (H & _ & _). unfold sp_window_lo in H. exact H. Qed.
  Lemma usp_hi : usp <= 0x800000000000.
  Proof. destruct Hsp as (_ & H & _). unfold sp_window_hi in H. exact H. Qed.
  Lemma usp_al : usp mod 16 = 0.
  Proof. destruct Hsp as (_ & _ & H). exact H. Qed.
  Lemma len_av : 1 <= argc <= 1024. Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  Lemma len_ev : 0 <= envc <= 256. Proof. unfold envc. destruct Hve as [H _]. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma kx_ok : know_ok SEGS E7 MEM0 kx.
  Proof. unfold kx. constructor. Qed.

  (* the window floor is at or below sp - 6144512 ([StoreOk.stack_window_lo_valid]) *)
  Lemma Hwlo_sp : (stack_window_lo (in_kernel inp) mb rnd <= bv_unsigned sp - 6144512)%Z.
  Proof.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk.stack_window_lo_valid inp sp brk mb rnd Hvl Hlau) as B.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk.stack_window_reach, stack_max_size in B. lia.
  Qed.

  (* one entry table per CONFIG_RSEQ value; [rs] is the launch's own *)
  Lemma KN0_ok : forall rs, kb_rseq (in_kernel inp) = rs -> know_ok SEGS E7 MEM0 (KN0r rs).
  Proof.
    intros rs Hrs. unfold KN0r, E7, MEM0. eapply kn0_ok_b; try eassumption.
    all: first [ exact img_hull | exact rw_window | exact kx_ok | exact Hwlo_sp ].
  Qed.

  Lemma R0_ok : regs_ok E7 sr_init (R0 sp).
  Proof. unfold E7. apply regs0_ok. Qed.

  (* The image IS the block at 75d69e00, so [bsb] is the image. *)
  Let bsb := entry_stack_image inp mb PH entry sp rnd.
  Let stk := stack_to_mem sp (entry_stack_image inp mb PH entry sp rnd).

  (* See point 2 of the port note: the deleted span bound is replaced by
     the EQUALITY, not re-threaded. *)
  Lemma usp_fit : usp + Z.of_nat (length bsb) <= 2 ^ 47.
  Proof.
    unfold bsb.
    rewrite (length_entry_stack_image_launch Sv48 inp mb PH entry sp brk rnd Hlau).
    destruct Hlau as (Htop & _ & _).
    unfold valid_stack_top_va in Htop. destruct Htop as (_ & Htople & _).
    cbn [va_stack_top] in Htople. unfold usp, sp_window_hi in *. lia.
  Qed.
  Lemma Hhi' : bv_unsigned sp <= sp_window_hi. Proof. pose proof usp_hi. unfold sp_window_hi, usp in *. lia. Qed.
  Lemma Hlo' : sp_window_lo <= bv_unsigned sp. Proof. pose proof usp_lo. unfold sp_window_lo, usp in *. lia. Qed.

  Lemma rdn_above : forall M (a : word) n,
    above_ok M -> usp <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
    rdn SEGS M a n = rdn SEGS stk a n.
  Proof.
    intros M a n HA Ha Hn. unfold stk.
    rewrite <- (rdn_wrap_stack_above SEGS inp mb PH entry sp rnd a n) by (unfold usp in *; lia).
    apply rdn_ext; [exact Hn|]. intros x Hx. rewrite (HA x) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma above_ok_block : forall M log,
    above_ok M -> log_below_b 0%nat [] log = true -> above_ok (mem_denot E7 M log).
  Proof.
    intros M log HA Hb x Hx. pose proof usp_lo. pose proof usp_hi.
    rewrite (mem_denot_above E7 M log 0%nat [] usp x Hb); try (cbn [ev E7 E0 vals_ev vals0 nth]; unfold usp in *; lia).
    - apply HA. exact Hx.
    - constructor.
  Qed.

  (* [comment removed for export] *)
  Ltac vmc := lazymatch goal with |- log_below_b _ _ _ = true => vmeq_refl end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ENVP : Z := usp + 8 * argc + 16.

  Lemma ENVP_range : 0 <= ENVP /\ ENVP + 8 * Z.of_nat (length (in_envp inp)) + 16 < 2 ^ 64.
  Proof.
    assert (NW : usp + Z.of_nat (length bsb) < 2 ^ 64)
      by (unfold usp, bsb; eapply lay_bsb_nw; first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
    assert (AB : (auxv_off (in_argv inp) (in_envp inp)
                  + auxv_size (kb_rseq (in_kernel inp)) + 16 <= length bsb)%nat)
      by (unfold bsb; eapply auxv_off_bound; first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
    pose proof usp_lo. unfold auxv_off in AB. unfold ENVP, usp, argc. lia.
  Qed.

  Lemma envp_slot_eq : forall k,
    (sp + nat_to_word (envp_off (in_argv inp) + 8 * k))%bv = Z_to_bv 64 (ENVP + 8 * Z.of_nat k).
  Proof.
    intros k. apply bv_eq. rewrite word_add_nat. f_equal. f_equal. unfold envp_off, ENVP, usp, argc. lia.
  Qed.

  Lemma phase1_t : kb_rseq (in_kernel inp) = true -> exists R M,
      msteps SEGS (mkst (R0 sp) (Z_to_bv 64 A_start) MEM0 ROM) (mkst R (Z_to_bv 64 A_envloop_exit) M ROM)
      /\ regs_ok E7 SR2_t R /\ know_ok SEGS E7 M KN1_t /\ above_ok M /\ mem_grows MEM0 M.
  Proof.
    intros Hrs. pose proof R0_ok as HR. pose proof (KN0_ok true Hrs) as HK.
    pose proof usp_lo as SL. pose proof usp_fit as SF. pose proof len_av as LA. pose proof len_ev as LE.
    pose proof ENVP_range as ER.
    (* [comment removed for export] *)
    ms_block_with HR HK FUEL [A_envloop] noscr NX0 R1 HR1 HK1 MS1.
    lazymatch type of HK1 with know_ok _ _ ?m _ => set (M1 := m) in * end.
    assert (A1 : above_ok M1).
    { unfold M1. apply above_ok_block; [intros x Hx; reflexivity | vmc]. }
    assert (G1 : mem_grows MEM0 M1) by (unfold M1; apply mem_denot_grows).
    clearbody M1.
    (* [comment removed for export] *)
    destruct (fetchd_some _ _ envloop_code_0) as (w1 & F1 & E1 & D1).
    destruct (fetchd_some _ _ envloop_code_4) as (w2 & F2 & E2 & D2).
    destruct (fetchd_some _ _ envloop_code_8) as (w3 & F3 & E3 & D3).
    assert (He9 : getr R1 9%bv = Z_to_bv 64 (ENVP + 8 * Z.of_nat 0)).
    { rewrite (HR1 9%bv). change (sr_get _ 9%bv) with e_envp. apply bv_eq.
      rewrite u_small by (unfold ENVP; lia).
      assert (U : bv_unsigned (edenot E7 e_envp) = usp + 8 * argc + 16)
        by (unfold E7, usp, argc; eapply u_e_envp; first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
      rewrite U. unfold ENVP, usp, argc. lia. }
    destruct (env_loop SEGS A_envloop w1 w2 w3 ltac:(unfold A_envloop; lia) F1 F2 F3 E1 E2 E3 D1 D2 D3
                M1 ROM ENVP (length (in_envp inp))
                (cat_envp_ptr (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp)) ER)
      with (n := length (in_envp inp)) (k := 0%nat) (regs := R1)
      as (R2 & MS2 & P9 & P10 & Pag).
    - (* [comment removed for export] *) intros k Hk. split.
      + assert (RP : rdn SEGS stk (sp + nat_to_word (envp_off (in_argv inp) + 8 * k)) 8%nat
                     = Some (word_le8 (cat_envp_ptr (ed_top rnd) (in_argv inp) (in_envp inp)
                                         (in_execfn inp) k)))
          by (unfold stk; eapply read_envp_ptr_k;
              first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH | exact Hk]).
        rewrite <- n_to_le_8_spec, <- RP, envp_slot_eq.
        apply rdn_above; [exact A1 | rewrite u_small; unfold ENVP in *; lia | rewrite u_small; unfold ENVP in *; change (Z.of_nat 8) with 8; lia].
      + eapply cat_envp_ptr_nz; first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH | exact Hk].
    - (* [comment removed for export] *)
      assert (RN : rdn SEGS stk
                     (sp + nat_to_word (envp_off (in_argv inp) + 8 * length (in_envp inp))) 8%nat
                   = Some (word_le8 (Z_to_bv 64 0)))
        by (unfold stk; eapply read_envp_null;
            first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
      rewrite <- n_to_le_8_spec, <- RN, envp_slot_eq.
      apply rdn_above; [exact A1 | rewrite u_small; unfold ENVP in *; lia | rewrite u_small; unfold ENVP in *; change (Z.of_nat 8) with 8; lia].
    - lia.
    - exact He9.
    - (* [comment removed for export] *)
      exists R2, M1. split; [|split; [|split; [exact HK1 | split; [exact A1 | exact G1]]]].
      + eapply msteps_trans; [exact MS1|]. rewrite envloop_exit_eq. exact MS2.
      + unfold SR2_t. apply (regs_ok_upd2 E7 _ R1 R2 9%bv 10%bv); try exact HR1;
          try (intros HH; apply (f_equal bv_unsigned) in HH; discriminate HH).
        * rewrite P9. symmetry. apply bv_eq.
          assert (U : bv_unsigned (edenot E7 e_auxv) = usp + 8 * argc + 8 * envc + 24)
            by (unfold E7, usp, argc, envc; eapply u_e_auxv;
                first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
          rewrite U. rewrite u_small by (unfold ENVP in *; lia). unfold ENVP, usp, argc. lia.
        * rewrite P10. reflexivity.
        * intros r Hra Hrb. apply Pag. intros [C|C]; [apply Hra | apply Hrb]; exact C.
  Qed.

  Lemma phase1_f : kb_rseq (in_kernel inp) = false -> exists R M,
      msteps SEGS (mkst (R0 sp) (Z_to_bv 64 A_start) MEM0 ROM) (mkst R (Z_to_bv 64 A_envloop_exit) M ROM)
      /\ regs_ok E7 SR2_f R /\ know_ok SEGS E7 M KN1_f /\ above_ok M /\ mem_grows MEM0 M.
  Proof.
    intros Hrs. pose proof R0_ok as HR. pose proof (KN0_ok false Hrs) as HK.
    pose proof usp_lo as SL. pose proof usp_fit as SF. pose proof len_av as LA. pose proof len_ev as LE.
    pose proof ENVP_range as ER.
    (* [comment removed for export] *)
    ms_block_with HR HK FUEL [A_envloop] noscr NX0 R1 HR1 HK1 MS1.
    lazymatch type of HK1 with know_ok _ _ ?m _ => set (M1 := m) in * end.
    assert (A1 : above_ok M1).
    { unfold M1. apply above_ok_block; [intros x Hx; reflexivity | vmc]. }
    assert (G1 : mem_grows MEM0 M1) by (unfold M1; apply mem_denot_grows).
    clearbody M1.
    (* [comment removed for export] *)
    destruct (fetchd_some _ _ envloop_code_0) as (w1 & F1 & E1 & D1).
    destruct (fetchd_some _ _ envloop_code_4) as (w2 & F2 & E2 & D2).
    destruct (fetchd_some _ _ envloop_code_8) as (w3 & F3 & E3 & D3).
    assert (He9 : getr R1 9%bv = Z_to_bv 64 (ENVP + 8 * Z.of_nat 0)).
    { rewrite (HR1 9%bv). change (sr_get _ 9%bv) with e_envp. apply bv_eq.
      rewrite u_small by (unfold ENVP; lia).
      assert (U : bv_unsigned (edenot E7 e_envp) = usp + 8 * argc + 16)
        by (unfold E7, usp, argc; eapply u_e_envp; first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
      rewrite U. unfold ENVP, usp, argc. lia. }
    destruct (env_loop SEGS A_envloop w1 w2 w3 ltac:(unfold A_envloop; lia) F1 F2 F3 E1 E2 E3 D1 D2 D3
                M1 ROM ENVP (length (in_envp inp))
                (cat_envp_ptr (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp)) ER)
      with (n := length (in_envp inp)) (k := 0%nat) (regs := R1)
      as (R2 & MS2 & P9 & P10 & Pag).
    - (* [comment removed for export] *) intros k Hk. split.
      + assert (RP : rdn SEGS stk (sp + nat_to_word (envp_off (in_argv inp) + 8 * k)) 8%nat
                     = Some (word_le8 (cat_envp_ptr (ed_top rnd) (in_argv inp) (in_envp inp)
                                         (in_execfn inp) k)))
          by (unfold stk; eapply read_envp_ptr_k;
              first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH | exact Hk]).
        rewrite <- n_to_le_8_spec, <- RP, envp_slot_eq.
        apply rdn_above; [exact A1 | rewrite u_small; unfold ENVP in *; lia | rewrite u_small; unfold ENVP in *; change (Z.of_nat 8) with 8; lia].
      + eapply cat_envp_ptr_nz; first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH | exact Hk].
    - (* [comment removed for export] *)
      assert (RN : rdn SEGS stk
                     (sp + nat_to_word (envp_off (in_argv inp) + 8 * length (in_envp inp))) 8%nat
                   = Some (word_le8 (Z_to_bv 64 0)))
        by (unfold stk; eapply read_envp_null;
            first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
      rewrite <- n_to_le_8_spec, <- RN, envp_slot_eq.
      apply rdn_above; [exact A1 | rewrite u_small; unfold ENVP in *; lia | rewrite u_small; unfold ENVP in *; change (Z.of_nat 8) with 8; lia].
    - lia.
    - exact He9.
    - (* [comment removed for export] *)
      exists R2, M1. split; [|split; [|split; [exact HK1 | split; [exact A1 | exact G1]]]].
      + eapply msteps_trans; [exact MS1|]. rewrite envloop_exit_eq. exact MS2.
      + unfold SR2_f. apply (regs_ok_upd2 E7 _ R1 R2 9%bv 10%bv); try exact HR1;
          try (intros HH; apply (f_equal bv_unsigned) in HH; discriminate HH).
        * rewrite P9. symmetry. apply bv_eq.
          assert (U : bv_unsigned (edenot E7 e_auxv) = usp + 8 * argc + 8 * envc + 24)
            by (unfold E7, usp, argc, envc; eapply u_e_auxv;
                first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
          rewrite U. rewrite u_small by (unfold ENVP in *; lia). unfold ENVP, usp, argc. lia.
        * rewrite P10. reflexivity.
        * intros r Hra Hrb. apply Pag. intros [C|C]; [apply Hra | apply Hrb]; exact C.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* The strings start at [usp + CHD + PAD], not at the old head's size:
     see point 3 of the port note above the first [Section Walk]. *)
  Definition PN : Z := usp + CHD + PAD.
  Let s0 : list byte := nth 0 (in_argv inp) [].

  Definition is_kblob_k (k : nat) (K : kentry) : bool :=
    match K with KBlob _ _ k' => Nat.eqb k k' | _ => false end.

  Lemma s0_len : Z.of_nat (length s0) <= 131071.
  Proof. unfold s0. destruct Hva as (H1 & _ & H3 & _). destruct (in_argv inp) as [|a t]; [cbn in H1; lia|]. cbn. inversion H3. lia. Qed.

  Lemma s0_nonul : ~ In (Z_to_bv 8 0) s0.
  Proof. unfold s0. destruct Hva as (H1 & _ & _ & H4 & _). destruct (in_argv inp) as [|a t]; [cbn in H1; lia|]. cbn. inversion H4. assumption. Qed.

  Lemma PN_range : 0 <= PN /\ PN + Z.of_nat (length s0) + 2 < 2 ^ 48.
  Proof.
    pose proof usp_lo. pose proof usp_fit as SF.
    assert (AE : usp + CHD + PAD + Z.of_nat (length s0) + 1 <= usp + Z.of_nat (length bsb))
      by (unfold usp, CHD, PAD, s0, bsb; eapply argv0_end_le;
          first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
    unfold PN, usp, CHD, PAD, s0 in *. lia.
  Qed.

  Lemma x11_after_B2_t : sr_get SR2e_t 11%bv = mkAlu ALU_ADD e_str0 (ELit 1).
  Proof. vmeq_refl. Qed.
  Lemma x11_after_B2_f : sr_get SR2e_f 11%bv = mkAlu ALU_ADD e_str0 (ELit 1).
  Proof. vmeq_refl. Qed.

  Lemma phase2_t : forall R M,
    regs_ok E7 SR2_t R -> know_ok SEGS E7 M KN1_t -> above_ok M -> mem_grows MEM0 M ->
    exists R' M', msteps SEGS (mkst R (Z_to_bv 64 A_envloop_exit) M ROM) (mkst R' (Z_to_bv 64 A_pnloop_exit) M' ROM)
      /\ regs_ok E7 SR3_t R' /\ know_ok SEGS E7 M' KN3_t /\ above_ok M' /\ mem_grows MEM0 M'.
  Proof.
    intros R M HR HK HA HG.
    pose proof usp_lo as SL. pose proof usp_fit as SF. pose proof len_av as LA. pose proof len_ev as LE.
    pose proof PN_range as PR. pose proof s0_len as SLEN.
    assert (US0 : bv_unsigned (edenot E7 e_str0) = usp + CHD + PAD)
      by (unfold E7, usp, CHD, PAD; eapply u_e_str0;
          first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
    assert (US1 : bv_unsigned (edenot E7 e_str1) = usp + CHD + PAD + Z.of_nat (length s0) + 1)
      by (unfold E7, usp, CHD, PAD, s0; eapply u_e_str1;
          first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
    (* [comment removed for export] *)
    ms_block_with HR HK FUEL [A_pnloop] noscr NX0 R2 HR2 HK2 MS2.
    lazymatch type of HK2 with know_ok _ _ ?m _ => set (M2 := m) in * end.
    assert (A2 : above_ok M2).
    { unfold M2. apply above_ok_block; [exact HA | vmc]. }
    assert (G2 : mem_grows MEM0 M2) by (unfold M2; eapply mem_grows_trans; [exact HG | apply mem_denot_grows]).
    clearbody M2. clear HR HK HA HG.
    (* [comment removed for export] *)
    destruct (fetchd_some _ _ pnloop_code_m8) as (w0 & F0 & NE0 & D0).
    destruct (fetchd_some _ _ pnloop_code_m4) as (w1 & F1 & NE1 & D1).
    destruct (fetchd_some _ _ pnloop_code_0) as (w2 & F2 & NE2 & D2).
    destruct (fetchd_some _ _ pnloop_code_4) as (w3 & F3 & NE3 & D3).
    destruct (fetchd_some _ _ pnloop_code_8) as (w4 & F4 & NE4 & D4).
    (* [comment removed for export] *)
    assert (Hrd : forall j, (j <= length s0)%nat -> rdn SEGS M2 (Z_to_bv 64 (PN + Z.of_nat j)) 1 = Some [byte_at s0 j]).
    { let i := kidx KN2_t (is_kblob_k K_ARGV0) in
      pose proof (know_nth SEGS E7 M2 KN2_t i _ HK2 eq_refl) as KB.
      cbn [kentry_ok] in KB. destruct KB as (Hfl & Hlen & Hby).
      lazymatch type of Hlen with _ = elenZ E7 ?n =>
        assert (Elen : elenZ E7 n = Z.of_nat (length s0) + 1)
          by (rewrite <- Hlen; unfold E7, E0; cbn [eb blobs0 K_ARGV0 K_RND Nat.eqb]; rewrite length_app; cbn [length]; unfold s0; lia)
      end.
      lazymatch type of Hby with (forall i, _ -> M2 (Z_to_bv 64 (?st + i)) = _) =>
        assert (Est : st = PN)
      end.
      { unfold estart. cbn [a_base a_off].
        assert (Hak : snd e_strb = 16) by (vm_compute; reflexivity).
        assert (Hab : split_lit e_str0 = (fst e_strb, snd e_strb))
          by (unfold e_strb; destruct (split_lit e_str0); reflexivity).
        assert (Hsu : bv_unsigned (edenot E7 (fst e_strb)) + snd e_strb
                      = bv_unsigned (edenot E7 e_str0)).
        { unfold E7. eapply split_u;
            [ exact Hab
            | rewrite Hak; lia
            | unfold EntryKn.uE; fold E7; rewrite US0, Hak; pose proof usp_lo; unfold CHD, PAD; lia ]. }
        (* the chain's blob start is [e_strb] in normal form *)
        rewrite Hak in Hsu. let b := eval vm_compute in (fst e_strb) in change (fst e_strb) with b in Hsu.
        rewrite Hsu, US0. unfold PN. reflexivity. }
      intros j Hj. cbn [rdn].
      rewrite Est, Elen in Hby. rewrite (Hby (Z.of_nat j)) by lia. rewrite Nat2Z.id.
      unfold byte_at. unfold E7, E0. cbn [eb blobs0 K_ARGV0 K_RND Nat.eqb]. reflexivity. }
    assert (Hst : store_ok SEGS M2 (Z_to_bv 64 A_progname) 8 = true).
    { let i := kidx KN2_t (is_kwr_cov (ELit 0) A_progname 8) in
      eapply (kwr_store_ok_lit SEGS E7 M2 KN2_t i); [exact HK2 | reflexivity | ..]; unfold A_progname; lia. }
    destruct (pn_loop SEGS A_pnloop w0 w1 w2 w3 w4 ltac:(unfold A_pnloop; lia) F0 F1 F2 F3 F4 NE0 NE1 NE2 NE3 NE4 D0 D1 D2 D3 D4
                M2 ROM A_progname PN s0 ltac:(unfold A_progname; lia) ltac:(lia) ltac:(pose proof usp_lo; unfold A_progname, PN, usp, CHD, PAD; lia) s0_nonul Hrd Hst
                s0 0%nat R2 M2 eq_refl ltac:(lia))
      as (R3 & M3 & MS3 & (P11 & P13 & Pag) & (C1 & C2)).
    - rewrite (HR2 10%bv). reflexivity.
    - rewrite (HR2 11%bv). change (sr_get _ 11%bv) with (mkAlu ALU_ADD e_str0 (ELit 1)). rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. unfold v_add.
      apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite US0.
      change (1 mod 2 ^ 64) with 1. rewrite !Z.mod_small by (unfold PN, usp, CHD, PAD in *; lia). unfold PN. lia.
    - rewrite (HR2 12%bv). reflexivity.
    - apply cellrel_refl.
    - (* [comment removed for export] *)
      exists R3, M3. split; [|split; [|split; [|split]]].
      + eapply msteps_trans; [exact MS2|]. rewrite pnloop_exit_eq. exact MS3.
      + unfold SR3_t. apply (regs_ok_upd2 E7 _ R2 R3 11%bv 13%bv); try exact HR2;
          try (intros HH; apply (f_equal bv_unsigned) in HH; discriminate HH).
        * rewrite P11. symmetry. apply bv_eq. rewrite US1. rewrite u_small by (unfold PN, usp, CHD, PAD in *; lia).
          unfold PN. lia.
        * rewrite P13. reflexivity.
        * intros r Hra Hrb. apply Pag. intros [C|C]; [apply Hra | apply Hrb]; exact C.
      + unfold KN3_t. apply (know_change_keep SEGS E7 M2 M3); [exact HK2 | | exact C2].
        intros x Hx. apply C1. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx.
        rewrite !u_small in Hx by (unfold A_progname; lia). lia.
      + intros x Hx. rewrite C1; [apply A2; exact Hx|]. unfold A_progname. right. unfold usp in *. lia.
      + eapply mem_grows_trans; [exact G2 | exact C2].
  Qed.

  Lemma phase2_f : forall R M,
    regs_ok E7 SR2_f R -> know_ok SEGS E7 M KN1_f -> above_ok M -> mem_grows MEM0 M ->
    exists R' M', msteps SEGS (mkst R (Z_to_bv 64 A_envloop_exit) M ROM) (mkst R' (Z_to_bv 64 A_pnloop_exit) M' ROM)
      /\ regs_ok E7 SR3_f R' /\ know_ok SEGS E7 M' KN3_f /\ above_ok M' /\ mem_grows MEM0 M'.
  Proof.
    intros R M HR HK HA HG.
    pose proof usp_lo as SL. pose proof usp_fit as SF. pose proof len_av as LA. pose proof len_ev as LE.
    pose proof PN_range as PR. pose proof s0_len as SLEN.
    assert (US0 : bv_unsigned (edenot E7 e_str0) = usp + CHD + PAD)
      by (unfold E7, usp, CHD, PAD; eapply u_e_str0;
          first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
    assert (US1 : bv_unsigned (edenot E7 e_str1) = usp + CHD + PAD + Z.of_nat (length s0) + 1)
      by (unfold E7, usp, CHD, PAD, s0; eapply u_e_str1;
          first [eassumption | exact Hhi' | exact Hlo' | exact Hwlo_sp | exact PH]).
    (* [comment removed for export] *)
    ms_block_with HR HK FUEL [A_pnloop] noscr NX0 R2 HR2 HK2 MS2.
    lazymatch type of HK2 with know_ok _ _ ?m _ => set (M2 := m) in * end.
    assert (A2 : above_ok M2).
    { unfold M2. apply above_ok_block; [exact HA | vmc]. }
    assert (G2 : mem_grows MEM0 M2) by (unfold M2; eapply mem_grows_trans; [exact HG | apply mem_denot_grows]).
    clearbody M2. clear HR HK HA HG.
    (* [comment removed for export] *)
    destruct (fetchd_some _ _ pnloop_code_m8) as (w0 & F0 & NE0 & D0).
    destruct (fetchd_some _ _ pnloop_code_m4) as (w1 & F1 & NE1 & D1).
    destruct (fetchd_some _ _ pnloop_code_0) as (w2 & F2 & NE2 & D2).
    destruct (fetchd_some _ _ pnloop_code_4) as (w3 & F3 & NE3 & D3).
    destruct (fetchd_some _ _ pnloop_code_8) as (w4 & F4 & NE4 & D4).
    (* [comment removed for export] *)
    assert (Hrd : forall j, (j <= length s0)%nat -> rdn SEGS M2 (Z_to_bv 64 (PN + Z.of_nat j)) 1 = Some [byte_at s0 j]).
    { let i := kidx KN2_f (is_kblob_k K_ARGV0) in
      pose proof (know_nth SEGS E7 M2 KN2_f i _ HK2 eq_refl) as KB.
      cbn [kentry_ok] in KB. destruct KB as (Hfl & Hlen & Hby).
      lazymatch type of Hlen with _ = elenZ E7 ?n =>
        assert (Elen : elenZ E7 n = Z.of_nat (length s0) + 1)
          by (rewrite <- Hlen; unfold E7, E0; cbn [eb blobs0 K_ARGV0 K_RND Nat.eqb]; rewrite length_app; cbn [length]; unfold s0; lia)
      end.
      lazymatch type of Hby with (forall i, _ -> M2 (Z_to_bv 64 (?st + i)) = _) =>
        assert (Est : st = PN)
      end.
      { unfold estart. cbn [a_base a_off].
        assert (Hak : snd e_strb = 16) by (vm_compute; reflexivity).
        assert (Hab : split_lit e_str0 = (fst e_strb, snd e_strb))
          by (unfold e_strb; destruct (split_lit e_str0); reflexivity).
        assert (Hsu : bv_unsigned (edenot E7 (fst e_strb)) + snd e_strb
                      = bv_unsigned (edenot E7 e_str0)).
        { unfold E7. eapply split_u;
            [ exact Hab
            | rewrite Hak; lia
            | unfold EntryKn.uE; fold E7; rewrite US0, Hak; pose proof usp_lo; unfold CHD, PAD; lia ]. }
        (* the chain's blob start is [e_strb] in normal form *)
        rewrite Hak in Hsu. let b := eval vm_compute in (fst e_strb) in change (fst e_strb) with b in Hsu.
        rewrite Hsu, US0. unfold PN. reflexivity. }
      intros j Hj. cbn [rdn].
      rewrite Est, Elen in Hby. rewrite (Hby (Z.of_nat j)) by lia. rewrite Nat2Z.id.
      unfold byte_at. unfold E7, E0. cbn [eb blobs0 K_ARGV0 K_RND Nat.eqb]. reflexivity. }
    assert (Hst : store_ok SEGS M2 (Z_to_bv 64 A_progname) 8 = true).
    { let i := kidx KN2_f (is_kwr_cov (ELit 0) A_progname 8) in
      eapply (kwr_store_ok_lit SEGS E7 M2 KN2_f i); [exact HK2 | reflexivity | ..]; unfold A_progname; lia. }
    destruct (pn_loop SEGS A_pnloop w0 w1 w2 w3 w4 ltac:(unfold A_pnloop; lia) F0 F1 F2 F3 F4 NE0 NE1 NE2 NE3 NE4 D0 D1 D2 D3 D4
                M2 ROM A_progname PN s0 ltac:(unfold A_progname; lia) ltac:(lia) ltac:(pose proof usp_lo; unfold A_progname, PN, usp, CHD, PAD; lia) s0_nonul Hrd Hst
                s0 0%nat R2 M2 eq_refl ltac:(lia))
      as (R3 & M3 & MS3 & (P11 & P13 & Pag) & (C1 & C2)).
    - rewrite (HR2 10%bv). reflexivity.
    - rewrite (HR2 11%bv). change (sr_get _ 11%bv) with (mkAlu ALU_ADD e_str0 (ELit 1)). rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. unfold v_add.
      apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite US0.
      change (1 mod 2 ^ 64) with 1. rewrite !Z.mod_small by (unfold PN, usp, CHD, PAD in *; lia). unfold PN. lia.
    - rewrite (HR2 12%bv). reflexivity.
    - apply cellrel_refl.
    - (* [comment removed for export] *)
      exists R3, M3. split; [|split; [|split; [|split]]].
      + eapply msteps_trans; [exact MS2|]. rewrite pnloop_exit_eq. exact MS3.
      + unfold SR3_f. apply (regs_ok_upd2 E7 _ R2 R3 11%bv 13%bv); try exact HR2;
          try (intros HH; apply (f_equal bv_unsigned) in HH; discriminate HH).
        * rewrite P11. symmetry. apply bv_eq. rewrite US1. rewrite u_small by (unfold PN, usp, CHD, PAD in *; lia).
          unfold PN. lia.
        * rewrite P13. reflexivity.
        * intros r Hra Hrb. apply Pag. intros [C|C]; [apply Hra | apply Hrb]; exact C.
      + unfold KN3_f. apply (know_change_keep SEGS E7 M2 M3); [exact HK2 | | exact C2].
        intros x Hx. apply C1. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx.
        rewrite !u_small in Hx by (unfold A_progname; lia). lia.
      + intros x Hx. rewrite C1; [apply A2; exact Hx|]. unfold A_progname. right. unfold usp in *. lia.
      + eapply mem_grows_trans; [exact G2 | exact C2].
  Qed.

  Lemma phase1 : forall rs, kb_rseq (in_kernel inp) = rs -> exists R M,
      msteps SEGS (mkst (R0 sp) (Z_to_bv 64 A_start) MEM0 ROM) (mkst R (Z_to_bv 64 A_envloop_exit) M ROM)
      /\ regs_ok E7 (SR2r rs) R /\ know_ok SEGS E7 M (KN1r rs) /\ above_ok M /\ mem_grows MEM0 M.
  Proof using Hsp Hva Hve Hvl Hlau Huid. intros [] Hrs; [exact (phase1_t Hrs) | exact (phase1_f Hrs)]. Qed.

  Lemma phase2 : forall rs R M,
    regs_ok E7 (SR2r rs) R -> know_ok SEGS E7 M (KN1r rs) -> above_ok M -> mem_grows MEM0 M ->
    exists R' M', msteps SEGS (mkst R (Z_to_bv 64 A_envloop_exit) M ROM) (mkst R' (Z_to_bv 64 A_pnloop_exit) M' ROM)
      /\ regs_ok E7 (SR3r rs) R' /\ know_ok SEGS E7 M' (KN3r rs) /\ above_ok M' /\ mem_grows MEM0 M'.
  Proof using Hsp Hva Hve Hvl Hlau. intros []; [exact phase2_t | exact phase2_f]. Qed.

End Walk.
End TwB.
(* [comment removed for export] *) Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
