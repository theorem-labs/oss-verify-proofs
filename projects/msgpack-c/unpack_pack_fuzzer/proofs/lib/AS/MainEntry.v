(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's whole ProcInput and kernel build; Linux's stack block, with the pad between the AT_RANDOM bytes and argv[0] and the string area up to the stack VMA's end; the main entry's states computed per CONFIG_RSEQ value by the start-up certificates, the recorded facts renumbered by a map read from a probe run, and the recorded fact lists kept by a fixed rule, a fact no remade list holds replaced in place by a trivially true one; the channel reader of the start state; the model's mappings apart from the reservations and the vDSO top bound; asan_side_ok lifts the walk to the run's segment list by RomStable.srun_init). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanStartup StartupHS2Asan AsanBoot
  PlanRegen AsanStartupCert2 MainRenum MainRegen
  RegsEqv0 SrzEqv MainExport MainFactsAsan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require RomStable.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore TopLevelGen.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require Import TopLevel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Definition AMAIN : Z := 0x8c6e8.
Definition ARA : Z := 0xbd320.
Definition AGP : Z := 0x10800.
Definition ATP : Z := 0x60cc80.
Definition AIMG_LO : Z := 0x10000.
Definition AIMG_HI : Z := 0x62f000.
Definition ACEIL : Z := 0x7fff7f800000.
Definition KHIGH : Z := 0x10007fff8000.
Definition ASHOFF : Z := 0x7fff8000.
Definition ABAND_LO : Z := 0x7fff7000.
Definition ABAND_LEN : Z := 0x100000001000.
Definition V_VMBRK : nat := 452.

Lemma asegs_ASEGS : ASEGS = asegs. Proof. reflexivity. Qed.
Lemma aph_APH : APH = a_phdrs. Proof. reflexivity. Qed.

(* LPS 727298f3: the start-up run numbers its fresh variables differently (the launch variable
   [V_GID], the longer auxv), so the hand-off states at main ([HM1 r], [HM2 r], computed in the
   build by AsanStartupCert2) name the main entry's variables at other numbers than the recorded
   facts of MainFactsAsan.  [FM] is that renumbering, the startup2 map read from a probe run
   (AsanStartupCert2.vsh2); the facts keep their recorded numbering and are stated about
   [fun n => V' (FM n)], [V'] the run's own variables (MainRenum). *)
Definition FM : nat -> nat := mapf vsh2.
Lemma FM_low : forall n, (n < 13)%nat -> FM n = n.
Proof.
  intros n Hn. unfold FM, mapf, vsh2. cbn [fold_left fst snd].
  repeat (rewrite (proj2 (Nat.leb_gt _ _)) by lia). reflexivity.
Qed.

(* the main entry's facts per CONFIG_RSEQ value [r] and hand-off [w]: the recorded ones (MainFactsAsan), remade
   from the computed main-entry state by MainRegen's rule (auxv facts from the state's own auxv claims, other facts
   the state no longer justifies by its single fact of the same kind there, a fact with no such fact dropped),
   computed in the build *)
Definition AW (w : bool) : list mfact := asan_mem_facts ++ (if w then asan_mem_facts_w1 else asan_mem_facts_w2).
Definition PW (w : bool) : list pfact := asan_pure_facts ++ (if w then asan_pure_facts_w1 else asan_pure_facts_w2).
Definition rmf (hs : acs) (l : list mfact) : list mfact := remake_facts (kn hs) AIMG_LO AIMG_HI vsh2 l.
Definition rpf (hs : acs) (l : list pfact) : list pfact := remake_pfacts (kn hs) vsh2 l.
Definition AMF0T : list mfact := Eval vm_compute in rmf (HM1 0) (AW true).
Definition AMF1T : list mfact := Eval vm_compute in rmf (HM1 1) (AW true).
Definition AMF0F : list mfact := Eval vm_compute in rmf (HM2 0) (AW false).
Definition AMF1F : list mfact := Eval vm_compute in rmf (HM2 1) (AW false).
Definition APF0T : list pfact := Eval vm_compute in rpf (HM1 0) (PW true).
Definition APF1T : list pfact := Eval vm_compute in rpf (HM1 1) (PW true).
Definition APF0F : list pfact := Eval vm_compute in rpf (HM2 0) (PW false).
Definition APF1F : list pfact := Eval vm_compute in rpf (HM2 1) (PW false).
Definition amf (r : Z) (w : bool) : list mfact :=
  if w then (if Z.eqb r 1 then AMF1T else AMF0T) else (if Z.eqb r 1 then AMF1F else AMF0F).
Definition apf (r : Z) (w : bool) : list pfact :=
  if w then (if Z.eqb r 1 then APF1T else APF0T) else (if Z.eqb r 1 then APF1F else APF0F).

(* The recorded lists as the main-phase proofs read them (by index or by membership), filtered by a fixed rule
   computed in the build: a recorded fact that every remade list still holds ([amf r w] at both values of [r], and
   at both [w] for the facts common to the two hand-offs) is kept in its place; any other is replaced IN PLACE by
   a fact true of every memory ([MImg 0 0]; [PDisj 0 0 0 0] for the pure facts), so no index moves, and a proof
   that needs a changed fact fails at its own membership or index check. *)
Definition kept_m (ls : list (list mfact)) (f : mfact) : mfact :=
  if forallb (fun l => existsb (mfact_eqb f) l) ls then f else MImg 0 0.
Definition pfact_eqb (f g : pfact) : bool :=
  match f, g with
  | PVar n lo hi, PVar n' lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
  | PRange e lo hi, PRange e' lo' hi' => zexp_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | PDisj a1 n1 a2 n2, PDisj a1' n1' a2' n2' => zexp_eqb a1 a1' && Z.eqb n1 n1' && zexp_eqb a2 a2' && Z.eqb n2 n2'
  | PDisjS a1 n1 a2 n2, PDisjS a1' n1' a2' n2' => zexp_eqb a1 a1' && zexp_eqb n1 n1' && zexp_eqb a2 a2' && zexp_eqb n2 n2'
  | _, _ => false
  end.
Lemma pfact_eqb_eq : forall f g, pfact_eqb f g = true -> f = g.
Proof.
  intros f g H. destruct f, g; cbn in H; try discriminate;
    repeat match goal with K : (_ && _) = true |- _ => apply andb_prop in K as [? K] end;
    repeat match goal with
           | K : zexp_eqb _ _ = true |- _ => apply zexp_eqb_eq in K
           | K : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in K
           | K : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in K end; subst; reflexivity.
Qed.
Definition kept_p (ls : list (list pfact)) (f : pfact) : pfact :=
  if forallb (fun l => existsb (pfact_eqb f) l) ls then f else PDisj (ZLit 0) 0 (ZLit 0) 0.
Definition AMKN : list mfact := Eval vm_compute in map (kept_m [AMF0T; AMF1T; AMF0F; AMF1F]) asan_mem_facts.
Definition AMKN1 : list mfact := Eval vm_compute in map (kept_m [AMF0T; AMF1T]) asan_mem_facts_w1.
Definition AMKN2 : list mfact := Eval vm_compute in map (kept_m [AMF0F; AMF1F]) asan_mem_facts_w2.
Definition AMKNW (w : bool) : list mfact := if w then AMKN1 else AMKN2.
Definition APKN : list pfact := Eval vm_compute in map (kept_p [APF0T; APF1T; APF0F; APF1F]) asan_pure_facts.
Lemma AMKN_eq : AMKN = map (kept_m [AMF0T; AMF1T; AMF0F; AMF1F]) asan_mem_facts. Proof. vm_compute. reflexivity. Qed.
Lemma AMKN1_eq : AMKN1 = map (kept_m [AMF0T; AMF1T]) asan_mem_facts_w1. Proof. vm_compute. reflexivity. Qed.
Lemma AMKN2_eq : AMKN2 = map (kept_m [AMF0F; AMF1F]) asan_mem_facts_w2. Proof. vm_compute. reflexivity. Qed.
Lemma APKN_eq : APKN = map (kept_p [APF0T; APF1T; APF0F; APF1F]) asan_pure_facts. Proof. vm_compute. reflexivity. Qed.

Lemma kept_m_ok : forall segs V m ls L l0, In L ls -> Forall (mfact_ok segs V m) L -> Forall (mfact_ok segs V m) (map (kept_m ls) l0).
Proof.
  intros segs V m ls L l0 HL HF. apply Forall_forall. intros g Hg. apply in_map_iff in Hg as (f & <- & _).
  unfold kept_m. destruct (forallb (fun l => existsb (mfact_eqb f) l) ls) eqn:E.
  - apply (mfact_find segs V m L f HF). exact (proj1 (forallb_forall _ _) E L HL).
  - cbn [mfact_ok]. intros i Hi. exfalso. lia.
Qed.
Lemma kept_p_ok : forall V ls L l0, In L ls -> Forall (pfact_ok V) L -> Forall (pfact_ok V) (map (kept_p ls) l0).
Proof.
  intros V ls L l0 HL HF. apply Forall_forall. intros g Hg. apply in_map_iff in Hg as (f & <- & _).
  unfold kept_p. destruct (forallb (fun l => existsb (pfact_eqb f) l) ls) eqn:E.
  - pose proof (proj1 (forallb_forall _ _) E L HL) as X. cbv beta in X.
    apply existsb_exists in X as (g & Hin & Hg). apply pfact_eqb_eq in Hg. subst g.
    exact (proj1 (Forall_forall _ _) HF f Hin).
  - cbn [pfact_ok zv]. lia.
Qed.
(* what a main-phase proof reads off [amain_at]'s facts *)
Lemma keep_facts : forall segs V m r w,
  Forall (mfact_ok segs V m) (amf r w) -> Forall (pfact_ok V) (apf r w) ->
  Forall (mfact_ok segs V m) AMKN /\ Forall (mfact_ok segs V m) (AMKNW w) /\ Forall (pfact_ok V) APKN.
Proof.
  intros segs V m r w HM HP.
  assert (IM : In (amf r w) [AMF0T; AMF1T; AMF0F; AMF1F])
    by (unfold amf; destruct w, (Z.eqb r 1); cbn [In]; repeat (first [left; reflexivity | right])).
  assert (IP : In (apf r w) [APF0T; APF1T; APF0F; APF1F])
    by (unfold apf; destruct w, (Z.eqb r 1); cbn [In]; repeat (first [left; reflexivity | right])).
  assert (IW : In (amf r w) (if w then [AMF0T; AMF1T] else [AMF0F; AMF1F]))
    by (unfold amf; destruct w, (Z.eqb r 1); cbn [In]; repeat (first [left; reflexivity | right])).
  split; [rewrite AMKN_eq; exact (kept_m_ok segs V m _ _ asan_mem_facts IM HM)|].
  split; [|rewrite APKN_eq; exact (kept_p_ok V _ _ asan_pure_facts IP HP)].
  unfold AMKNW. destruct w; [rewrite AMKN1_eq | rewrite AMKN2_eq]; exact (kept_m_ok segs V m _ _ _ IW HM).
Qed.
(* the reserved-and-mapped total the computed states carry (the vDSO pair's 20 pages more than recorded) *)
Definition ATOTSZ : Z := Eval vm_compute in
  Z.max (Z.max (a_totsz (HM1 0)) (a_totsz (HM1 1))) (Z.max (a_totsz (HM2 0)) (a_totsz (HM2 1))).
(* the stack window below sp the start state states (AsanPlanCore's [KWr (SA e_sp0 (-6144513)) (ELit 6144513)]) *)
Definition STKA : zexp := ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-6144513)).

Record amodel (V : nat -> Z) (sp : word) (fs : Fs.Fs) (mo : Model) : Prop := AMODEL {
  am_halted   : m_halted mo = None;
  am_fds      : m_fds mo = [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
                            (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))];
  am_fs       : m_fs mo = fs;
  (* [State.init_reserved] appends the vdso/vvar pair to the image's
     reservations, so the ledger is the two appended.  Same shape as
     [APS.co_res], which is what supplies this field. *)
  am_reserved : vm_reserved (m_vmmaps mo)
                = segments_reserved asegs ++ vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo));
  am_limit    : vm_limit (m_vmmaps mo) = target_alloc_limit;
  am_brk      : vm_brk (m_vmmaps mo) = Z_to_bv 64 (V V_VMBRK);
  am_start_brk : bv_unsigned (vm_start_brk (m_vmmaps mo)) <= V V_VMBRK;

  am_top      : vm_init_sp (m_vmmaps mo) = sp;
  am_usp      : 0x7fff80000000 <= bv_unsigned sp /\ bv_unsigned sp <= 0x800000000000 /\ bv_unsigned sp mod 16 = 0;

  am_maps     : ledger_den V asan_ledger (vm_maps (m_vmmaps mo));
  am_kinds    : Forall (lentry_kind_ok V mo) asan_ledger;
  am_sep      : ivs_sep (vm_maps (m_vmmaps mo));
  am_bounds   : Forall (fun iv => 0 < bv_unsigned (snd iv) /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                                  /\ 0 < bv_unsigned (fst iv)
                                  /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= AIMG_LO \/ AIMG_HI <= bv_unsigned (fst iv))
                                  /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned sp - 8388608)
                       (vm_maps (m_vmmaps mo));
  am_lazy_bounds : Forall (fun iv => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= AIMG_LO \/ AIMG_HI <= bv_unsigned (fst iv))
                                     /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned sp - 8388608)
                          (m_vm_lazy mo);
  am_noaccess_wf : Forall (fun iv => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= 2 ^ 64) (vm_noaccess (m_vmmaps mo));
  am_noaccess_sub : forall z, MainExport.in_ivs z (vm_noaccess (m_vmmaps mo)) -> MainExport.in_ivs z (vm_maps (m_vmmaps mo));
  am_totsz    : ivs_sum (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) <= ATOTSZ;

  am_nonlazy  : nonlazy_bytes mo <= asan_eager;
  am_abytes   : ivz_bytes (allow_of ASHOFF V asan_vis) <= asan_abytes;
  am_budget   : nonlazy_bytes mo + ivz_bytes (allow_of ASHOFF V asan_vis) <= target_alloc_limit;
  am_allow_wf : ivz_wf (allow_of ASHOFF V asan_vis);
  am_mat_nodup : List.NoDup (m_vm_materialized mo);
  am_mat      : forall p, In p (m_vm_materialized mo) ->
                  bv_unsigned p mod 4096 = 0 /\ page_in_ranges p (m_vm_lazy mo) = true /\ aallowed (allow_of ASHOFF V asan_vis) p;

  am_lazy_sub : forall z, MainExport.in_ivs z (m_vm_lazy mo) -> MainExport.in_ivs z (vm_maps (m_vmmaps mo));
  am_noaccess_nz : Forall (fun e => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mo));
  am_fake_eager : forall a, 4096 * V 377%nat <= a < 4096 * V 377%nat + 11571200 -> page_in_ranges (page_base_of a) (m_vm_lazy mo) = false;
  (* LPS 08b1429: the far-end reader, seeded at launch from [in_channel_reader] ([valid_input]);
     the start-up chain carries it as [APS.co_rdr]. *)
  am_reader   : m_channel_reader mo = true;
  (* LPS 727298f3: the reserved ledger holds the launch's vdso/vvar pair ([am_reserved]); every mapping
     is apart from the whole ledger ([APS.co_mres]), and the pair's top is at or above the mmap base's
     floor ([APS.co_vtop]; [AsanPlanCore.MBASE_MIN] = [State.mmap_base_min]). *)
  am_mres     : Forall (fun iv => Forall (fun q => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned (fst q)
                                              \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst iv))
                                   (vm_reserved (m_vmmaps mo)))
                       (vm_maps (m_vmmaps mo));
  am_vtop     : 0x154555557000 <= vdso_top (m_vmmaps mo)
}.

(* LPS 727298f3: Linux's stack block.  The arch_align_stack pad [Wpad] sits between the AT_RANDOM
   bytes and argv[0] (it was the strings' padding, below the random bytes); the string area runs
   from [STR0_of] (argv[0]) to the stack VMA's end.  [AsanInit.argH0]'s two ranges, in the entry's
   own terms. *)
Definition RZ_of (inp : ProcInput) : Z := rseq_z (kb_rseq (in_kernel inp)).
Definition Wpad (en : ExecEntry) (inp : ProcInput) : Z :=
  Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) (en_sp en) (ed_top (en_draw en)) (in_argv inp) (in_envp inp) (in_execfn inp)).
Definition STR0_of (en : ExecEntry) (inp : ProcInput) : Z :=
  bv_unsigned (en_sp en) + Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)) + Wpad en inp.

Definition hidden_arg (en : ExecEntry) (inp : ProcInput) (a : Z) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
  (usp + 8 * argc + 16 <= a < usp + 8 * argc + 8 * envc + 24)
  \/ (STR0_of en inp <= a < bv_unsigned (ed_top (en_draw en))).

Definition ashadow (a : Z) : Prop := (0x7fff7000 <= a < 0x8fff7000) \/ (0x2008fff7000 <= a < 0x10007fff8000).
Definition ASHADOWS : list (Z * Z) := [(0x7fff7000, 0x8fff7000); (0x2008fff7000, 0x10007fff8000)].
Definition ashadow_vis (V : nat -> Z) (a : Z) : Prop :=
  exists bn, In bn asan_vis_app /\ ASHOFF + zv V (fst bn) / 8 <= a < ASHOFF + (zv V (fst bn) + zv V (snd bn)) / 8.

Definition ashadow0 (V : nat -> Z) (m : word -> option byte) : Prop :=
  forall a, ashadow a -> ~ ashadow_vis V a -> m (wa a) = Some (Z_to_bv 8 0).

Definition amain_at (en : ExecEntry) (inp : ProcInput) (ms : machine_state) (mo : Model) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
  exists (w : bool) (V : nat -> Z) (m : word -> option byte),
    ms = MS (mkR (Z_to_bv 64 ARA) (Z_to_bv 64 (usp - 48)) (Z_to_bv 64 AGP) (Z_to_bv 64 ATP)
                 (Z_to_bv 64 (V 856%nat)) (Z_to_bv 64 (V 857%nat)) (Z_to_bv 64 (V 858%nat))
                 (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (usp + 8))
                 (Z_to_bv 64 (usp + 8 * argc + 16)) (Z_to_bv 64 0x6000000000000000)
                 (Z_to_bv 64 (V 859%nat)) (Z_to_bv 64 (V 860%nat)) (Z_to_bv 64 (V 861%nat)) (Z_to_bv 64 (V 862%nat))
                 (Z_to_bv 64 AMAIN) (Z_to_bv 64 (usp + 8 * argc + 16))
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 (V 863%nat)) (Z_to_bv 64 (V 864%nat)) (Z_to_bv 64 (V 865%nat)) (Z_to_bv 64 (V 866%nat)))
            bvmap_empty (Z_to_bv 64 AMAIN) (Z_to_bv 32 0) None m (seg_rom asegs)
    /\ (forall n, 0 <= V n < 2 ^ 64)

    /\ (V 0%nat = usp / 32768 /\ V 6%nat = usp mod 4096 / 16 /\ V 10%nat = usp mod 32768 / 4096
        /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp
        /\ V 1%nat = argc /\ V 2%nat = envc
        /\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) [])) /\ V 7%nat = Z.of_nat (length (nth 1 (in_argv inp) []))
        /\ V 4%nat = Wpad en inp /\ V 5%nat = bv_unsigned (en_brk en) / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
        /\ V 9%nat = bv_unsigned (in_hwcap inp)
        /\ V 11%nat = Z.of_nat (block_items (in_argv inp) (in_envp inp) mod 2))
    /\ Forall (mfact_ok asegs V m) (amf (RZ_of inp) w)
    /\ Forall (pfact_ok V) (apf (RZ_of inp) w)
    /\ mem_inv asegs m
    /\ stk asegs m (usp - 6144513) usp
    /\ (forall a, hidden_arg en inp a ->
          m (wa a) = wrap_mem inp (en_mmap_base en) a_phdrs (Z_to_bv 64 (a_entry ASAN)) (en_sp en) (en_draw en) (wa a))
    /\ ashadow0 V m
    /\ amodel V (en_sp en) (in_fs inp) mo.

Lemma ashadow0_range : forall V m lo n,
  ashadow0 V m -> 0 < n ->
  (forall a, lo <= a < lo + n -> ashadow a /\ ~ ashadow_vis V a) ->
  (forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0))
  /\ wr_at asegs m lo n /\ rw_cells asegs m lo [CB (Z.to_nat n) (zeros n)].
Proof.
  intros V m lo n H0 Hn HR.
  assert (Z0 : forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. destruct (HR (lo + i) ltac:(lia)) as (S1 & S2). exact (H0 _ S1 S2). }
  split; [exact Z0|].
  destruct (HR lo ltac:(lia)) as (Slo & _). destruct (HR (lo + n - 1) ltac:(lia)) as (Shi & _). unfold ashadow in Slo, Shi.
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
  range_clear ASHADOWS VR bn || band_fact ABAND_LO ABAND_LEN PF bn.

Lemma shad_clear_sound : forall V VR PF bn a, vr_sound V VR -> Forall (pfact_ok V) PF -> shad_clear VR PF bn = true ->
  (exists s, In s ASHADOWS /\ fst s <= a < snd s) -> ~ (zv V (fst bn) <= a < zv V (fst bn) + zv V (snd bn)).
Proof.
  intros V VR PF bn a HV HPF H HS. unfold shad_clear in H. apply orb_prop in H as [H|H].
  - exact (range_clear_sound V VR ASHADOWS bn a HV H HS).
  - apply (band_fact_sound V ABAND_LO ABAND_LEN PF bn a HPF H).
    destruct HS as (s & Hs & Ha). unfold ABAND_LO, ABAND_LEN. cbn in Hs. destruct Hs as [<-|[<-|[]]]; cbn in Ha; lia.
Qed.

(* the recorded main-entry registers, renumbered by [FM] (the computed states hold exactly these:
   checked by [regs_HM1] / [regs_HM2] below) *)
Definition AREGS : list expr := Eval vm_compute in map (esh FM) (s_regs (a_ss HS_asan2_1)).

(* what the bridge reads off a computed main-entry state [hs] (hand-off 1 when [w], 2 otherwise) at
   CONFIG_RSEQ value [r]: its registers, pc, descriptor table and break are the recorded ones
   renumbered, and the facts, visible ranges and ledger, renumbered, are justified by it *)
Definition JUST (r : Z) (w : bool) (hs : acs) : Prop :=
  s_regs (a_ss hs) = AREGS /\ pc hs = AMAIN /\ a_fd hs = FdStd /\ a_brk hs = EVar (FM V_VMBRK)
  /\ forallb (mjustify (kn hs) (var_ranges (kn hs)) AIMG_LO AIMG_HI) (map (msh FM) (amf r w)) = true
  /\ forallb (pjustify (kn hs) (var_ranges (kn hs))) (map (pfsh FM) (apf r w)) = true
  /\ (vis_match (var_ranges (kn hs)) (a_vis hs) (map (bnsh FM) asan_vis_app) = true
      /\ vis_match (var_ranges (kn hs)) (a_ghost hs) (map (bnsh FM) asan_ghost) = true)
  /\ ledger_xmatch (var_ranges (kn hs)) (a_maps hs) (map (lsh FM) asan_ledger) = true
  /\ ((a_totsz hs <=? ATOTSZ) && (a_eager hs <=? asan_eager) && (a_abytes hs <=? asan_abytes))%bool = true
  /\ existsb (fun f => match f with MImg lo' hi' => (lo' <=? 0x10000) && (0xcd000 <=? hi') | _ => false end) (amf r w) = true
  /\ existsb (fun f => match f with MWr a' n' => zexp_eqb a' STKA && (n' =? 6144513) | _ => false end) (amf r w) = true
  /\ forallb (shad_clear (pvranges (apf r w)) (apf r w)) asan_vis_app = true
  /\ forallb (shad_clear (pvranges (apf r w)) (apf r w)) asan_ghost = true
  /\ existsb (fun f => match f with PVar n lo hi => (Nat.eqb n 377 && (0 <=? lo) && (hi <=? 2 ^ 40))%bool | _ => false end) (apf r w) = true.

Section Bridge.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable ifs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nof sigm : word.
  Variable abt : bool.
  Variable urnd : InputStream.
  Variable tmpf : Fs.Fs.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variables chrdr sigdef sigterm : bool.
  #[local] Notation INP := (AsanInit.inp argv envp ifs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm).
  #[local] Notation fs := (in_fs INP).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  Hypothesis Hrdr : in_channel_reader INP = true.

  Definition en0 : ExecEntry := mkEntry sp brk0 mbase rdraw.
  Definition inp0 : ProcInput := INP.

  #[local] Notation SINV := (SINV0 ASAN APH sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm).
  #[local] Notation argH := (argH0 sp rdraw argv envp kb execfn).
  #[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 argv envp uid gid hw kb execfn).
  #[local] Notation LIM := AsanInit.LIMIT.
  #[local] Notation RZ := (rseq_z (kb_rseq kb)).
  Let RZr : 0 <= RZ <= 1 := rseq_z_range (kb_rseq kb).

  (* AsanInit's lemmas take the atable / headers / image facts their proofs use; the goal fixes
     the rest, the section's hypotheses give the launch.  The hypotheses are given first
     ([unshelve (eapply _; CL); CL]), so that they fix the values they name (a value goal given first
     would take the context's last value of its type); only the values nothing fixes are filled after *)
  Local Ltac CL := first [eassumption | exact ASAN | exact APH | exact ASEGS | exact asan_img_facts].

  Let AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Proof. intros E a Ha. eapply argH0_high; eassumption. Qed.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).

  Lemma sinv_usp : forall E M, SINV E M -> uE E e_sp0 = usp.
  Proof.
    intros E M [HE _].
    transitivity (uE E0a e_sp0); [| unshelve (eapply AsanInit.u_e_sp0; CL); CL].
    unfold e_sp0, uE. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot].
    rewrite !HE by (unfold NX0, V_S1, V_S2, V_SP; lia). reflexivity.
  Qed.

  Lemma u_launch :
    uE E0a (EVar V_S1) = usp / 32768 /\ uE E0a (EVar V_S2) = (usp mod 4096) / 16
    /\ uE E0a (EVar V_ARGC) = argc /\ uE E0a (EVar V_ENVC) = envc
    /\ uE E0a (EVar V_L0) = Z.of_nat (length (nth 0 argv []))
    /\ uE E0a (EVar V_W) = Wpad en0 inp0 /\ uE E0a (EVar V_BRK) = bv_unsigned brk0 / 4096
    /\ uE E0a (EVar V_SP) = (usp mod 32768) / 4096
    /\ uE E0a (EVar V_L1) = Z.of_nat (length (nth 1 argv []))
    /\ uE E0a (EVar V_UID) = bv_unsigned uid /\ uE E0a (EVar V_HW) = bv_unsigned hw
    /\ uE E0a (EVar V_G) = Z.of_nat (block_items argv envp mod 2).
  Proof.
    assert (U : uE E0a (EVar V_S1) = usp / 32768 /\ uE E0a (EVar V_S2) = (usp mod 4096) / 16
    /\ uE E0a (EVar V_ARGC) = argc /\ uE E0a (EVar V_ENVC) = envc
    /\ uE E0a (EVar V_L0) = Z.of_nat (length (nth 0 argv []))
    /\ uE E0a (EVar V_W) = Wpad en0 inp0 /\ uE E0a (EVar V_BRK) = bv_unsigned brk0 / 4096
    /\ uE E0a (EVar V_G) = Z.of_nat (block_items argv envp mod 2)) by (unshelve (eapply AsanInit.uE0; CL); CL).
    destruct U as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8).
    assert (U9 : uE E0a (EVar V_SP) = (usp mod 32768) / 4096) by (unshelve (eapply AsanInit.uE0_sp; CL); CL).
    assert (U10 : uE E0a (EVar V_L1) = Z.of_nat (length (nth 1 argv []))) by (unshelve (eapply AsanInit.uE0_L1; CL); CL).
    repeat split; try assumption; reflexivity.
  Qed.

  Theorem amain_bridge_w : forall (w : bool) (hs : acs), JUST RZ w hs ->
    forall E R FULL mo,
    cs_ok ASEGS ASAN LIM SINV argH fs E hs R FULL mo ->
    exists ms, cfg_eqv (cfg_of ASEGS R (pc hs) FULL mo) (mkCfg ms mo) /\ amain_at en0 inp0 ms mo.
  Proof.
    intros w hs (Hregs & Hpc & Hfd & Hbrk0 & MJ & PJ & VJ & LJ & CONSTS & IMGc & STKc & CLRv & CLRg & VB) E R FULL mo HC. rewrite Hpc.
    set (V := Vf FM (uev E)).
    assert (HVl : forall n, (n < 13)%nat -> V n = uev E n).
    { intros n Hn. unfold V, Vf. rewrite (FM_low n Hn). reflexivity. }

    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as HSINV. pose proof HSINV as [Hev Hhid].
    pose proof (sinv_usp E FULL HSINV) as USP.
    pose proof u_launch as (U0 & U6 & U1 & U2 & U3 & U4 & U5 & U10 & U7 & U8 & U9 & U11).
    unfold APS.uE in U0, U6, U1, U2, U3, U4, U5, U7, U8, U9, U10, U11. cbn [edenot] in U0, U6, U1, U2, U3, U4, U5, U7, U8, U9, U10, U11.
    assert (PIN : forall n z, (n < 13)%nat -> bv_unsigned (ev E0a n) = z -> V n = z).
    { intros n z Hn Hz. rewrite (HVl n Hn). unfold uev. rewrite (Hev n) by (unfold NX0; lia). exact Hz. }
    pose proof (PIN 0%nat _ ltac:(lia) U0) as P0. pose proof (PIN 6%nat _ ltac:(lia) U6) as P6.
    pose proof (PIN 1%nat _ ltac:(lia) U1) as P1. pose proof (PIN 2%nat _ ltac:(lia) U2) as P2.
    pose proof (PIN 3%nat _ ltac:(lia) U3) as P3. pose proof (PIN 4%nat _ ltac:(lia) U4) as P4.
    pose proof (PIN 5%nat _ ltac:(lia) U5) as P5. pose proof (PIN 7%nat _ ltac:(lia) U7) as P7.
    pose proof (PIN 8%nat _ ltac:(lia) U8) as P8. pose proof (PIN 9%nat _ ltac:(lia) U9) as P9.
    pose proof (PIN 10%nat _ ltac:(lia) U10) as P10. pose proof (PIN 11%nat _ ltac:(lia) U11) as P11.
    clear U0 U6 U1 U2 U3 U4 U5 U7 U8 U9 U10 U11.
    assert (Hal : bv_unsigned sp mod 16 = 0) by (pose proof Hsp as (_ & _ & H); exact H).
    assert (LO : 0x7fff80000000 <= usp) by (pose proof Hsp as (H & _); exact H).
    assert (HI : usp + 192 <= 2 ^ 47) by (unshelve (eapply AsanInit.usp_hi; CL); CL).
    assert (PSP : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = bv_unsigned sp).
    { rewrite P0, P6, P10. fold usp. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (VR : forall n, 0 <= V n < 2 ^ 64) by (intros n; unfold V, Vf; apply uev_range).

    pose proof (co_top _ _ _ _ _ _ _ _ _ _ _ HC) as TOP. rewrite USP in TOP.
    assert (ATOP : atop mo = bv_unsigned sp - 8388608) by (unfold atop; rewrite TOP; reflexivity).
    eexists. split; cycle 1.
    {
      exists w, V, FULL. split; [reflexivity|].
      split; [exact VR|].
      split; [repeat split; assumption|].

      assert (HIDrom : forall a, APS.hid ASAN argH E hs mo a = true -> seg_rom asegs a = None).
      { intros a Ha. apply (APS.seg_rom_off_hull ASEGS ASAN asan_in_hull).
        unfold APS.hid in Ha. apply orb_prop in Ha as [Ha|Ha].
        - pose proof (AH E a Ha) as Hc. unfold APS.in_hull. cbn [img_lo img_hi ASAN]. unfold CEIL in Hc.
          apply andb_false_iff. right. apply Z.ltb_ge. lia.
        - apply negb_true_iff in Ha. unfold APS.vis in Ha. apply orb_false_iff in Ha as [Ha _]. apply orb_false_iff in Ha as [Ha _]. exact Ha. }
      assert (HULLvis : forall a, AIMG_LO <= bv_unsigned a < AIMG_HI -> APS.hid ASAN argH E hs mo a = false).
      { intros a Ha. apply (APS.hid_hull ASAN asan_hull_ok argH AH). unfold APS.in_hull. cbn [img_lo img_hi ASAN]. unfold AIMG_LO, AIMG_HI in Ha.
        apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
      pose proof (export_sound asegs E (APS.hid ASAN argH E hs mo) FULL (kn hs) AIMG_LO AIMG_HI
                    (co_know _ _ _ _ _ _ _ _ _ _ _ HC) HIDrom HULLvis _ _ MJ PJ) as [HMFs HPFs].
      pose proof (Forall_mfact_ok_msh FM asegs (uev E) FULL _ HMFs) as HMF. fold V in HMF.
      pose proof (Forall_pfact_ok_pfsh FM (uev E) _ HPFs) as HPF. fold V in HPF.
      pose proof HPF as HPFc.
      split; [exact HMF|]. split; [exact HPF|].

      split.
      { intros a b Hab. rewrite a_ro_addr.
        destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); [|reflexivity].
        destruct (Z.ltb_spec0 (bv_unsigned a) 0xcd000); [|reflexivity].
        exfalso. pose proof (mimg_cover asegs V FULL (amf RZ w) 0x10000 0xcd000 HMF IMGc (bv_unsigned a) ltac:(lia)) as X.
        unfold wa in X. rewrite Z_to_bv_bv_unsigned in X. congruence. }

      split.
      { pose proof (mwr_find asegs V FULL (amf RZ w) STKA 6144513 HMF STKc) as W.
        cbn [zv STKA] in W.
        replace (32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat) + -6144513) with (bv_unsigned sp - 6144513) in W by lia.
        cbn [en0 en_sp].
        apply wr_at_stk; [replace (bv_unsigned sp - (bv_unsigned sp - 6144513)) with 6144513 by lia; exact W|].
        intros a Ha. apply ref_find_segment_none; [lia|]. lia. }

      split.
      { intros a Ha. apply Hhid. unshelve (eapply argH0_of_range; first [exact Ha | CL]); CL. }

      pose proof (var_ranges_sound ASEGS E _ (kn hs) (co_know _ _ _ _ _ _ _ _ _ _ _ HC)) as HVR.
      destruct VJ as [VJa VJg].
      pose proof (vis_match_sound E _ _ _ HVR VJa) as HVISa0. pose proof (vis_match_sound E _ _ _ HVR VJg) as HVISg0.
      pose proof (Forall2_map_bnsh FM (uev E)
                    (fun p x y => bv_unsigned (edenot E (fst p)) = x /\ bv_unsigned (edenot E (snd p)) = y /\ 0 <= y) _ _ HVISa0) as HVISa.
      pose proof (Forall2_map_bnsh FM (uev E)
                    (fun p x y => bv_unsigned (edenot E (fst p)) = x /\ bv_unsigned (edenot E (snd p)) = y /\ 0 <= y) _ _ HVISg0) as HVISg.
      cbv beta in HVISa, HVISg. fold V in HVISa, HVISg.
      pose proof (ledger_den_lsh FM (uev E) _ _ (ledger_den_sound E _ HVR _ _ _ LJ (co_maps _ _ _ _ _ _ _ _ _ _ _ HC))) as HLD.
      pose proof (ledger_kinds_sound E _ HVR _ _ mo LJ (co_none _ _ _ _ _ _ _ _ _ _ _ HC) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC) (co_eagk _ _ _ _ _ _ _ _ _ _ _ HC)) as HKD0.
      assert (HKD : Forall (lentry_kind_ok V mo) asan_ledger).
      { rewrite Forall_map in HKD0. eapply Forall_impl; [|exact HKD0]. intros e He. exact (lentry_kind_ok_lsh FM (uev E) mo e He). }
      fold V in HLD.

      split.
      { pose proof (pvranges_sound V (apf RZ w) VR HPFc) as HVRp.
        assert (Elow : In (LMap (ZLit 0x7fff7000) 0x10000000 KRWLAZY) asan_ledger) by (cbn; tauto).
        assert (Ehigh : In (LMap (ZLit 0x2008fff7000) 0xdfff0001000 KRWLAZY) asan_ledger) by (cbn; tauto).
        intros a Hsh Hnv.
        assert (Ha : 0 <= a < 2 ^ 64) by (unfold ashadow in Hsh; lia).
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
        assert (HSS : exists s, In s ASHADOWS /\ fst s <= a < snd s).
        { destruct Hsh as [Hsh|Hsh]; [exists (0x7fff7000, 0x8fff7000) | exists (0x2008fff7000, 0x10007fff8000)]; cbn; split; auto; lia. }
        apply (co_zero _ _ _ _ _ _ _ _ _ _ _ HC (wa a)); rewrite ?Ua.
        -
          unfold APS.hid. apply orb_true_intro. right. apply negb_true_iff. unfold APS.vis. rewrite Ua.
          rewrite Klz. cbn [negb].
          replace (APS.in_hull ASAN a) with false.
          2:{ symmetry. unfold APS.in_hull. cbn [img_lo img_hi ASAN]. apply andb_false_iff. right. apply Z.ltb_ge. unfold ashadow in Hsh. lia. }
          replace (atop mo <=? a) with false by (symmetry; apply Z.leb_gt; rewrite ATOP; unfold ashadow in Hsh; lia).
          cbn [orb]. replace (APS.in_allow ASAN E hs a) with false; [destruct (APS.in_ivs _ _ && _)%bool; reflexivity|].
          symmetry. unfold APS.in_allow. apply orb_false_intro.
          +
            unfold APS.in_vis. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Xp).
            apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
            destruct (Forall2_In_l _ _ _ _ HVISa Hp) as (bn & Hbn & E1 & E2 & E3). unfold APS.uE in X1, X2. rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2.
            apply (shad_clear_sound V _ (apf RZ w) bn a HVRp HPFc (proj1 (forallb_forall _ _) CLRv bn Hbn) HSS). lia.
          +
            unfold APS.in_sh. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Xp).
            apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. unfold APS.sh_lo, APS.sh_hi, APS.uE in X1, X2.
            destruct (Forall2_In_l _ _ _ _ HVISa Hp) as (bn & Hbn & E1 & E2 & E3). rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2.
            apply Hnv. exists bn. split; [exact Hbn|]. change (shadow_off ASAN) with ASHOFF in X1, X2. lia.
        - exact Kmap.
        - apply Bool.not_true_iff_false. intros X. apply Kna. apply (proj1 (in_ivs_APS _ _)). exact X.
        - exact Klz.
        -
          unfold APS.in_ghost. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Xp).
          apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. unfold APS.uE in X1, X2.
          destruct (Forall2_In_l _ _ _ _ HVISg Hp) as (bn & Hbn & E1 & E2 & E3). rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2.
          apply (shad_clear_sound V _ (apf RZ w) bn a HVRp HPFc (proj1 (forallb_forall _ _) CLRg bn Hbn) HSS). lia. }

      pose proof (allowA_allow_of ASAN E _ _ (Forall2_app HVISa0 HVISg0)) as HAL. change (shadow_off ASAN) with ASHOFF in HAL.
      change (flat_map (allow1 ASAN E) (a_vis hs ++ a_ghost hs)) with (allowA ASAN E hs) in HAL.
      rewrite <- map_app, (allow_of_bnsh FM) in HAL. fold V in HAL. change (asan_vis_app ++ asan_ghost) with asan_vis in HAL.
      apply andb_prop in CONSTS as [CONSTS Ca]. apply andb_prop in CONSTS as [Ct Ce]. apply Z.leb_le in Ct, Ce, Ca.
      assert (USPW : vm_init_sp (m_vmmaps mo) = sp) by (apply bv_eq; exact TOP).
      destruct HC. cbn [inp0 AsanInit.inp in_fs en0 en_sp]. rewrite Hfd in co_fds0. rewrite Hbrk0 in co_brk0.
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
        unfold hull_clear in B5. cbn [img_lo img_hi ASAN] in B5. rewrite ATOP in B6. unfold AIMG_LO, AIMG_HI. repeat split; assumption.
      + eapply Forall_impl; [|exact co_lazyb0]. cbv beta. intros iv (B5 & B6).
        unfold hull_clear in B5. cbn [img_lo img_hi ASAN] in B5. rewrite ATOP in B6. unfold AIMG_LO, AIMG_HI. split; assumption.
      + destruct co_wf0 as (_ & Wn & _). apply Forall_forall. intros iv Hiv. exact (Wn iv Hiv).
      + intros z Hz. apply (proj1 (in_ivs_APS _ _)). apply co_nasub0. apply (proj2 (in_ivs_APS _ _)). exact Hz.
      + (* the state's bounds meet amodel's by conversion (sum_sizes / ivs_sum, eager_used / nonlazy_bytes,
           A_bytes / ivz_bytes are the same functions), which lia does not see *)
        apply (Z.le_trans _ (a_totsz hs)); [exact co_totsz0 | exact Ct].
      + apply (Z.le_trans _ (a_eager hs)); [exact co_eager0 | exact Ce].
      + rewrite <- HAL. apply (Z.le_trans _ (a_abytes hs)); [exact co_abytes0 | exact Ca].
      + rewrite <- HAL. pose proof (minv_budget _ _ co_minv0) as B. rewrite co_limit0 in B. exact B.
      + rewrite <- HAL. exact (APS.A_wf_allowA ASAN (HS_asan2 RZ) XN0 XE0 XB0 NX0 E hs).
      + exact (minv_nodup _ _ co_minv0).
      + intros p Hp. split; [exact (minv_aligned _ _ co_minv0 p Hp)|]. split; [exact (minv_lazy _ _ co_minv0 p Hp)|].
        rewrite <- HAL. apply page_allowedb_aallowed. exact (minv_allowed _ _ co_minv0 p Hp).
      +   intros z Hz. apply (proj1 (in_ivs_APS _ _)). apply co_lzsub0. apply (proj2 (in_ivs_APS _ _)). exact Hz.
      +   apply Forall_forall. intros [ea en] Hin. cbn [snd]. exact (co_nanz0 ea en Hin).
      +
        intros a Ha.
        assert (EF : In (LMap (ZMul (ZLit 4096) (ZV 377)) 11571200 KRWE) asan_ledger) by (unfold asan_ledger; cbn [In]; tauto).
        pose proof (proj1 (Forall_forall _ _) HKD _ EF) as K. cbn [lentry_kind_ok zv] in K.
        pose proof VB as VB'.
        apply existsb_exists in VB as (f & Hf & Hb). pose proof (proj1 (Forall_forall _ _) HPFc f Hf) as PF.
        destruct f as [n377 lo377 hi377| | |]; try discriminate Hb.
        apply andb_prop in Hb as [Hb Hb3]. apply andb_prop in Hb as [Hb1 Hb2]. apply Nat.eqb_eq in Hb1. subst n377.
        apply Z.leb_le in Hb2. apply Z.leb_le in Hb3. cbn [pfact_ok] in PF.
        assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha PF Hb2 Hb3; lia).
        destruct (K (Z_to_bv 64 a) ltac:(rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; clear - Ra; lia); clear - Ha Ra; lia)) as [_ K2].
        unfold page_base in K2. rewrite Z_to_bv_unsigned, bv_wrap_small in K2 by (unfold bv_modulus; clear - Ra; lia). exact K2.
      + exact co_rdr0.
      + exact co_mres0.
      + exact co_vtop0. }
    -
      unfold cfg_of. split; [|reflexivity]. cbn [cfg_ms].
      split; [| split; [apply regs_eqv_refl| repeat split; reflexivity]].
      cbn [ms_regs AS.PropExec.mkst MS].
      intros r Hr. destruct (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.RegsEquiv.reg_of_nat r) as (n & -> & Hn).
      pose proof (is_x0_of_nat n Hn Hr) as Hn1.
      rewrite (regs_ok_nth E _ R (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) n Hn1). rewrite reg_get_mkR by exact Hn1. rewrite Hregs.
      destruct n as [|n]; [cbv in Hr; discriminate|].
      cbn [en0 inp0 AsanInit.inp en_sp in_argv in_envp].
      do 31 (destruct n as [|n];
        [ cbn [nth AREGS];
          first [ reflexivity
                | apply Z_to_bv_bv_unsigned
                | symmetry; apply Z_to_bv_bv_unsigned
                | erewrite <- (zexp_of_sound E) by reflexivity; cbn [zv];
                  rewrite <- ?(HVl 0%nat ltac:(lia)), <- ?(HVl 1%nat ltac:(lia)), <- ?(HVl 6%nat ltac:(lia)), <- ?(HVl 10%nat ltac:(lia));
                  unfold AMAIN, ARA, AGP, ATP, usp, argc in *; f_equal; lia ]
        |]). lia.
  Qed.

  (* the two computed main-entry states, at the run's own CONFIG_RSEQ value; [main_justified] below
     proves the hypothesis by computation at both values *)
  Hypothesis HJ : forall w : bool, JUST RZ w (if w then HM1 RZ else HM2 RZ).
  Theorem amain_bridge_HM : forall (w : bool) E R FULL mo,
    cs_ok ASEGS ASAN LIM SINV argH fs E (if w then HM1 RZ else HM2 RZ) R FULL mo ->
    exists ms, cfg_eqv (cfg_of ASEGS R (pc (if w then HM1 RZ else HM2 RZ)) FULL mo) (mkCfg ms mo) /\ amain_at en0 inp0 ms mo.
  Proof.
    intros w E R FULL mo HC.
    exact (amain_bridge_w w _ (HJ w) E R FULL mo HC).
  Qed.

  Variable T : TSet.
  Hypothesis T_nil : T [].
  Hypothesis MAINA : forall ms mo, amain_at en0 inp0 ms mo -> srealizes asegs (mkCfg ms mo) T.

  Theorem asan_main_boot :
    srealizes asegs (init_config asegs Asan.M.init_pc a_phdrs sp brk0 mbase rdraw target_alloc_limit inp0) T.
  Proof.
    change asegs with ASEGS. change a_phdrs with APH. change target_alloc_limit with AsanInit.LIMIT. unfold inp0.
    (* the hole family is given explicitly, as before LPS 727298f3 (there positionally, [fun _ _ => T]): [?H E0a fs] against [T] is no pattern the
       unifier solves *)
    eapply (asan_boot sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm)
      with (H := fun (_ : env) (_ : Fs.Fs) => T); try eassumption.
    - intros; reflexivity.
    - intros; exact T_nil.
    - intros h ch Hh E R FULL mo HC.
      destruct (HS_asan2_two RZ h ch Hh) as [[-> ->]|[-> ->]].
      + destruct (amain_bridge_HM true E R FULL mo HC) as (ms & Heqv & Hat).
        apply (srealizes_eqv ASEGS (mkCfg ms mo) T (MAINA ms mo Hat)). apply cfg_eqv_sym. exact Heqv.
      + destruct (amain_bridge_HM false E R FULL mo HC) as (ms & Heqv & Hat).
        apply (srealizes_eqv ASEGS (mkCfg ms mo) T (MAINA ms mo Hat)). apply cfg_eqv_sym. exact Heqv.
  Qed.
End Bridge.

Lemma main_justified : forall r, 0 <= r <= 1 -> forall w : bool, JUST r w (if w then HM1 r else HM2 r).
Proof.
  intros r Hr w. assert (r = 0 \/ r = 1) as [-> | ->] by lia; destruct w; unfold JUST; vm_compute; repeat split; reflexivity.
Qed.

Theorem asan_side_ok : forall T : tfam,
  (forall en inp, valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
      T inp en [] /\ forall ms mo, amain_at en inp ms mo -> srealizes asegs (mkCfg ms mo) (T inp en)) ->
  side_ok asegs a_init_pc a_phdrs target_alloc_limit T.
Proof.
  intros T HT. apply side_ok_of_srealizes. intros [sp brk0 mbase rdraw] inp Hv Hi.
  (* LPS 727298f3 (run_segments, from 75d69e00): the start-up walk is over the image's own
     segments; [RomStable.srun_init] lifts it to the run's list (the image has no vDSO text) *)
  cbn [en_sp en_brk en_mmap_base en_draw]. apply RomStable.srun_init; [reflexivity|].
  destruct (HT _ _ Hv Hi) as [Tnil MAINA].
  pose proof Hi as (Hva & Hve & Hfs & _ & _ & [Huid Hgid] & Hnof & Hsigm & Hhw & Hvasz & _ & Hlaunch & Hrdr & _).
  apply (proj1 (valid_entry_sv48 _ _ _ Hvasz)) in Hv.
  destruct Hv as (Hsp & Hbrk & Hmb & Hfit & Hlau).
  destruct inp as [argv envp fs stdin uid gid groups net nof sigm hw abt vasz urnd tmpf kb execfn chrdr sigdef sigterm].
  cbn in Hfit, Hva, Hve, Hfs, Huid, Hgid, Hhw, Hvasz. subst vasz.
  (* the section's hypotheses asan_main_boot takes are those its proof uses: each one from the context, the
     main-entry states' justification by computation *)
  eapply (asan_main_boot sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm);
    first [exact (main_justified _ (rseq_z_range (kb_rseq kb))) | eassumption].
Qed.
