(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the initial state takes the launch input (the kernel build at the recorded kernel's eight fields, pinned_kernel, exec file name, gid, groups, network queue, file limits and SIGPIPE disposition), lays out the stack block and an auxv of 27 or 29 pairs by the launch's CONFIG_RSEQ flag, with the vDSO base, AT_MINSIGSTKSZ and the gid as variables (V_VDSO, V_MSS, V_GID), and checks under a table whose CONFIG_RSEQ layout is the launch's (Hrs), with auxv lemmas after projects/jsoncons/fuzz_bigint/proofs/lib/AsanInitK.v of this tree (auxv_words_null and auxv_null_ok taken from its lines 63-68 and 1165-1171, auxv_unk_ok and auxv_rseq_ok taken from its lines 1186-1230 with their proofs reworked); launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec CatExec CatSim SeqExec StoreOk StreamSim StepTac ShapeAlg AgentLib StartupAux RefLayout ArgvEnv
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan AsanPlanSound.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanCeil.  (* [comment removed for export] *)
From Stdlib Require Import Zify.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac el_lia_core := first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                                | Zify.zify; xlia zchecker ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.  (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition LIMIT : Z := target_alloc_limit.

(* [comment removed for export] *)
Record img_facts (segs : list Segment) (A : atable) (ph : PhdrInfo) : Prop := IMG_FACTS {
  if_ph    : ph_addr_z A = Z.of_N (ph_addr ph) /\ ph_ent_z A = Z.of_N (ph_ent ph) /\ ph_num_z A = Z.of_N (ph_num ph);
  if_hull  : 0 <= img_lo A <= img_hi A /\ img_hi A <= 2 ^ 32 /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0;
  if_top   : reserved_top (segments_reserved segs) = img_hi A;
  if_res   : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                    (segments_reserved segs);
  if_sizes : sum_sizes (segments_reserved segs) = img_hi A - img_lo A;
  if_rw    : (0 <= rw_lo A /\ 0 <= rw_len A /\ rw_lo A + rw_len A < 2 ^ 64)
             /\ forall m (x : word), rw_lo A <= bv_unsigned x < rw_lo A + rw_len A -> wview segs m x <> None;
  if_shadow : 0 <= shadow_off A <= 2 ^ 47;
  (* [comment removed for export] *)
  if_resx  : (2 <= n_resx A)%nat /\ (20 <= p_resx A)%nat
}.

(* [comment removed for export] *)
Definition stack_image_size (sp top : word) : Z :=
  (bv_unsigned top - bv_unsigned sp)%Z.

(* [comment removed for export] *)
Lemma NX0_sp0 : nx0_sp_ok NX0.
Proof. unfold nx0_sp_ok, NX0. lia. Qed.

(** [e_G] is the parity of argc + envc + 3, that is of [StackLayout.block_items argv envp]
    ([c0dd863a:theories/LinuxProcessSem/StackLayout.v:388]), whenever the sum does not wrap. *)
Lemma uE_e_G : forall E, uE E (EVar V_ARGC) + uE E (EVar V_ENVC) + 3 < 2 ^ 64 ->
  uE E e_G = (uE E (EVar V_ARGC) + uE E (EVar V_ENVC) + 3) mod 2.
Proof.
  intros E H. unfold uE in *. unfold e_G. cbn [edenot]. rewrite u_and64.
  assert (L : forall x, 0 <= x -> Z.land x 1 = x mod 2).
  { intros x Hx. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. }
  pose proof (u64_range (edenot E (EVar V_ARGC))). pose proof (u64_range (edenot E (EVar V_ENVC))).
  unfold eaddz, eadd. rewrite !mkAlu_denot, !edenot_lit. rewrite !u_add64, !u64_lit by lia.
  rewrite (Z.mod_small (bv_unsigned (edenot E (EVar V_ARGC)) + bv_unsigned (edenot E (EVar V_ENVC)))) by lia.
  rewrite (Z.mod_small (_ + 3) (2 ^ 64)) by lia.
  (* [cbn [edenot]] above may have reduced the variables to [ev]: give lia both spellings *)
  pose proof (u64_range (ev E V_ARGC)). pose proof (u64_range (ev E V_ENVC)).
  apply L. cbn [edenot]. lia.
Qed.

(** The hwcap start state: [init_acs_of] with the AT_HWCAP auxv pair known and the hwcap held in
    the first fresh variable [V_HW] (= [NX0]); its stack windows reach the argument block. *)
Definition V_HW : nat := 9.
(** The three auxv a_val slots.  Thirteen of the vector's values are closed and live in
    [init_kn_with] as literals; these four rows are the ones whose value is a FREE Section
    variable, so a literal cannot hold them and each needs a slot, exactly as AT_HWCAP does:
      [V_VDSO]  pair 0, AT_SYSINFO_EHDR = [Run.vdso_text_base (in_kernel inp) sp mbase]
                      = [vdso_pair_top sp mbase - vdso_text_pages (in_kernel inp) * page_size]
                        ([c0dd863a:theories/LinuxProcessSem/Run.v:301-312]).  [sp] and [mbase]
                        are free.  The term is carried SYMBOLICALLY: [vdso_text_pages (in_kernel
                        inp)] is never replaced by a numeral.  It is not opaque -- [pinned_vdso_text_pages] (:223)
                        reduces it to [vdso_text_pages default_kernel] from [Hkernel], one
                        definition on -- but the plan has no business naming a kernel constant.
      [V_MSS]   pair 9, AT_MINSIGSTKSZ = [min_sigframe_size] of the free hwcap ([c0dd863a:theories/LinuxProcessSem/State.v:4074])
      [V_GID]   pairs 21 and 22, AT_GID and AT_EGID, both the free [gid].  [vals0] binds [uid]
                        at [V_UID] and nothing for [gid], so pairs 21 and 22 need the [V_GID] slot;
                        a key-only pair would halt one instruction later, not pass.
    The slots sit AFTER [V_HW] and below [NX_HW] (= 13), so none of them shares an index with
    [V_S1]..[V_HW]. *)
Definition V_VDSO : nat := 10.
Definition V_MSS : nat := 11.
Definition V_GID : nat := 12.
Definition NX_HW : nat := 13.

Definition STK_HW_TOP : Z := 2 ^ 47 + 8388608.
Definition STK_HW_HI : Z := 0x80801000.
Definition e_stklen : expr := esub (ELit STK_HW_TOP) e_pd.
Definition STK_HW_HI0 : Z := 0x80800000.
Definition e_stklen0 : expr := esub (ELit STK_HW_TOP) e_sp0.

Definition init_vis_hw (A : atable) : list (expr * expr) :=
  [(ELit (img_lo A), ELit (img_hi A - img_lo A)); (eaddz e_pd STK_OFF, e_stklen); (eaddz e_sp0 STK_OFF, e_stklen0)].

(** AT_HWCAP is the eleventh auxv pair (index 10) of the 08b1429 layout *)
(** The four a_val rows whose value is a free Section variable; [init_kn_hw] puts them after
    [init_kn].  A plan term must be CLOSED -- a certificate [vm_compute]s over it --
    so these carry a SLOT and the symbolic term is supplied by the valuation [E0hw], which is
    the same division of labour AT_HWCAP already uses: [EVar V_HW] in the plan, [hw] in the
    environment, tied by [kword_reenv] in [init_kn_hw_ok].  Pairs 21 and 22 share [V_GID]
    because the model gives AT_GID and AT_EGID the same word ([c0dd863a:theories/LinuxProcessSem/StackLayout.v:256-257]). *)
Definition auxv_vals_free : list kentry :=
  [ KWord (SA (fst e_auxb) (snd e_auxb + 16 *  0 + 8)) 8 (EVar V_VDSO);   (* AT_SYSINFO_EHDR *)
    KWord (SA (fst e_auxb) (snd e_auxb + 16 *  9 + 8)) 8 (EVar V_MSS);    (* AT_MINSIGSTKSZ *)
    KWord (SA (fst e_auxb) (snd e_auxb + 16 * 21 + 8)) 8 (EVar V_GID);    (* AT_GID *)
    KWord (SA (fst e_auxb) (snd e_auxb + 16 * 22 + 8)) 8 (EVar V_GID) ].  (* AT_EGID *)

(** The rest of the vector, at parity with fuzz_bigint's [AsanPlanCoreK.auxv_rest] and bzip2's
    [K/AS/AsanPlanCore.v] [init_kn_with]: AT_EXECFN's type word (pair
    25), the CONFIG_RSEQ pair (26, 27) when [a_rseq A] = 1, and the whole vector readable
    ([KUnk]), so the value no plan variable denotes (AT_EXECFN's) is read as unknown.  musl's
    [__init_libc] reads every pair's type up to AT_NULL and the value of each type below
    AUX_CNT; without these the walk stops at pair 25, short of [x_pnscan], and [PX XPnScan]
    refuses.  [init_kn_hw] puts these rows LAST. *)
Definition auxv_rest (A : atable) : list kentry :=
  KWord (SA (fst e_auxb) (snd e_auxb + 16 * 25)) 8 (ELit 31)                    (* AT_EXECFN's type *)
  :: (if Z.eqb (a_rseq A) 1 then auxw 26 27 (ELit 28) ++ auxw 27 28 (ELit 32) else [])
  ++ [KUnk (SA (fst e_auxb) (snd e_auxb)) (ELit (AUXSZ (a_rseq A)))].

Definition init_kn_hw (A : atable) : list kentry :=
  auxw 10 16 (EVar V_HW) ++ init_kn A ++ auxv_vals_free ++ auxv_rest A.

Definition init_acs_hw (A : atable) : acs :=
  ACS (mk_ss (a_entry A) init_regs (init_kn_hw A) NX_HW) []
      (img_hi A - img_lo A + resx_bytes A) (MBASE_MIN - resx_bytes A) 0 (init_vis_hw A) []
      (vis_cost (img_hi A - img_lo A) + vis_cost STK_HW_HI + vis_cost STK_HW_HI0) (escale 4096 (EVar V_BRK)) FdStd false.

(** The layout terms fold [a_rseq A] into literals, so the check computes only at a literal
    layout: the lemma takes the layout's range. *)
Lemma kn_vars_lt_init_kn : forall A, a_rseq A = 0 \/ a_rseq A = 1 -> AP.kn_vars_lt NX0 (init_kn A) = true.
Proof.
  (* unfolded outside-in, so no layout term is left folded over [a_rseq A] *)
  intros A HA. unfold init_kn, init_kn_with, atr_entry, e_atrb, e_argv1w, e_str1, e_str0, e_atrandom.
  destruct HA as [HA|HA]; rewrite HA; vm_compute; reflexivity.
Qed.

Lemma auxv_rest_vars : forall A, AP.kn_vars_lt NX0 (auxv_rest A) = true.
Proof. intros A. unfold auxv_rest. destruct (Z.eqb (a_rseq A) 1); vm_compute; reflexivity. Qed.

(** The layout's flag is 0 or 1 ([rseq_z] of the launch's bit); the check computes the layout
    terms only at a literal flag, so a consumer over a symbolic table splits on the flag here. *)
Lemma rseq_z_01 : forall b, rseq_z b = 0 \/ rseq_z b = 1.
Proof. intros [|]; [right|left]; reflexivity. Qed.

Lemma sr_vars_lt_init_regs : AP.sr_vars_lt NX0 init_regs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma kword_reenv : forall segs E E' M b k w v v',
  edenot E b = edenot E' b -> edenot E v = edenot E' v' ->
  kentry_ok segs E M (KWord (SA b k) w v) -> kentry_ok segs E' M (KWord (SA b k) w v').
Proof.
  intros segs E E' M b k w v v' Hb Hv H. cbn [kentry_ok] in *.
  unfold flat, estart, adenot in *. cbn [a_base a_off] in *. rewrite <- Hb, <- Hv. exact H.
Qed.

Lemma auxw_reenv : forall segs E E' M i ty v v',
  env_agree NX0 E E' -> edenot E v = edenot E' v' ->
  know_ok segs E M (auxw i ty v) -> know_ok segs E' M (auxw i ty v').
Proof.
  intros segs E E' M i ty v v' Hag Hv HK. unfold auxw, know_ok in *.
  pose proof (Forall_inv HK) as HK1. pose proof (Forall_inv (Forall_inv_tail HK)) as HK3.
  assert (Hb : AP.expr_vars_lt NX0 (fst e_auxb) = true) by (vm_compute; reflexivity).
  pose proof (edenot_agree' NX0 E E' _ Hag Hb) as Eb.
  constructor; [|constructor; [|constructor]].
  - exact (kword_reenv segs E E' M _ _ 8 (ELit ty) (ELit ty) Eb eq_refl HK1).
  - exact (kword_reenv segs E E' M _ _ 8 v v' Eb Hv HK3).
Qed.

(** THE KERNEL SHAPE THE ASAN START-UP IS PROVED FOR.

    [Run.valid_input]'s last conjunct is [in_kernel inp = recorded_kernel (in_kernel inp)], which
    fixes the eight fields [State.recorded_kernel] copies from [default_kernel] -- the vDSO
    image, vlenb, the cache view, the skb head and the four socket sysctls -- and leaves
    [kb_thp], [kb_aslr], [kb_guard], [kb_rnd_bits] and [kb_rseq] FREE.  This start-up assumes
    exactly [recorded_kernel]'s eight fields: CONFIG_RSEQ is free too, and the plan and its
    certificates are checked at both layouts, the atable's [a_rseq] tied to the launch's bit by
    [Hrs] below.  [pinned_of_recorded] is how a consumer builds it from [valid_input]. *)
Definition pinned_kernel (kb : KernelBuild) : KernelBuild :=
  mkKernelBuild (kb_thp kb) (kb_vdso default_kernel) (kb_aslr kb)
                (kb_guard kb) (kb_rnd_bits kb) (kb_rseq kb)
                (kb_vlenb default_kernel) (kb_cache default_kernel)
                (kb_skb_head default_kernel) (kb_wmem_default default_kernel)
                (kb_rmem_default default_kernel) (kb_wmem_max default_kernel)
                (kb_rmem_max default_kernel).

Lemma pinned_of_recorded : forall kb, kb = recorded_kernel kb -> kb = pinned_kernel kb.
Proof. intros kb H. unfold pinned_kernel. exact H. Qed.

(* The AT_RANDOM block's literal offset off [e_auxb]'s base: the pointer vector's NULLs and argc
   (24) plus the auxv itself, under both layouts -- 456 without CONFIG_RSEQ, 488 with it (fuzz_bigint's
   [AsanInitK.e_atrb_off]). *)
Lemma e_atrb_off : forall A, a_rseq A = 0 \/ a_rseq A = 1 -> snd (e_atrb A) = 24 + AUXSZ (a_rseq A).
Proof. intros A [H|H]; unfold e_atrb, e_atrandom; rewrite H; vm_compute; reflexivity. Qed.

(* AT_NULL closes the vector: pair 28 with CONFIG_RSEQ, pair 26 without ([StackLayout.auxv_entries]), so its
   two words are [2 * (26 + 2 * r)] and one more, at the flag's [r = rseq_z (la_rseq la)] (this sentence is the first of the comment on
   lines 57-62, and the lemma below is copied from lines 63-68, of projects/jsoncons/fuzz_bigint/proofs/lib/AsanInitK.v of this tree). *)
Lemma auxv_words_null : forall la ph entry uid gid hw ar ae,
  nth (Z.to_nat (2 * (26 + 2 * rseq_z (la_rseq la))))
      (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0
  /\ nth (Z.to_nat (2 * (26 + 2 * rseq_z (la_rseq la)) + 1))
         (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. intros [ehdr c msz [|]] ph entry uid gid hw ar ae; split; reflexivity. Qed.

Lemma pinned_vdso_len : forall kb, kb = pinned_kernel kb -> vdso_len kb = vdso_len default_kernel.
Proof. intros kb H. exact (f_equal vdso_len H). Qed.

Lemma pinned_vdso_text_pages : forall kb,
  kb = pinned_kernel kb -> vdso_text_pages kb = vdso_text_pages default_kernel.
Proof. intros kb H. exact (f_equal vdso_text_pages H). Qed.

Section Init.
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  (* [comment removed for export] *)
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  (* [comment removed for export] *)
  Variable uid gid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.
  (* [comment removed for export] *)
  Variable nofile sigmask : word.
  Variable urnd : InputStream.
  (** the kernel build and the exec file name come from the input *)
  Variable kern : KernelBuild.
  Variable execfn : list byte.
  (** LPS 727298f3: the launch's SIGPIPE disposition at entry ([State.in_sigpipe_default]).
      [Run.valid_input] leaves it free (both dispositions are Linux launches), so the Section
      takes it as given and [init_config_inp] supplies the input's own value.  It is implicit,
      as in coturn's [Asan/AsanInit.v]: a caller names it where nothing else fixes it. *)
  Context {sigpipe_default : bool}.

  Hypothesis IMG : img_facts segs A ph.
  Hypothesis Hapc : Z.of_N apc = a_entry A.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  (* [comment removed for export] *)
  Hypothesis Huid : valid_id uid.
  (* [comment removed for export] *)
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).
  (* [comment removed for export] *)
  Definition inp : ProcInput :=
    mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd []
      kern execfn true sigpipe_default false.

  (** The kernel shape this start-up is proved for: [recorded_kernel]'s eight fields, which
      [Run.valid_input]'s last conjunct hands a consumer, and no more.  [kb_thp], [kb_aslr],
      [kb_guard], [kb_rnd_bits] and [kb_rseq] are FREE; see [pinned_kernel] above, and [Hrs]
      below for the CONFIG_RSEQ layout. *)
  Hypothesis Hkernel : in_kernel inp = pinned_kernel (in_kernel inp).

  (* [comment removed for export] *)
  Hypothesis Hlaunch : valid_launch inp.
  (* [comment removed for export] *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.

  (* [comment removed for export] *)
  Let rseq : bool := kb_rseq kern.
  Let entryw : word := Z_to_bv 64 (Z.of_N apc).
  Let la : LaunchAuxv := launch_auxv inp sp mbase.
  Let top : word := ed_top rdraw.
  (** the launch's CONFIG_RSEQ flag as 0 or 1, and the atable the plan is checked under reads the
      same layout (coturn's [Asan/AsanInit.v] [Hrs]); the launch proves it by [eq_refl], at
      [A := INFO_ASAN_at (rseq_z (kb_rseq (in_kernel inp)))]. *)
  Let RZ : Z := rseq_z rseq.
  Hypothesis Hrs : a_rseq A = RZ.

  Lemma RZ_range : 0 <= RZ <= 1.
  Proof. exact (rseq_z_range rseq). Qed.

  Lemma a_rseq_01 : a_rseq A = 0 \/ a_rseq A = 1.
  Proof. rewrite Hrs. unfold RZ, rseq, rseq_z. destruct (kb_rseq kern); auto. Qed.

  (* the vector's length, the one case split on the flag the arithmetic needs (fuzz_bigint's
     [AsanInitK.auxv_count_RZ]) *)
  Lemma auxv_count_RZ : Z.of_nat (auxv_count rseq) = 27 + 2 * RZ.
  Proof. unfold RZ, rseq, rseq_z, auxv_count. destruct (kb_rseq kern); reflexivity. Qed.

  Lemma inp_argv : in_argv inp = argv.        Proof. reflexivity. Qed.
  Lemma inp_envp : in_envp inp = envp.        Proof. reflexivity. Qed.
  Lemma inp_kernel : in_kernel inp = kern. Proof. reflexivity. Qed.
  Lemma kern_pinned : kern = pinned_kernel kern. Proof. exact Hkernel. Qed.
  Lemma inp_execfn : in_execfn inp = execfn.  Proof. reflexivity. Qed.
  Lemma inp_rseq : kb_rseq (in_kernel inp) = rseq. Proof. reflexivity. Qed.
  (** The eight AT_L*_CACHE* values are CLOSED, and this is why.  [Run.launch_cache_words]
      reads [kb_cache] and nothing else ([c0dd863a:theories/LinuxProcessSem/Run.v:1367-1374]), and [pinned_kernel] pins
      [kb_cache] to [default_kernel]'s, so the whole cache half of the vector is determined by
      [Hkernel] alone -- no free field of the kernel build reaches it, and in particular the
      free [kb_thp], [kb_aslr], [kb_guard], [kb_rnd_bits] and [kb_rseq] do not. *)
  Lemma la_cache_pinned : la_cache la = launch_cache_words default_kernel.
  Proof.
    (* [rewrite inp_kernel] first: [la] is [launch_auxv inp sp mbase], so [launch_cache_words] is
       applied to [in_kernel inp], not to [kern].  The two are equal by [inp_kernel] but not
       syntactically, and [rewrite] matches syntactically, so without it the goal holds
       [kb_cache (in_kernel inp)] where the rewrite looks for [kb_cache kern].  [cbn] does not
       bridge it, since [in_kernel] is not in its delta list, and widening that list would
       reduce [inp]'s other projections too. *)
    unfold la. cbn [launch_auxv la_cache]. rewrite inp_kernel.
    unfold launch_cache_words. rewrite (f_equal kb_cache kern_pinned). reflexivity.
  Qed.

  Let bsb := entry_stack_image inp mbase ph entryw sp rdraw.   (* [comment removed for export] *)
  Let usp := bv_unsigned sp.

  Let utop := bv_unsigned top.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let L0 := Z.of_nat (length (nth 0 argv [])).
  Let L1 := Z.of_nat (length (nth 1 argv [])).
  (* [comment removed for export] *)
  Let G := Z.of_nat (block_items argv envp mod 2).
  (* [comment removed for export] *)
  Let CHEAD := Z.of_nat (block_head_size rseq argv envp).
  (* [comment removed for export] *)
  Let LSTR := Z.of_nat (launch_string_bytes argv envp execfn).
  (* [comment removed for export] *)
  Let W := Z.of_nat (block_pad_len rseq sp top argv envp execfn).
  (* [comment removed for export] *)
  Let STR0 := usp + CHEAD + W.

  Definition vals0 : list word :=
    [Z_to_bv 64 (usp / 32768); Z_to_bv 64 argc; Z_to_bv 64 envc; Z_to_bv 64 L0; Z_to_bv 64 W;
     Z_to_bv 64 (bv_unsigned brk0 / 4096); Z_to_bv 64 ((usp mod 32768) / 16); Z_to_bv 64 L1; uid].
  (* [comment removed for export] *)
  Definition E0 : env := Env (fun n => nth n vals0 (Z_to_bv 64 0))
                             (fun k => if Nat.eqb k K_RND then at_random_bytes (ed_random rdraw) else []).

  (* [comment removed for export] *)
  Definition argH0 (E : env) (a : word) : bool :=
    let z := bv_unsigned a in
    (((usp + 8 * argc + 16 <=? z) && (z <? usp + 8 * argc + 8 * envc + 24))
     || ((STR0 <=? z) && (z <? utop)))%bool.

  Definition SINV0 (E : env) (M : word -> option byte) : Prop :=
    (forall n, (n < NX0)%nat -> ev E n = ev E0 n)
    /\ (forall a, argH0 E a = true -> M a = wrap_mem inp mbase ph entryw sp rdraw a).

  (* [comment removed for export] *)
  Lemma argH0_high : forall E a, argH0 E a = true -> CEIL <= bv_unsigned a.
  Proof.
    intros E a H. unfold argH0 in H. destruct Hsp as [Hlo _]. unfold sp_window_lo in Hlo. unfold CEIL.
    pose proof (valid_argv_len argv Hva).
    assert (HC : 0 <= CHEAD) by (unfold CHEAD; lia).
    assert (HW : 0 <= W) by (unfold W; lia).
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H _]; apply Z.leb_le in H;
      unfold usp, argc, envc, STR0 in H; lia.
  Qed.

  Lemma argH0_agree : forall E E' a, env_agree NX0 E E' -> argH0 E a = argH0 E' a.
  Proof. reflexivity. Qed.

  Lemma SINV0_frame : forall E M M', (forall a, argH0 E a = true -> M' a = M a) -> SINV0 E M -> SINV0 E M'.
  Proof. intros E M M' Hf [H1 H2]. split; [exact H1|]. intros a Ha. rewrite (Hf a Ha). apply H2. exact Ha. Qed.

  Lemma SINV0_agree : forall E E' M, env_agree NX0 E E' -> SINV0 E M -> SINV0 E' M.
  Proof.
    intros E E' M [Hag _] [H1 H2]. split; [|exact H2]. intros n Hn. rewrite <- (Hag n) by (unfold NX0 in *; lia). apply H1. exact Hn.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma Hhi' : (bv_unsigned sp <= sp_window_hi)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hal' : (bv_unsigned sp mod 16 = 0)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hav0 : (0 < length argv)%nat. Proof. destruct Hva as [[? ?] _]; lia. Qed.

  Lemma len_av : 1 <= argc <= 1024.
  Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  Lemma len_ev : 0 <= envc <= 256.
  Proof. unfold envc. destruct Hve as [H _]. lia. Qed.
  Lemma usp_lo : 0x7fff80000000 <= usp.
  Proof. unfold usp. destruct Hsp as [H _]. exact H. Qed.
  Lemma usp_al : usp mod 16 = 0.
  Proof. unfold usp. destruct Hsp as (_ & _ & H). exact H. Qed.

  Lemma gap_range : 0 <= G <= 1.
  Proof. unfold G. pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia. Qed.

  (* [comment removed for export] *)
  (* C = 8*items + AUXSZ RZ + 8*g + 16, with items = argc + envc + 3 and the auxv
     AUXSZ RZ = 432 + 32*RZ bytes: 29 pairs with CONFIG_RSEQ, 27 without (fuzz_bigint's
     [AsanInitK.chead_eq]) *)
  Lemma chead_eq : CHEAD = 8 * argc + 8 * envc + 472 + 32 * RZ + 8 * G.
  Proof.
    pose proof (AUXSZ_of rseq) as HA. unfold AUXSZ in HA. change (rseq_z rseq) with RZ in HA.
    unfold CHEAD, G, argc, envc, block_head_size, block_items.
    lia.
  Qed.

  Lemma chead_range : 480 <= CHEAD <= 10752.
  Proof.
    pose proof chead_eq. pose proof len_av. pose proof len_ev. pose proof gap_range. pose proof RZ_range. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma s0_in_strings2 : L0 + 2 <= LSTR.
  Proof.
    unfold LSTR, launch_string_bytes, L0.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
    pose proof (Nat2Z.is_nonneg (length execfn)).
    pose proof Hav0 as Hnz.
    destruct argv as [|a t] eqn:Ea; [cbn in Hnz; lia|].
    cbn [flatten_strings flat_map nth]. rewrite !length_app. cbn [length]. lia.
  Qed.

  Lemma lstr_lo : 2 <= LSTR.
  Proof. pose proof s0_in_strings2. unfold L0 in *. lia. Qed.

  (* [comment removed for export] *)
  Lemma s0_in_strings : L0 + 1 <= LSTR.
  Proof. pose proof s0_in_strings2. lia. Qed.

  (* [comment removed for export] *)
  Lemma lstr_hi : LSTR + 8 * argc + 8 * envc <= 2097152.
  Proof.
    destruct Hlaunch as [_ Hb]. unfold launch_bytes, e2big_limit in Hb.
    rewrite inp_argv, inp_envp, inp_execfn in Hb. unfold LSTR, argc, envc. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pad_bounds_Z : 0 <= utop - 8 - LSTR - usp - CHEAD <= 4110.
  Proof.
    destruct Hlau as (_ & Hsw & _). destruct Hsw as (_ & Hslo & Hshi).
    unfold launch_sp_lo, launch_sp_hi, align_down16 in Hslo, Hshi.
    rewrite inp_argv, inp_envp, inp_execfn, inp_rseq in Hslo, Hshi.
    change (ed_top rdraw) with top in Hslo, Hshi.
    fold LSTR in Hslo, Hshi. fold CHEAD in Hslo, Hshi. fold utop usp in Hslo, Hshi.
    pose proof (Z.mod_pos_bound (utop - 8 - LSTR) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound (utop - 8 - LSTR - 4095) 16 ltac:(lia)).
    lia.
  Qed.

  Lemma pad_eq : W = utop - 8 - LSTR - usp - CHEAD.
  Proof.
    pose proof pad_bounds_Z.
    unfold W, block_pad_len, LSTR, CHEAD, utop, usp in *.
    rewrite Z2Nat.id by lia. reflexivity.
  Qed.

  Lemma pad_range : 0 <= W <= 4110.
  Proof. pose proof pad_bounds_Z. pose proof pad_eq. lia. Qed.

  (* [comment removed for export] *)
  Lemma length_bsb_eq : Z.of_nat (length bsb) = stack_image_size sp top.
  Proof.
    unfold bsb, stack_image_size.
    exact (length_entry_stack_image_launch Sv48 inp mbase ph entryw sp brk0 rdraw Hlau).
  Qed.

  Lemma length_bsb_sum : Z.of_nat (length bsb) = CHEAD + W + LSTR + 8.
  Proof.
    pose proof pad_eq. rewrite length_bsb_eq. unfold stack_image_size. fold utop usp. lia.
  Qed.

  Lemma bsb_nw : usp + Z.of_nat (length bsb) < 2 ^ 64.
  Proof.
    unfold usp, bsb.
    exact (entry_stack_image_no_wrap Sv48 inp mbase ph entryw sp brk0 rdraw Hlau).
  Qed.

  Lemma usp_fit : usp + Z.of_nat (length bsb) <= 2 ^ 47.
  Proof.
    rewrite length_bsb_eq. unfold stack_image_size. fold utop usp.
    pose proof (entry_page_top_within_window Sv48 inp mbase sp brk0 rdraw Hlau) as H.
    unfold entry_page_top, va_stack_top, sp_window_hi in H. fold top utop in H. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bsb_ge : 8 * argc + 8 * envc + 482 <= Z.of_nat (length bsb).
  Proof.
    pose proof length_bsb_sum. pose proof chead_eq. pose proof RZ_range. pose proof lstr_lo. pose proof pad_range.
    pose proof gap_range. pose proof RZ_range. lia.
  Qed.

  Lemma str0_hi : STR0 + LSTR + 8 = utop.
  Proof. unfold STR0. pose proof pad_eq. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma brk_range : img_hi A <= bv_unsigned brk0 <= img_hi A + BRK_ASLR /\ bv_unsigned brk0 mod 4096 = 0.
  Proof.
    destruct Hbrk as (H1 & H2 & H3). unfold brk_aslr_max in H2. unfold page_size in H3.
    rewrite (if_top _ _ _ IMG) in H1, H2. unfold BRK_ASLR. lia.
  Qed.

  Lemma usp_hi : usp + 192 <= 2 ^ 47.
  Proof. pose proof usp_fit. pose proof bsb_ge. pose proof len_av. pose proof len_ev. lia. Qed.

  (* [comment removed for export] *)
  Lemma uE0 :
    uE E0 (EVar V_S1) = usp / 32768 /\ uE E0 (EVar V_S2) = (usp mod 32768) / 16
    /\ uE E0 (EVar V_ARGC) = argc /\ uE E0 (EVar V_ENVC) = envc /\ uE E0 (EVar V_L0) = L0
    /\ uE E0 (EVar V_W) = W /\ uE E0 (EVar V_BRK) = bv_unsigned brk0 / 4096
    /\ uE E0 e_G = G.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof gap_range.
    pose proof (u64_range brk0) as [B1 B2].
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva ltac:(destruct Hva as [Hl _]; lia)). lia. }
    assert (Hu7 : uE E0 (EVar V_S1) = usp / 32768 /\ uE E0 (EVar V_S2) = (usp mod 32768) / 16
      /\ uE E0 (EVar V_ARGC) = argc /\ uE E0 (EVar V_ENVC) = envc /\ uE E0 (EVar V_L0) = L0
      /\ uE E0 (EVar V_W) = W /\ uE E0 (EVar V_BRK) = bv_unsigned brk0 / 4096).
    { unfold uE. cbn [edenot E0 ev nth vals0 V_S1 V_S2 V_ARGC V_ENVC V_L0 V_W V_BRK].
      rewrite !u64_lit by lia. repeat split; reflexivity. }
    destruct Hu7 as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
    split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
    rewrite uE_e_G by (rewrite A3, A4; lia). rewrite A3, A4.
    unfold G, argc, envc, block_items. rewrite Nat2Z.inj_mod, !Nat2Z.inj_add. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma uE0_envc : uE E0 (EVar V_ENVC) = envc.
  Proof. destruct uE0 as (_ & _ & _ & H & _). exact H. Qed.

  Lemma L1_range : 0 <= L1 <= 131071.
  Proof.
    unfold L1. destruct (Nat.lt_ge_cases 1 (length argv)) as [Hl|Hl].
    - pose proof (valid_argv_str_len argv 1 Hva Hl). lia.
    - rewrite nth_overflow by lia. cbn. lia.
  Qed.

  Lemma uE0_L1 : uE E0 (EVar V_L1) = L1.
  Proof. pose proof L1_range. unfold uE. cbn [edenot E0 ev nth vals0 V_L1]. rewrite u64_lit by lia. reflexivity. Qed.

  Lemma edenot_uid : uid = edenot E0 (EVar V_UID).
  Proof. reflexivity. Qed.

  Lemma uE0_uid : uE E0 (EVar V_UID) = bv_unsigned uid.
  Proof. reflexivity. Qed.

  Lemma u_e_sp0 : uE E0 e_sp0 = usp.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _).
    unfold e_sp0, eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma edenot_e_sp0 : edenot E0 e_sp0 = sp.
  Proof. apply bv_eq. exact u_e_sp0. Qed.

  (* [comment removed for export] *)
  Lemma e_sp0_of_SINV0 : forall E M, SINV0 E M -> edenot E e_sp0 = edenot E0 e_sp0.
  Proof.
    intros E M [H _]. unfold e_sp0, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot. cbn [edenot].
    unfold NX0, V_S1, V_S2 in H |- *. rewrite (H 0%nat) by lia. rewrite (H 6%nat) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma argH0_sp : forall E M (a : word), SINV0 E M -> argH0 E a = true -> uE E e_sp0 <= bv_unsigned a.
  Proof.
    intros E M a HS Ha. unfold uE. rewrite (e_sp0_of_SINV0 E M HS), edenot_e_sp0. fold usp.
    pose proof len_av. pose proof len_ev.
    assert (0 <= CHEAD) by (unfold CHEAD; lia). assert (0 <= W) by (unfold W; lia). unfold STR0 in *.
    unfold argH0 in Ha. apply orb_prop in Ha as [Q|Q]; apply andb_prop in Q as [Q _]; apply Z.leb_le in Q; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma u_stk0 : uE E0 (eaddz e_sp0 STK_OFF) = usp - 8388608.
  Proof.
    pose proof usp_lo. pose proof usp_hi.
    unfold eaddz, uE. rewrite mkAlu_denot, edenot_lit, edenot_e_sp0. rewrite u_add64, u_lit64.
    fold usp. unfold STK_OFF, two64. lia.
  Qed.

  Lemma u_sp8 : uE E0 (eadd (escale 4096 (EVar V_S1)) (escale 2 (EVar V_S2))) = usp / 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _).
    unfold eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_envp : uE E0 e_envp = usp + 8 * argc + 16.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. destruct uE0 as (_ & _ & U3 & _).
    pose proof u_e_sp0 as US. unfold e_envp, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite US, U3.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_auxv : uE E0 e_auxv = usp + 8 * argc + 8 * envc + 24.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. destruct uE0 as (_ & _ & _ & U4 & _).
    pose proof u_e_envp as UE. unfold e_auxv, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UE, U4.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma u_e_atrandom : uE E0 (e_atrandom A) = usp + CHEAD - 16.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof gap_range. pose proof chead_eq. pose proof bsb_ge. pose proof RZ_range. pose proof length_bsb_sum.
    pose proof lstr_lo. pose proof pad_range.
    destruct uE0 as (_ & _ & _ & _ & _ & _ & _ & U8).
    pose proof u_e_auxv as UA. unfold e_atrandom, eadd, eaddz, escale, uE, AUXSZ in *. rewrite Hrs.
    rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UA, U8. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_str0 : uE E0 (e_str0 A) = STR0.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof chead_eq. pose proof RZ_range. pose proof gap_range. pose proof bsb_ge.
    pose proof RZ_range. pose proof length_bsb_sum. pose proof lstr_lo.
    destruct uE0 as (_ & _ & _ & _ & _ & U6 & _).
    pose proof u_e_atrandom as UA. unfold e_str0, eadd, eaddz, uE, STR0 in *.
    rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite UA, U6. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_str1 : uE E0 (e_str1 A) = STR0 + L0 + 1.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof chead_eq. pose proof RZ_range. pose proof gap_range. pose proof bsb_ge.
    pose proof length_bsb_sum. pose proof lstr_hi. pose proof RZ_range.
    destruct uE0 as (_ & _ & _ & _ & U5 & _).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    pose proof u_e_str0 as US. unfold e_str1, eadd, eaddz, uE, STR0 in *. rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite US, U5. rewrite !Z.mod_small by lia. lia.
  Qed.

  (** the exec file name is never empty ([Run.valid_execfn]) *)
  Lemma execfn_ne : (1 <= length execfn)%nat.
  Proof.
    destruct Hlaunch as [Hv _]. rewrite inp_execfn in Hv.
    destruct Hv as [[Hl _] | [(ds & -> & _) | (ds & rest & -> & _)]].
    - lia.
    - unfold dev_fd_prefix. rewrite length_app. cbn [length]. lia.
    - unfold dev_fd_prefix. rewrite !length_app. cbn [length]. lia.
  Qed.

  (** argv[0] and argv[1] with their terminators, and the exec file name, all sit in the strings *)
  Lemma str1_room : L0 + L1 + 3 <= LSTR.
  Proof.
    pose proof execfn_ne as Hx.
    unfold LSTR, launch_string_bytes, L0, L1.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
    pose proof Hav0 as Hnz.
    destruct argv as [|a [|b t]] eqn:Ea; [cbn in Hnz; lia| |];
      cbn [flatten_strings flat_map nth]; rewrite !length_app; cbn [length]; lia.
  Qed.

  Lemma utop_le : utop <= 2 ^ 47.
  Proof. pose proof usp_fit. pose proof length_bsb_sum. pose proof str0_hi. unfold STR0 in *. lia. Qed.

  (* [comment removed for export] *)
  Lemma u_e_str1_L1 : uE E0 (eadd (e_str1 A) (EVar V_L1)) = STR0 + L0 + 1 + L1.
  Proof.
    pose proof u_e_str1 as U1. pose proof uE0_L1 as U8. pose proof L1_range. pose proof usp_lo.
    pose proof str1_room. pose proof utop_le. pose proof str0_hi.
    assert (HL0 : 0 <= L0) by (unfold L0; lia).
    unfold eadd, uE in *. rewrite mkAlu_denot, u_add64, U1, U8.
    rewrite Z.mod_small by (pose proof chead_range; pose proof pad_range; unfold STR0 in *; lia). lia.
  Qed.


  Lemma u_e_atr8 : uE E0 e_atr8 = usp / 8 + argc + envc + G.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof gap_range.
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8). pose proof u_sp8 as U9.
    unfold e_atr8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia.
    rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit, !u_add64, !u_mul64, !u64_lit in U9 by lia.
    rewrite U1, U2, U3, U4, U8 in *. rewrite !Z.mod_small by lia. rewrite !Z.mod_small in U9 by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.
  Definition FULL0 : word -> option byte := wrap_mem inp mbase ph entryw sp rdraw.
  (* [comment removed for export] *)
  Definition model0 : Model :=
    with_vdso (vdso_run_init (ed_vdso rdraw))
      (init_model (segments_reserved segs) brk0 mbase sp LIMIT inp).

  Let cs0 := init_acs_of A.
  Let cs0z := init_acs_of_zero A.   (* [comment removed for export] *)
  Let hid0 := hid A argH0 E0 cs0 model0.
  Let Mr0 := Mr A argH0 E0 cs0 model0 FULL0.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let VTOP : Z :=
    page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)).
  Let RESX : list (word * word) := vdso_reserved (in_kernel inp) VTOP.

  Lemma model0_facts :
    m_halted model0 = None /\ m_fds model0 = fds_std /\ m_tid model0 = None
    /\ vm_reserved (m_vmmaps model0) = segments_reserved segs ++ RESX /\ vm_maps (m_vmmaps model0) = []
    /\ vm_noaccess (m_vmmaps model0) = [] /\ m_vm_lazy model0 = [] /\ m_vm_materialized model0 = []
    /\ vm_limit (m_vmmaps model0) = LIMIT /\ vm_brk (m_vmmaps model0) = brk0 /\ vm_start_brk (m_vmmaps model0) = brk0
    /\ vm_mmap_base (m_vmmaps model0) = mbase /\ eager_used model0 = 0.
  Proof. repeat split; reflexivity. Qed.

  Lemma sum_sizes_app : forall l1 l2, sum_sizes (l1 ++ l2) = sum_sizes l1 + sum_sizes l2.
  Proof.
    induction l1 as [|iv l1 IH]; intro l2; cbn [app sum_sizes]; [lia|]. rewrite IH. lia.
  Qed.

  Lemma mb_range : mmap_base_min <= bv_unsigned mbase <= mmap_base_max
                   /\ bv_unsigned mbase mod page_size = 0.
  Proof. destruct Hmb as (Y1 & Y2 & Y3). repeat split; assumption. Qed.

  (* [comment removed for export] *)
  Lemma vtop_range : mmap_base_min - 4095 <= VTOP <= bv_unsigned mbase
                     /\ VTOP mod 4096 = 0.
  Proof.
    pose proof mb_range as ((Y1 & Y2) & Y3). pose proof usp_lo.
    unfold VTOP, page_round_down_Z, page_size, stack_max_size,
           mmap_base_min, mmap_base_max, sp_window_hi, usp in *.
    split; [split|]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma resx_eq : RESX = [(Z_to_bv 64 (VTOP - 24576), Z_to_bv 64 16384);
                          (Z_to_bv 64 (VTOP - 24576 + 16384), Z_to_bv 64 8192)].
  Proof.
    pose proof vtop_range as [[T1 T2] T3].
    unfold RESX, vdso_reserved. cbv zeta.
    rewrite (pinned_vdso_len (in_kernel inp) Hkernel).
    rewrite (pinned_vdso_text_pages (in_kernel inp) Hkernel).
    replace (vdso_len default_kernel) with 24576 by (vm_compute; reflexivity).
    replace (vdso_vvar_pages * page_size)%Z with 16384 by (vm_compute; reflexivity).
    replace (vdso_text_pages default_kernel * page_size)%Z with 8192 by (vm_compute; reflexivity).
    replace (VTOP - 24576 <? page_size)%Z with false
      by (symmetry; apply Z.ltb_ge; unfold page_size, mmap_base_min in *; lia).
    reflexivity.
  Qed.

  Lemma resx_len : (length RESX <= 2)%nat.
  Proof. rewrite resx_eq. cbn [length]. lia. Qed.

  Lemma resx_sum : sum_sizes RESX = 24576.
  Proof.
    pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
    rewrite resx_eq. cbn [sum_sizes fst snd].
    rewrite !u64_lit by (unfold mmap_base_min, mmap_base_max, sp_window_hi in *; lia). lia.
  Qed.

  Lemma resx_bytes_lo : 81920 <= resx_bytes A.
  Proof.
    pose proof (if_resx _ _ _ IMG) as [RX1 RX2]. unfold resx_bytes. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma alloc_top0 : alloc_top (m_vmmaps model0) = usp - 8388608.
  Proof. reflexivity. Qed.
  Lemma hid0_eq : forall a : word, hid0 a = (argH0 E0 a || negb (APS.in_hull A (bv_unsigned a) || (usp - 8388608 <=? bv_unsigned a)))%bool.
  Proof.
    intros a. unfold hid0, hid, vis. rewrite alloc_top0. destruct model0_facts as (_&_&_&_&Hm&Hn&Hl&_). rewrite Hm. cbn [in_ivs existsb andb].
    rewrite orb_false_r. reflexivity.
  Qed.

  Lemma Mr0_visible : forall a : word, usp - 8388608 <= bv_unsigned a -> argH0 E0 a = false -> Mr0 a = FULL0 a.
  Proof.
    intros a Hc Ha. unfold Mr0, Mr, mrestrict. fold hid0. rewrite hid0_eq, Ha.
    replace (usp - 8388608 <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; exact Hc). rewrite orb_true_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma FULL0_below : forall a : word, usp - 6144513 <= bv_unsigned a < usp -> FULL0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. unfold FULL0, wrap_mem.
    assert (HW : stack_window_lo (in_kernel inp) mbase rdraw
                 <= bv_unsigned sp + stack_window_reach - stack_max_size)
      by exact (stack_window_lo_valid inp sp brk0 mbase rdraw Hlaunch Hlau).
    assert (Hs : stack_to_mem sp bsb a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold bsb. rewrite Hs.
    unfold stack_window_reach, stack_max_size, usp in *.
    replace (Z.leb (stack_window_lo (in_kernel inp) mbase rdraw) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  Qed.

  Lemma FULL0_low : forall a : word, bv_unsigned a < usp - 8388608 -> FULL0 a = None.
  Proof.
    intros a Ha. unfold FULL0, wrap_mem.
    pose proof (stack_window_lo_ge_sp inp sp brk0 mbase rdraw Hlau) as HW.
    assert (Hs : stack_to_mem sp bsb a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold bsb. rewrite Hs. unfold stack_max_size, usp in *.
    replace (Z.leb (stack_window_lo (in_kernel inp) mbase rdraw) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_Mr0_stack : forall (a : word) n,
    usp <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
    (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> argH0 E0 x = false) ->
    rdn segs Mr0 a n = rdn segs (stack_to_mem sp bsb) a n.
  Proof.
    intros a n Ha Hn Hvis. pose proof usp_lo. unfold bsb.
    rewrite <- (rdn_wrap_stack_above segs inp mbase ph entryw sp rdraw a n) by (unfold usp in *; lia).
    apply rdn_ext; [exact Hn|]. intros x Hx. apply Mr0_visible; [unfold usp in *; lia | apply Hvis; exact Hx].
  Qed.

  Lemma split_u : forall E e b k, split_lit e = (b, k) -> 0 <= k -> k <= uE E e ->
    bv_unsigned (edenot E b) + k = uE E e.
  Proof.
    intros E e b k Hs Hk Hle. unfold uE in *. rewrite (split_lit_denot E e b k Hs) in Hle |- *.
    pose proof (u64_range (edenot E b)) as Rb.
    rewrite Z_to_bv_unsigned in Hle |- *. unfold bv_wrap, bv_modulus in *. change (2 ^ Z.of_N 64) with (2 ^ 64) in *.
    destruct (Z_lt_le_dec (bv_unsigned (edenot E b) + k) (2 ^ 64)).
    - rewrite Z.mod_small by lia. reflexivity.
    - exfalso.
      assert ((bv_unsigned (edenot E b) + k) mod 2 ^ 64 = bv_unsigned (edenot E b) + k - 2 ^ 64).
      { replace (bv_unsigned (edenot E b) + k) with ((bv_unsigned (edenot E b) + k - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      lia.
  Qed.

  Lemma adenot_SA : forall E b k, adenot E (SA b k) = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
  Proof. intros. unfold adenot, v_addi. cbn [a_base a_off]. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma argH0_range : forall a : word, argH0 E0 a = true ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 8 * envc + 24
    \/ STR0 <= bv_unsigned a < utop.
  Proof.
    intros a H. unfold argH0 in H.
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; [left|right]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma not_argH0 : forall a : word,
    (bv_unsigned a < usp + 8 * argc + 16 \/ (usp + 8 * argc + 8 * envc + 24 <= bv_unsigned a < STR0)
     \/ utop <= bv_unsigned a) -> argH0 E0 a = false.
  Proof.
    intros a H. destruct (argH0 E0 a) eqn:Ha; [|reflexivity]. apply argH0_range in Ha.
    pose proof len_av. pose proof len_ev. pose proof chead_eq. pose proof RZ_range. pose proof pad_range.
    pose proof gap_range. pose proof str0_hi. pose proof lstr_lo. unfold STR0 in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kword_stack : forall b k v (w : word),
    bv_unsigned (edenot E0 b) + k = bv_unsigned w ->
    usp <= bv_unsigned w -> bv_unsigned w + 8 <= usp + Z.of_nat (length bsb) ->
    (forall x : word, bv_unsigned w <= bv_unsigned x < bv_unsigned w + 8 -> argH0 E0 x = false) ->
    rdn segs (stack_to_mem sp bsb) w 8%nat = Some (word_le8 (edenot E0 v)) ->
    kentry_ok segs E0 Mr0 (KWord (SA b k) 8 v).
  Proof.
    intros b k v w Hw Hlo Hhi Hvis Hrd. pose proof usp_fit. pose proof usp_lo. pose proof (u64_range w).
    cbn [kentry_ok]. split; [lia|].
    assert (Hfl : flat E0 (SA b k) (Z.of_nat 8)) by (unfold flat, estart; cbn [a_base a_off]; change (Z.of_nat 8) with 8; lia).
    split; [exact Hfl|].
    rewrite adenot_SA. cbn [a_base a_off]. rewrite Hw, Z_to_bv_bv_unsigned.
    rewrite rdn_Mr0_stack; [| lia | change (Z.of_nat 8) with 8; lia | exact Hvis].
    rewrite Hrd. rewrite n_to_le_8_spec. reflexivity.
  Qed.

  Lemma spb_eq : split_lit e_sp0 = (e_sp0, 0).
  Proof. reflexivity. Qed.

  Let AUXW := auxv_words la ph entryw uid gid hw
                (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn).

  (* [comment removed for export] *)
  (* the bound is the vector's own, [2 * auxv_count rseq] words (fuzz_bigint's
     [AsanInitK.auxv_word_ok]), so it holds at both layouts *)
  Lemma auxv_word_ok : forall (j : nat) v,
    (j < 2 * auxv_count rseq)%nat ->
    nth j AUXW (Z_to_bv 64 0) = edenot E0 v ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 v).
  Proof.
    intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof RZ_range. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum.
    pose proof lstr_lo. pose proof bsb_ge. pose proof RZ_range. pose proof auxv_count_RZ.
    assert (Hab : split_lit e_auxv = (fst e_auxb, snd e_auxb)) by (unfold e_auxb; destruct (split_lit e_auxv); reflexivity).
    set (ab := fst e_auxb) in *. set (ak := snd e_auxb) in *.
    pose proof (split_u E0 e_auxv ab ak Hab) as Hs. rewrite u_e_auxv in Hs.
    assert (Hak : ak = 24) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    apply (kword_stack ab (ak + 8 * Z.of_nat j) v (sp + nat_to_word (auxv_off argv envp + 8 * j))%bv).
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold auxv_off, usp in *; [|lia].
      rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul in Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. unfold STR0. lia.
    - rewrite <- Hv.
      exact (read_auxv_word segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi' j Hj).
  Qed.

  Lemma auxw_ok : forall i ty v,
    (0 <= i < Z.of_nat (auxv_count rseq)) ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    nth (Z.to_nat (2 * i + 1)) AUXW (Z_to_bv 64 0) = edenot E0 v ->
    know_ok segs E0 Mr0 (auxw i ty v).
  Proof.
    intros i ty v Hi H1 H2. unfold auxw.
    constructor; [|constructor; [|constructor]].
    - replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia. apply auxv_word_ok; [pose proof auxv_count_RZ; lia|]. rewrite H1. reflexivity.
    - replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia. apply auxv_word_ok; [pose proof auxv_count_RZ; lia|]. exact H2.
  Qed.

  (** The a_type leg of an auxv pair on its own.  [auxw_ok] proves both legs and so needs the
      VALUE too; musl's AT_RANDOM scan reads only [a_type] until it reaches pair 24, so the
      rows that unblock the start-up walk need just this half.  The body is [auxw_ok]'s first
      bullet verbatim.  The bound is the vector's own, so it holds at both layouts. *)
  Lemma auxv_type_ok : forall i ty,
    (0 <= i < Z.of_nat (auxv_count rseq)) ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 16 * i)) 8 (ELit ty)).
  Proof.
    intros i ty Hi H1.
    replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia.
    apply auxv_word_ok; [pose proof auxv_count_RZ; lia|]. rewrite H1. reflexivity.
  Qed.

  (** The a_val leg of an auxv pair on its own, the mirror of [auxv_type_ok].  The body is
      [auxw_ok]'s SECOND bullet verbatim (:931).  Both halves are needed because musl's
      [__init_libc] walk is `for (i = 0; auxv[i]; i += 2) ... aux[auxv[i]] = auxv[i+1];` --
      it reads the VALUE of every pair, so a type row without its value row only moves the
      halt from the type load to the value load one instruction later.  Unlike [auxw_ok] this
      does not demand the type word, so the two legs of one pair may be supplied from
      different places: the thirteen CLOSED values go in [init_kn_with] beside their types,
      and the four whose value is a free Section variable ([sp] and [mbase] for pair 0, [hw] for pair 9,
      [gid] for 21 and 22) take a plan slot at the [init_kn_hw] layer instead.
      The bound is the vector's own, as for [auxv_type_ok]. *)
  Lemma auxv_val_ok : forall i v,
    (0 <= i < Z.of_nat (auxv_count rseq)) ->
    nth (Z.to_nat (2 * i + 1)) AUXW (Z_to_bv 64 0) = edenot E0 v ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 16 * i + 8)) 8 v).
  Proof.
    intros i v Hi H2.
    replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia.
    apply auxv_word_ok; [pose proof auxv_count_RZ; lia|]. exact H2.
  Qed.

  Lemma kr_ok : forall e lo hi, lo <= uE E0 e <= hi -> kentry_ok segs E0 Mr0 (KRange e lo hi).
  Proof. intros e lo hi H. cbn [kentry_ok]. unfold uE in H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma Mr0_below : forall a : word, usp - 6144513 <= bv_unsigned a < usp -> Mr0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. pose proof usp_lo. pose proof len_av.
    rewrite Mr0_visible; [apply FULL0_below; exact Ha | unfold usp in *; lia | apply not_argH0; lia].
  Qed.

  Lemma stack_window_ok :
    kentry_ok segs E0 Mr0 (KWr (SA e_sp0 (-6144513)) (ELit 6144513))
    /\ kentry_ok segs E0 Mr0 (KZero (SA e_sp0 (-6144513)) (ELit 6144513)).
  Proof.
    pose proof usp_lo. pose proof usp_hi.
    assert (Hst : estart E0 (SA e_sp0 (-6144513)) = usp - 6144513).
    { unfold estart. cbn [a_base a_off]. pose proof u_e_sp0 as U. unfold uE in U. rewrite U. lia. }
    assert (Hl : elenZ E0 (ELit 6144513) = 6144513) by (apply elenZ_lit; lia).
    assert (Hfl : flat E0 (SA e_sp0 (-6144513)) (elenZ E0 (ELit 6144513))).
    { unfold flat. rewrite Hst, Hl. lia. }
    split; cbn [kentry_ok]; (split; [exact Hfl|]); rewrite Hst, ?Hl.
    - intros d m Hd Hdm. apply store_ok_of_all; rewrite u_small by lia; [lia|].
      intros x Hx. unfold wview. rewrite (Mr0_below x) by lia. discriminate.
    - intros i Hi. apply Mr0_below. rewrite u_small by lia. lia.
  Qed.

  Lemma argc_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 0) 8 (EVar V_ARGC)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge.
    apply (kword_stack e_sp0 0 (EVar V_ARGC) sp).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. unfold usp. lia.
    - unfold usp. lia.
    - unfold usp in *. lia.
    - intros x Hx. apply not_argH0. unfold usp in *. lia.
    - pose proof (read_argc inp mbase ph entryw segs sp rdraw) as RW.
      assert (Hv : len_word argv = edenot E0 (EVar V_ARGC)).
      { apply bv_eq. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. rewrite U3.
        pose proof len_av. unfold len_word, argc in *. rewrite u64_lit by lia. reflexivity. }
      rewrite inp_argv in RW. rewrite <- Hv. apply RW. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cat_argv0_eq :
    bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) = STR0.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof RZ_range. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum.
    rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0 Hav0).
    change (total_arg_bytes_nat (firstn 0 (in_argv inp))) with 0%nat.
    rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
    change (in_kernel inp) with kern. change (in_execfn inp) with execfn.
    change (in_argv inp) with argv. change (in_envp inp) with envp.
    unfold STR0, CHEAD, W, usp, rseq, top, cat_string_off in *.
    rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia.
  Qed.

  Lemma argv0_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 8) 8 (e_str0 A)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge.
    apply (kword_stack e_sp0 8 (e_str0 A) (sp + nat_to_word (8 + 8 * 0))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
    - pose proof (read_argv_ptr_k segs inp mbase ph entryw sp rdraw 0) as RW.
      assert (Hv : cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0
                   = edenot E0 (e_str0 A)).
      { apply bv_eq. rewrite cat_argv0_eq. pose proof u_e_str0 as U. unfold uE in U. rewrite U. reflexivity. }
      rewrite <- Hv. apply RW; [exact Hav0|]. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma argv1_word_ok : kentry_ok segs E0 Mr0 (kw_argv1 (e_argv1w A)).
  Proof.
    unfold kw_argv1.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge.
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    assert (Hw1 : edenot E0 (e_argv1w A) = if (1 <? argc) then edenot E0 (e_str1 A) else Z_to_bv 64 0).
    { unfold e_argv1w. cbn [edenot]. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. cbn [edenot] in U3.
      apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit, U3 by lia.
      pose proof (u64_range (edenot E0 (e_str1 A))).
      destruct (1 <? argc); [rewrite Z.mul_1_l, Z.mod_small by lia; reflexivity | rewrite u64_lit by lia; reflexivity]. }
    apply (kword_stack e_sp0 16 (e_argv1w A) (sp + nat_to_word (8 + 8 * 1))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
    - rewrite Hw1. destruct (1 <? argc) eqn:Hc.
      + apply Z.ltb_lt in Hc. assert (Hav1 : (1 < length argv)%nat) by (unfold argc in Hc; lia).
        pose proof (read_argv_ptr_k segs inp mbase ph entryw sp rdraw 1) as RW.
        assert (Hv : cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1
                     = edenot E0 (e_str1 A)).
        { apply bv_eq.
          pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof RZ_range.
          assert (TF : forall l : list (list byte), (0 < length l)%nat ->
                        Z.of_nat (total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1)
            by (intros [|x t] Hl; [cbn in Hl; lia|]; change (firstn 1 (x :: t)) with [x]; cbn -[Z.of_nat Z.add]; lia).
          pose proof (TF argv Hav0) as TF0.
          pose proof u_e_str1 as U. unfold uE in U.
          rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1 Hav1).
          rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
          change (in_kernel inp) with kern. change (in_execfn inp) with execfn.
          change (in_argv inp) with argv. change (in_envp inp) with envp.
          rewrite U. unfold STR0, CHEAD, W, usp, L0, rseq, top, cat_string_off in *.
          rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia. }
        rewrite <- Hv. apply RW; [exact Hav1|]. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
      + apply Z.ltb_ge in Hc. assert (Hav1 : length argv = 1%nat) by (unfold argc in Hc; pose proof Hav0; lia).
        pose proof (read_argv_null segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as RW.
        rewrite inp_argv in RW. rewrite Hav1 in RW.
        exact RW.
  Qed.

  (* [comment removed for export] *)
  Lemma atrandom_ok : kentry_ok segs E0 Mr0 (KBlob (SA (fst (e_atrb A)) (snd (e_atrb A))) (ELit 16) K_RND).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge.
    pose proof chead_eq. pose proof RZ_range. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof lstr_lo.
    pose proof RZ_range.
    assert (Hab : split_lit (e_atrandom A) = (fst (e_atrb A), snd (e_atrb A))) by (unfold e_atrb; destruct (split_lit (e_atrandom A)); reflexivity).
    set (ab := fst (e_atrb A)) in *. set (ak := snd (e_atrb A)) in *.
    pose proof (split_u E0 (e_atrandom A) ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    assert (Hak : ak = 24 + AUXSZ RZ) by (subst ak; rewrite (e_atrb_off A a_rseq_01), Hrs; reflexivity).
    unfold AUXSZ in Hak.
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + CHEAD - 16) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl.
    assert (HE : eb E0 K_RND = at_random_bytes (ed_random rdraw)) by (unfold E0; cbn [eb]; rewrite Nat.eqb_refl; reflexivity).
    rewrite HE.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    split; [rewrite length_at_random_bytes; reflexivity|].
    intros i Hi.
    destruct (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as [off (Hp & Hoff & Hmod & Hrd)].
    rewrite inp_argv, inp_envp, inp_rseq in Hp, Hoff, Hrd.
    assert (Hu : bv_unsigned (at_random_ptr sp rseq argv envp) = usp + CHEAD - 16).
    { rewrite Hp, word_add_nat, u64_lit by (unfold usp in *; lia). unfold CHEAD. lia. }
    specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold bsb in Hrd.
    rewrite (AsanCeil.firstn1_skipn_nth _ _ (Z_to_bv 8 0)) in Hrd by (rewrite length_at_random_bytes; lia).
    assert (Ha : (at_random_ptr sp rseq argv envp + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + CHEAD - 16 + i)).
    { apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
    rewrite Ha in Hrd.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold STR0, usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw) by (rewrite u64_lit; unfold usp in *; lia). fold bsb.
    cbn [rdn] in Hrd.
    destruct (stack_to_mem sp bsb (Z_to_bv 64 (usp + CHEAD - 16 + i))) as [b|] eqn:Hstk.
    - cbn in Hrd. injection Hrd as ->. reflexivity.
    - exfalso. unfold stack_to_mem in Hstk. fold usp in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
      replace (usp <=? usp + CHEAD - 16 + i) with true in Hstk by (symmetry; apply Z.leb_le; lia).
      cbv zeta in Hstk.
      replace (usp + CHEAD - 16 + i - usp <? Z.of_nat (length bsb)) with true in Hstk by (symmetry; apply Z.ltb_lt; lia).
      apply nth_error_None in Hstk. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma atrandom_zero_ok : kentry_ok segs E0 Mr0 (KZero (SA (fst (e_atrb A)) (snd (e_atrb A))) (ELit 16)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge.
    pose proof chead_eq. pose proof RZ_range. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof lstr_lo.
    pose proof RZ_range.
    assert (Hab : split_lit (e_atrandom A) = (fst (e_atrb A), snd (e_atrb A))) by (unfold e_atrb; destruct (split_lit (e_atrandom A)); reflexivity).
    set (ab := fst (e_atrb A)) in *. set (ak := snd (e_atrb A)) in *.
    pose proof (split_u E0 (e_atrandom A) ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    assert (Hak : ak = 24 + AUXSZ RZ) by (subst ak; rewrite (e_atrb_off A a_rseq_01), Hrs; reflexivity).
    unfold AUXSZ in Hak.
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + CHEAD - 16) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    intros i Hi.
    destruct (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as [off (Hp & Hoff & Hmod & Hrd)].
    rewrite inp_argv, inp_envp, inp_rseq in Hp, Hoff, Hrd.
    assert (Hu : bv_unsigned (at_random_ptr sp rseq argv envp) = usp + CHEAD - 16).
    { rewrite Hp, word_add_nat, u64_lit by (unfold usp in *; lia). unfold CHEAD. lia. }
    specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold bsb in Hrd.
    pose proof Hzr as Hz0. unfold AsanCeil.zero_random_draw in Hz0.
    rewrite Hz0, AsanCeil.at_random_bytes_zero, repeat_firstn_skipn in Hrd by lia.
    assert (Ha : (at_random_ptr sp rseq argv envp + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + CHEAD - 16 + i)).
    { apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
    rewrite Ha in Hrd.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold STR0, usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw) by (rewrite u64_lit; unfold usp in *; lia). fold bsb.
    cbn [rdn] in Hrd.
    destruct (stack_to_mem sp bsb (Z_to_bv 64 (usp + CHEAD - 16 + i))) as [b|] eqn:Hstk.
    - cbn in Hrd. injection Hrd as ->. reflexivity.
    - exfalso. unfold stack_to_mem in Hstk. fold usp in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
      replace (usp <=? usp + CHEAD - 16 + i) with true in Hstk by (symmetry; apply Z.leb_le; lia).
      cbv zeta in Hstk.
      replace (usp + CHEAD - 16 + i - usp <? Z.of_nat (length bsb)) with true in Hstk by (symmetry; apply Z.ltb_lt; lia).
      apply nth_error_None in Hstk. lia.
  Qed.

  Lemma kimg_ok : kentry_ok segs E0 Mr0 (KImg (img_lo A) (img_hi A)).
  Proof.
    pose proof usp_lo. pose proof (if_hull _ _ _ IMG) as (H1 & H2 & H3 & H4). cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    unfold Mr0, Mr, mrestrict. destruct (hid A argH0 E0 cs0 model0 (Z_to_bv 64 i)); [reflexivity|].
    apply FULL0_low. rewrite u64_lit; lia.
  Qed.

  Lemma rw_window_ok : kentry_ok segs E0 Mr0 (KWr (SA (ELit 0) (rw_lo A)) (ELit (rw_len A))).
  Proof.
    pose proof (if_rw _ _ _ IMG) as ((R1 & R0 & R2) & R3).
    assert (Hst : estart E0 (SA (ELit 0) (rw_lo A)) = rw_lo A) by (unfold estart; cbn [a_base a_off]; rewrite edenot_lit, u64_lit; lia).
    assert (Hl : elenZ E0 (ELit (rw_len A)) = rw_len A) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. split; [unfold flat; rewrite Hst; lia|].
    intros d m Hd Hdm. destruct m as [|m']; [reflexivity|].
    assert (Hu : bv_unsigned (Z_to_bv 64 (rw_lo A + d)) = rw_lo A + d) by (apply u_small; rewrite Nat2Z.inj_succ in Hdm; lia).
    apply store_ok_of_all; rewrite Hu; [lia|].
    intros x Hx. apply R3. lia.
  Qed.

  Lemma atr_ptr_eq : at_random_ptr sp rseq argv envp = edenot E0 (e_atrandom A).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof chead_eq. pose proof RZ_range. pose proof gap_range.
    pose proof len_av. pose proof len_ev. pose proof bsb_ge. pose proof RZ_range. pose proof length_bsb_sum.
    destruct (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as [off (Hp & Hoff & _ & _)].
    rewrite inp_argv, inp_envp, inp_rseq in Hp, Hoff.
    apply bv_eq. rewrite Hp, word_add_nat, u64_lit by (unfold CHEAD, usp in *; lia).
    pose proof u_e_atrandom as U. unfold uE in U. rewrite U. unfold CHEAD, usp. lia.
  Qed.

  (* AT_NULL, the one claimed pair whose index moves with the flag: pair [26 + 2 * RZ]
     (fuzz_bigint's [AsanInitK.auxv_null_ok]) *)
  Lemma auxv_null_ok : know_ok segs E0 Mr0 (auxw (26 + 2 * RZ) 0 (ELit 0)).
  Proof.
    pose proof auxv_count_RZ. pose proof RZ_range.
    destruct (auxv_words_null la ph entryw uid gid hw
                (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn)) as [N1 N2].
    apply auxw_ok; [lia | exact N1 | rewrite edenot_lit; exact N2].
  Qed.

  Lemma init_kn_with_ok : forall atr, kentry_ok segs E0 Mr0 atr -> know_ok segs E0 Mr0 (init_kn_with atr A).
  Proof.
    intros atr Hatr.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof gap_range. pose proof chead_eq. pose proof RZ_range. pose proof length_bsb_sum. pose proof lstr_lo.
    pose proof RZ_range. pose proof auxv_count_RZ. pose proof usp_al.
    pose proof brk_range as [B1 B2]. pose proof bsb_ge. pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    pose proof (if_ph _ _ _ IMG) as (P1 & P2 & P3).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    unfold init_kn_with. rewrite Hrs.
    destruct stack_window_ok as [SW1 SW2].
    apply Forall_app; split.
    { apply Forall_cons; [apply kr_ok; rewrite U1; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U2; lia|].
      apply Forall_cons; [apply kr_ok; unfold eaddz, uE; rewrite mkAlu_denot, edenot_lit, u_add64, u64_lit by lia;
                          pose proof u_e_atrandom as U; unfold uE in U; rewrite U; rewrite Z.mod_small by lia; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_atr8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_sp0; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_sp8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U3; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U4; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U5; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_L1; pose proof L1_range; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_uid; unfold valid_id in Huid; pose proof (u64_range uid); lia|].
      apply Forall_cons; [apply kr_ok; rewrite U8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U6; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U7; unfold BRK_ASLR in *; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_str1; pose proof str1_room; pose proof utop_le; pose proof str0_hi;
                          pose proof L1_range; unfold STR0 in *; lia|].   (* [comment removed for export] *)
      apply Forall_cons; [apply kr_ok; rewrite u_e_str1_L1; pose proof str1_room; pose proof utop_le; pose proof str0_hi;
                          pose proof L1_range; unfold STR0 in *; lia|].
      apply Forall_cons; [exact SW1|].
      apply Forall_cons; [exact SW2|].
      apply Forall_cons; [exact argc_word_ok|].
      apply Forall_cons; [exact argv0_word_ok|].
      apply Forall_cons; [exact argv1_word_ok|].
      apply Forall_nil. }
    repeat (apply Forall_app; split).
    (* AT_NULL (pair [26 + 2 * RZ]): its index is symbolic in the free field, so no [cbn]
       closes it; [auxv_null_ok] is the case split. *)
    9: exact auxv_null_ok.
    (* pairs 13, 14, 15, 11, 19, 20, 23 and 24: all below the CONFIG_RSEQ pair, so the same
       words under both layouts *)
    1-8: apply auxw_ok;
         [ lia
         | unfold AUXW, auxv_words, auxv_entries;
           cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
           try reflexivity .. ].
    all: try (rewrite edenot_lit; reflexivity).
    1: rewrite edenot_lit, P1; reflexivity.
    1: rewrite edenot_lit, P2; reflexivity.
    1: rewrite edenot_lit, P3; reflexivity.
    1: exact atr_ptr_eq.
    apply Forall_cons; [exact Hatr|].
    apply Forall_cons; [exact kimg_ok|].
    apply Forall_cons; [exact rw_window_ok|].
    (* The sixteen a_type rows of [init_kn_with] outside its [auxw] pairs: pairs 0-9, 12, 16, 17, 18, 21, 22.
       All discharged uniformly by [auxv_type_ok], which is [auxw_ok]'s first bullet (:930)
       on its own -- the index bound by [lia], the word by computing the (2*i)th [AUXW] entry
       from [auxv_entries].  Proved FROM the start-up facts, not assumed.  The rows are
       literals that name no variable and need no environment entry, so
       [kn_vars_lt_init_kn] computes and [init_kn_hw_ok] carries the rows to [E0hw]
       through [know_ok_agree'].  Kernel-free at both values of [kb_rseq]:
       every index is below 27 and [auxv_count] is 27 without CONFIG_RSEQ, 29 with it. *)
    (* Exactly sixteen: a [repeat] here goes on to try [auxv_type_ok] on the first a_val row,
       and the failed unification of its offset [16 * ?i] with [snd e_auxb + 16 * i + 8] is
       very slow. *)
    do 16 (apply Forall_cons;
      [ apply auxv_type_ok; [lia|];
        unfold AUXW, auxv_words, auxv_entries;
        cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
        reflexivity
      |]).
    (* The THIRTEEN a_val rows after them: pairs 1-8 (the cache words), 12, 16, 17
       and 18.  Discharged by [auxv_val_ok], which is [auxw_ok]'s SECOND bullet on its
       own, so each one is proved from [AUXW] exactly as its type row was.  The [do 16] above
       stops before them: [auxv_type_ok]'s conclusion has offset [16 * i] and these have
       [16 * i + 8], which do not unify (and the checker is very slow to find that out),
       so no clause of either block can take the other's row.  These rows name no variable
       either, and need no environment entry --
       every value here is CLOSED, which is the reason these thirteen could be written into
       the plan at all.  [la_cache_pinned] is what closes the eight cache words: [Hkernel]
       pins [kb_cache] to [default_kernel]'s and [launch_cache_words] reads nothing else. *)
    repeat (apply Forall_cons;
      [ apply auxv_val_ok; [lia|];
        unfold AUXW, auxv_words, auxv_entries;
        cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
        rewrite ?la_cache_pinned, edenot_lit, ?Z_to_bv_bv_unsigned; reflexivity
      |]).
    (* Pair 18, AT_ENTRY, is the one of the thirteen whose value is not computed but TIED:
       [Hapc] is the hypothesis that makes the image's [a_entry A] the launch's entry word. *)
    apply Forall_cons.
    { apply auxv_val_ok; [lia|].
      unfold AUXW, auxv_words, auxv_entries;
        cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul].
      rewrite edenot_lit. unfold entryw. rewrite Hapc. reflexivity. }
    apply Forall_nil.
  Qed.

  Lemma init_kn_ok : know_ok segs E0 Mr0 (init_kn A).
  Proof. exact (init_kn_with_ok _ atrandom_ok). Qed.
  (* [comment removed for export] *)
  Lemma init_kn_zero_ok : know_ok segs E0 Mr0 (init_kn_zero A).
  Proof. exact (init_kn_with_ok _ atrandom_zero_ok). Qed.

  (* The rest of the vector ([auxv_rest]), at parity with fuzz_bigint's [AsanInitK.auxv_unk_ok] /
     [auxv_rseq_ok] and bzip2's [K/AS/AsanInit.v].
     *)
  (* the whole vector is readable ([KUnk]): it is visible block memory below argv[0] *)
  Lemma auxv_unk_ok : kentry_ok segs E0 Mr0 (KUnk (SA (fst e_auxb) (snd e_auxb)) (ELit (AUXSZ RZ))).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof RZ_range. pose proof chead_range. pose proof pad_range. pose proof gap_range.
    pose proof length_bsb_sum. pose proof lstr_lo. pose proof bsb_ge. pose proof RZ_range.
    pose proof str0_hi. pose proof pad_eq.
    assert (Hab : split_lit e_auxv = (fst e_auxb, snd e_auxb)) by (unfold e_auxb; destruct (split_lit e_auxv); reflexivity).
    set (ab := fst e_auxb) in *. set (ak := snd e_auxb) in *.
    pose proof (split_u E0 e_auxv ab ak Hab) as Hs. rewrite u_e_auxv in Hs.
    assert (Hak : ak = 24) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + 8 * argc + 8 * envc + 24) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit (AUXSZ RZ)) = AUXSZ RZ) by (apply elenZ_lit; unfold AUXSZ; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. unfold AUXSZ in *.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    intros i Hi.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold STR0, usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw) by (rewrite u64_lit; unfold usp in *; lia). fold bsb.
    unfold stack_to_mem. fold usp. rewrite u64_lit by (unfold usp in *; lia).
    replace (usp <=? usp + 8 * argc + 8 * envc + 24 + i) with true by (symmetry; apply Z.leb_le; lia).
    cbv zeta.
    replace (usp + 8 * argc + 8 * envc + 24 + i - usp <? Z.of_nat (length bsb)) with true by (symmetry; apply Z.ltb_lt; lia).
    intros Hn. apply nth_error_None in Hn. lia.
  Qed.

  (* the CONFIG_RSEQ pair (26, 27), claimed only at [RZ = 1], where it is in the vector *)
  Lemma auxv_rseq_ok :
    know_ok segs E0 Mr0 (if Z.eqb RZ 1 then auxw 26 27 (ELit 28) ++ auxw 27 28 (ELit 32) else []).
  Proof.
    unfold RZ, rseq, rseq_z.
    destruct (Bool.bool_dec (kb_rseq kern) true) as [Hr|Hr]; [| apply Bool.not_true_is_false in Hr];
      rewrite Hr; cbn [Z.eqb Pos.eqb]; [|constructor].
    assert (Hr' : kb_rseq (in_kernel inp) = true) by exact Hr.
    apply Forall_app; split; (apply auxw_ok;
      [ pose proof auxv_count_RZ as HC; unfold RZ, rseq, rseq_z in HC |- *; rewrite Hr in HC |- *; lia
      | unfold AUXW, la, launch_auxv, auxv_words, auxv_entries; cbn [la_rseq]; rewrite ?Hr, ?Hr';
        cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
        first [reflexivity | (rewrite edenot_lit; reflexivity)]
      | unfold AUXW, la, launch_auxv, auxv_words, auxv_entries; cbn [la_rseq]; rewrite ?Hr, ?Hr';
        cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
        first [reflexivity | (rewrite edenot_lit; reflexivity)] ]).
  Qed.

  Lemma auxv_rest_ok : know_ok segs E0 Mr0 (auxv_rest A).
  Proof.
    pose proof auxv_count_RZ. pose proof RZ_range.
    unfold auxv_rest. rewrite Hrs.
    apply Forall_cons.
    { apply auxv_type_ok; [lia|].
      unfold AUXW, auxv_words, auxv_entries.
      cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul].
      reflexivity. }
    apply Forall_app; split; [exact auxv_rseq_ok|].
    apply Forall_cons; [exact auxv_unk_ok | apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma init_regs_nth : forall n, nth n init_regs (ELit 0) = if Nat.eqb n 2 then e_sp0 else ELit 0.
  Proof.
    intros n. unfold init_regs.
    do 32 (destruct n as [|n]; [reflexivity|]). cbn. destruct n; reflexivity.
  Qed.

  Lemma init_regs_ok : regs_ok E0 init_regs R0.
  Proof.
    intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
    - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
    - rewrite init_regs_nth. pose proof (ridx_range r) as Hlt.
      destruct (Nat.eqb (ridx r) 2) eqn:H2.
      + apply Nat.eqb_eq in H2. rewrite edenot_e_sp0.
        assert (r = 2%bv) by (rewrite <- (ridx_roundtrip r); rewrite H2; apply bv_eq; reflexivity). subst r. reflexivity.
      + rewrite edenot_lit. apply Nat.eqb_neq in H2.
        rewrite <- (ridx_roundtrip r). rewrite <- (ridx_roundtrip r) in Hr0.
        set (n := ridx r) in *. clearbody n.
        do 32 (destruct n as [|n]; [first [exfalso; lia | vm_compute in Hr0 |- *; first [discriminate | reflexivity]] |]).
        exfalso. lia.
  Qed.

Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.   (* [comment removed for export] *)
  Lemma allowA_init : allowA A E0 cs0 =
    [(pagedown (img_lo A), pageup (img_lo A + (img_hi A - img_lo A)));
     (pagedown (shadow_off A + img_lo A / 8), pageup (shadow_off A + (img_lo A + (img_hi A - img_lo A)) / 8));
     (pagedown (usp - 8388608), pageup (usp - 8388608 + STK_VLEN));
     (pagedown (shadow_off A + (usp - 8388608) / 8), pageup (shadow_off A + (usp - 8388608 + STK_VLEN) / 8))].
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    unfold allowA, cs0, init_acs_of, init_acs_of_with, init_vis. cbn [a_vis a_ghost app flat_map allow1 fst snd].
    unfold sh_lo, sh_hi. cbn [fst snd]. rewrite !u_stk0.
    unfold uE. rewrite !edenot_lit, !u64_lit by (unfold STK_VLEN; lia). reflexivity.
  Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

  Lemma abytes_init : A_bytes (allowA A E0 cs0) <= vis_cost (img_hi A - img_lo A) + vis_cost STK_VLEN
                      /\ vis_cost (img_hi A - img_lo A) + vis_cost STK_VLEN <= LIMIT.
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof (if_shadow _ _ _ IMG) as S1.
    pose proof usp_lo. pose proof usp_hi.
    rewrite allowA_init. cbn [A_bytes fst snd]. unfold vis_cost, STK_VLEN, LIMIT, target_alloc_limit.
    replace (img_lo A + (img_hi A - img_lo A)) with (img_hi A) by lia.
    assert (P1 : forall z, z mod 4096 = 0 -> pagedown z = z) by (intros z Hz; unfold pagedown; lia).
    assert (P2 : forall z, z mod 4096 = 0 -> pageup z = z) by (intros z Hz; unfold pageup; lia).
    rewrite (P1 (img_lo A) I3), (P2 (img_hi A) I4).
    pose proof (pageup_minus_pagedown (shadow_off A + img_lo A / 8) (shadow_off A + img_hi A / 8) ltac:(lia)).
    pose proof (pageup_minus_pagedown (usp - 8388608) (usp - 8388608 + 0x800000) ltac:(lia)).
    pose proof (pageup_minus_pagedown (shadow_off A + (usp - 8388608) / 8) (shadow_off A + (usp - 8388608 + 0x800000) / 8) ltac:(lia)).
    split; lia.
  Qed.

  (* [comment removed for export] *)
  Theorem init_cs_ok : cs_ok segs A LIMIT SINV0 argH0 fs E0 cs0 R0 FULL0 model0.
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
    destruct abytes_init as [AB1 AB2].
    constructor; cbn [cs0 init_acs_of init_acs_of_with a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
      rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
    - exact init_regs_ok.
    - reflexivity.
    - exact init_kn_ok.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - (* the reserved ledger: the image's intervals, then the launch's vDSO/vvar pair *)
      split; [|split].
      + pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
        pose proof (if_hull _ _ _ IMG) as (G1 & G2 & G3 & G4).
        pose proof (if_resx _ _ _ IMG) as [RX1 RX2]. pose proof resx_bytes_lo.
        exists RESX. split; [reflexivity|].
        split; [| split; [pose proof resx_len; lia | rewrite resx_sum; lia]].
        rewrite resx_eq. repeat constructor;
          cbn [fst snd];
          rewrite !u64_lit
            by (unfold mmap_base_min, mmap_base_max, sp_window_hi in *; lia);
          unfold KHI, mmap_base_min, mmap_base_max, sp_window_hi in *; lia.
      + constructor.
      + replace (m_kernel model0) with (in_kernel inp) by reflexivity.
        replace (vdso_top (m_vmmaps model0)) with VTOP
          by (symmetry; exact (vdso_top_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp)).
        apply incl_appr, incl_refl.
    - reflexivity.
    - reflexivity.
    - constructor.   (* [comment removed for export] *)
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      exact (init_sp_ok_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp Hsp).
    - constructor.
    - constructor.
    - intros z Hz. exact Hz.
    - constructor.
    - constructor.
    - rewrite app_nil_r, sum_sizes_app, (if_sizes _ _ _ IMG), resx_sum.
      pose proof resx_bytes_lo. lia.
    - (* [comment removed for export] *) split; [exact u_e_sp0 | destruct Hsp as (_ & Hs2 & _); exact Hs2].
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7 & _). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.
    - lia.
    - lia.
    - exact AB1.
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
    - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
    - split; [intros; reflexivity | intros; reflexivity].
    - (* the launch's reader: [init_model] copies [in_channel_reader inp], which [inp] sets *)
      reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem init_cs_ok_zero : cs_ok segs A LIMIT SINV0 argH0 fs E0 cs0z R0 FULL0 model0.
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
    destruct abytes_init as [AB1 AB2].
    change (allowA A E0 cs0) with (allowA A E0 (init_acs_of_zero A)) in AB1.   (* [comment removed for export] *)
    constructor; unfold cs0z; cbn [init_acs_of_zero init_acs_of_with a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
      rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
    - exact init_regs_ok.
    - reflexivity.
    - exact init_kn_zero_ok.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - (* the reserved ledger: the image's intervals, then the launch's vDSO/vvar pair *)
      split; [|split].
      + pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
        pose proof (if_hull _ _ _ IMG) as (G1 & G2 & G3 & G4).
        pose proof (if_resx _ _ _ IMG) as [RX1 RX2]. pose proof resx_bytes_lo.
        exists RESX. split; [reflexivity|].
        split; [| split; [pose proof resx_len; lia | rewrite resx_sum; lia]].
        rewrite resx_eq. repeat constructor;
          cbn [fst snd];
          rewrite !u64_lit
            by (unfold mmap_base_min, mmap_base_max, sp_window_hi in *; lia);
          unfold KHI, mmap_base_min, mmap_base_max, sp_window_hi in *; lia.
      + constructor.
      + replace (m_kernel model0) with (in_kernel inp) by reflexivity.
        replace (vdso_top (m_vmmaps model0)) with VTOP
          by (symmetry; exact (vdso_top_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp)).
        apply incl_appr, incl_refl.
    - reflexivity.
    - reflexivity.
    - constructor.   (* [comment removed for export] *)
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      exact (init_sp_ok_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp Hsp).
    - constructor.
    - constructor.
    - intros z Hz. exact Hz.
    - constructor.
    - constructor.
    - rewrite app_nil_r, sum_sizes_app, (if_sizes _ _ _ IMG), resx_sum.
      pose proof resx_bytes_lo. lia.
    - (* [comment removed for export] *) split; [exact u_e_sp0 | destruct Hsp as (_ & Hs2 & _); exact Hs2].
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7 & _). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.
    - lia.
    - lia.
    - exact AB1.
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
    - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
    - split; [intros; reflexivity | intros; reflexivity].
    - (* the launch's reader: [init_model] copies [in_channel_reader inp], which [inp] sets *)
      reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem init_cfg_eq :
    init_config segs apc ph sp brk0 mbase rdraw LIMIT inp = cfg_of segs R0 (a_entry A) FULL0 model0.
  Proof.
    (* [comment removed for export] *)
    unfold init_config, cfg_of, FULL0, entryw. rewrite init_mkst, Hapc. reflexivity.
  Qed.

  (** The hwcap start state [init_acs_hw]: the valuation [E0] with [V_HW] set to the hwcap and
      the three auxv a_val slots set to THE MODEL'S OWN TERMS.  Each is the model's expression
      verbatim, not a reduced constant: [la_sysinfo_ehdr la] is
      [Run.vdso_text_base (in_kernel inp) sp mbase], so [vdso_text_pages (in_kernel inp)] stays
      symbolic here and the literal 8192 appears nowhere.  [la_minsigstksz la] is
      [min_sigframe_size] of the free hwcap, and [gid] is the Section's own.  All four slots
      are at or above [NX0] = 9, so [E0hw] agrees with [E0] below [NX0] ([E0hw_agree]), and a
      fact proved at [E0] for terms below [NX0] carries to [E0hw]. *)
  Definition E0hw : env :=
    Env (fun n => if Nat.eqb n V_HW then hw
                  else if Nat.eqb n V_VDSO then la_sysinfo_ehdr la
                  else if Nat.eqb n V_MSS then la_minsigstksz la
                  else if Nat.eqb n V_GID then gid
                  else ev E0 n) (eb E0).

  Lemma E0hw_agree : env_agree NX0 E0 E0hw.
  Proof.
    split; [|reflexivity]. intros n Hn. unfold E0hw. cbn [ev].
    destruct (Nat.eqb n V_HW) eqn:E; [apply Nat.eqb_eq in E; unfold V_HW, NX0 in *; lia|].
    destruct (Nat.eqb n V_VDSO) eqn:E1; [apply Nat.eqb_eq in E1; unfold V_VDSO, NX0 in *; lia|].
    destruct (Nat.eqb n V_MSS) eqn:E2; [apply Nat.eqb_eq in E2; unfold V_MSS, NX0 in *; lia|].
    destruct (Nat.eqb n V_GID) eqn:E3; [apply Nat.eqb_eq in E3; unfold V_GID, NX0 in *; lia|].
    reflexivity.
  Qed.

  (** with no mapping yet, the restricted view does not depend on the valuation or the state *)
  Lemma Mr0_indep : forall E E' cs cs', Mr A argH0 E cs model0 FULL0 = Mr A argH0 E' cs' model0 FULL0.
  Proof.
    intros E E' cs cs'. apply functional_extensionality. intros a. unfold Mr, mrestrict, hid, vis.
    destruct model0_facts as (_&_&_&_&Hm&_). rewrite Hm. cbn [in_ivs existsb andb]. reflexivity.
  Qed.

  Let upd := usp / 4096 * 4096.

  Lemma u_pd0 : uE E0hw e_pd = upd.
  Proof.
    pose proof usp_lo as L. pose proof u_e_sp0 as U.
    unfold uE. rewrite <- (edenot_agree' NX0 E0 E0hw e_pd E0hw_agree) by (vm_compute; reflexivity).
    fold (uE E0 e_pd). rewrite (e_pd_val E0) by (rewrite U; lia). rewrite U. reflexivity.
  Qed.

  Lemma u_stklen : uE E0hw e_stklen = STK_HW_TOP - upd.
  Proof.
    pose proof usp_lo. pose proof usp_hi.
    pose proof u_pd0 as P. unfold e_stklen, esub, uE in *. rewrite mkAlu_denot, edenot_lit.
    rewrite u_sub64, u64_lit by (unfold STK_HW_TOP; lia). rewrite P. unfold upd, usp, STK_HW_TOP, two64 in *.
    rewrite Z.mod_small; lia.
  Qed.

  Lemma u_stk0_hw : uE E0hw (eaddz e_pd STK_OFF) = upd - 8388608.
  Proof.
    pose proof usp_lo. pose proof usp_hi.
    pose proof u_pd0 as P. unfold eaddz, uE in *. rewrite mkAlu_denot, edenot_lit.
    rewrite u_add64, u_lit64. rewrite P. unfold upd, usp, STK_OFF, two64 in *.
    rewrite Z.add_mod_idemp_r by lia. rewrite Z.mod_small; lia.
  Qed.

  Lemma u_stklen0 : uE E0hw e_stklen0 = STK_HW_TOP - usp.
  Proof.
    pose proof usp_lo. pose proof usp_hi.
    unfold e_stklen0, esub, uE. rewrite mkAlu_denot, edenot_lit. cbn [edenot].
    rewrite <- (edenot_agree' NX0 E0 E0hw e_sp0 E0hw_agree) by (vm_compute; reflexivity).
    rewrite edenot_e_sp0.
    rewrite u_sub64, u64_lit by (unfold STK_HW_TOP; lia). fold usp. unfold STK_HW_TOP, two64 in *.
    rewrite Z.mod_small; lia.
  Qed.

  Lemma u_stk0_hw0 : uE E0hw (eaddz e_sp0 STK_OFF) = usp - 8388608.
  Proof.
    pose proof u_stk0 as U. unfold uE in *.
    rewrite <- (edenot_agree' NX0 E0 E0hw _ E0hw_agree) by (vm_compute; reflexivity). exact U.
  Qed.

  Lemma allowA_init_hw : allowA A E0hw (init_acs_hw A) =
    [(pagedown (img_lo A), pageup (img_lo A + (img_hi A - img_lo A)));
     (pagedown (shadow_off A + img_lo A / 8), pageup (shadow_off A + (img_lo A + (img_hi A - img_lo A)) / 8));
     (pagedown (upd - 8388608), pageup (upd - 8388608 + (STK_HW_TOP - upd)));
     (pagedown (shadow_off A + (upd - 8388608) / 8), pageup (shadow_off A + (upd - 8388608 + (STK_HW_TOP - upd)) / 8));
     (pagedown (usp - 8388608), pageup (usp - 8388608 + (STK_HW_TOP - usp)));
     (pagedown (shadow_off A + (usp - 8388608) / 8), pageup (shadow_off A + (usp - 8388608 + (STK_HW_TOP - usp)) / 8))].
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    unfold allowA, init_acs_hw, init_vis_hw. cbn [a_vis a_ghost app flat_map allow1 fst snd].
    unfold sh_lo, sh_hi. cbn [fst snd]. rewrite !u_stk0_hw, !u_stklen, !u_stk0_hw0, !u_stklen0.
    unfold uE. rewrite !edenot_lit, !u64_lit by lia. reflexivity.
  Qed.

  Lemma abytes_init_hw : A_bytes (allowA A E0hw (init_acs_hw A)) <= vis_cost (img_hi A - img_lo A) + vis_cost STK_HW_HI + vis_cost STK_HW_HI0
                         /\ vis_cost (img_hi A - img_lo A) + vis_cost STK_HW_HI + vis_cost STK_HW_HI0 <= LIMIT.
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof (if_shadow _ _ _ IMG) as S1.
    pose proof usp_lo as HL1. pose proof usp_hi as HL2.
    rewrite allowA_init_hw. cbn [A_bytes fst snd]. unfold vis_cost, STK_HW_HI, STK_HW_HI0, STK_HW_TOP, LIMIT, target_alloc_limit.
    replace (img_lo A + (img_hi A - img_lo A)) with (img_hi A) by lia.
    replace (upd - 8388608 + (2 ^ 47 + 8388608 - upd)) with (2 ^ 47) by lia.
    assert (UPD : usp - 4095 <= upd <= usp /\ upd mod 4096 = 0).
    { unfold upd. lia. }
    assert (P1 : forall z, z mod 4096 = 0 -> pagedown z = z) by (intros z Hz; unfold pagedown; lia).
    assert (P2 : forall z, z mod 4096 = 0 -> pageup z = z) by (intros z Hz; unfold pageup; lia).
    rewrite (P1 (img_lo A) I3), (P2 (img_hi A) I4).
    pose proof (pageup_minus_pagedown (shadow_off A + img_lo A / 8) (shadow_off A + img_hi A / 8) ltac:(lia)).
    pose proof (pageup_minus_pagedown (upd - 8388608) (2 ^ 47) ltac:(lia)).
    pose proof (pageup_minus_pagedown (shadow_off A + (upd - 8388608) / 8) (shadow_off A + 2 ^ 47 / 8) ltac:(lia)).
    replace (usp - 8388608 + (2 ^ 47 + 8388608 - usp)) with (2 ^ 47) by lia.
    pose proof (pageup_minus_pagedown (usp - 8388608) (2 ^ 47) ltac:(lia)).
    pose proof (pageup_minus_pagedown (shadow_off A + (usp - 8388608) / 8) (shadow_off A + 2 ^ 47 / 8) ltac:(lia)).
    split; lia.
  Qed.

  Lemma init_kn_hw_ok : know_ok segs E0hw (Mr A argH0 E0hw (init_acs_hw A) model0 FULL0) (init_kn_hw A).
  Proof.
    pose proof auxv_count_RZ. pose proof RZ_range.
    rewrite (Mr0_indep E0hw E0 (init_acs_hw A) cs0). unfold init_kn_hw, know_ok.
    assert (Hb : AP.expr_vars_lt NX0 (fst e_auxb) = true) by (vm_compute; reflexivity).
    pose proof (edenot_agree' NX0 E0 E0hw _ E0hw_agree Hb) as Eb.
    apply Forall_app. split.
    - apply (auxw_reenv segs E0 E0hw _ 10 16 (ELit (bv_unsigned hw)) (EVar V_HW) E0hw_agree).
      + rewrite edenot_lit. unfold E0hw. cbn [edenot ev]. rewrite Z_to_bv_bv_unsigned. reflexivity.
      + apply auxw_ok; [lia | |];
          unfold AUXW, auxv_words, auxv_entries;
          cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
          rewrite ?edenot_lit, ?Z_to_bv_bv_unsigned; reflexivity.
    - apply Forall_app. split.
      + apply (know_ok_agree' segs NX0 E0 E0hw _ _ E0hw_agree (kn_vars_lt_init_kn A a_rseq_01)).
        exact init_kn_ok.
      + (* [auxv_vals_free]: the four a_val rows whose value is a free Section variable.  Each
           is proved at [E0] against [AUXW] by [auxv_val_ok] with the MODEL'S OWN TERM as a
           literal, then carried to [E0hw] by [kword_reenv] -- the same two-step AT_HWCAP uses
           just above, with [auxw_reenv] replaced by its single-entry form because only the
           a_val leg moves here (the a_type legs of 0, 9, 21 and 22 are already in
           [init_kn_with] as closed literals).  [vdso_text_pages (in_kernel inp)] is never
           reduced: [la_sysinfo_ehdr la] is written whole. *)
        apply Forall_app; split;
          [| apply (know_ok_agree' segs NX0 E0 E0hw _ _ E0hw_agree (auxv_rest_vars A)); exact auxv_rest_ok].
        unfold auxv_vals_free, know_ok.
        apply Forall_cons.
        { apply (kword_reenv segs E0 E0hw _ _ _ 8
                   (ELit (bv_unsigned (la_sysinfo_ehdr la))) (EVar V_VDSO) Eb).
          - rewrite edenot_lit. unfold E0hw, V_HW, V_VDSO, V_MSS, V_GID.
            cbn [edenot ev Nat.eqb]. rewrite Z_to_bv_bv_unsigned. reflexivity.
          - apply auxv_val_ok; [lia|].
            unfold AUXW, auxv_words, auxv_entries;
              cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul].
            rewrite edenot_lit, Z_to_bv_bv_unsigned. reflexivity. }
        apply Forall_cons.
        { apply (kword_reenv segs E0 E0hw _ _ _ 8
                   (ELit (bv_unsigned (la_minsigstksz la))) (EVar V_MSS) Eb).
          - rewrite edenot_lit. unfold E0hw, V_HW, V_VDSO, V_MSS, V_GID.
            cbn [edenot ev Nat.eqb]. rewrite Z_to_bv_bv_unsigned. reflexivity.
          - apply auxv_val_ok; [lia|].
            unfold AUXW, auxv_words, auxv_entries;
              cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul].
            rewrite edenot_lit, Z_to_bv_bv_unsigned. reflexivity. }
        apply Forall_cons.
        { apply (kword_reenv segs E0 E0hw _ _ _ 8
                   (ELit (bv_unsigned gid)) (EVar V_GID) Eb).
          - rewrite edenot_lit. unfold E0hw, V_HW, V_VDSO, V_MSS, V_GID.
            cbn [edenot ev Nat.eqb]. rewrite Z_to_bv_bv_unsigned. reflexivity.
          - apply auxv_val_ok; [lia|].
            unfold AUXW, auxv_words, auxv_entries;
              cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul].
            rewrite edenot_lit, Z_to_bv_bv_unsigned. reflexivity. }
        apply Forall_cons.
        { apply (kword_reenv segs E0 E0hw _ _ _ 8
                   (ELit (bv_unsigned gid)) (EVar V_GID) Eb).
          - rewrite edenot_lit. unfold E0hw, V_HW, V_VDSO, V_MSS, V_GID.
            cbn [edenot ev Nat.eqb]. rewrite Z_to_bv_bv_unsigned. reflexivity.
          - apply auxv_val_ok; [lia|].
            unfold AUXW, auxv_words, auxv_entries;
              cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul].
            rewrite edenot_lit, Z_to_bv_bv_unsigned. reflexivity. }
        apply Forall_nil.
  Qed.

  Theorem init_cs_ok_hw : cs_ok segs A LIMIT SINV0 argH0 fs E0hw (init_acs_hw A) R0 FULL0 model0.
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
    destruct abytes_init_hw as [AB1 AB2].
    constructor; cbn [init_acs_hw a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
      rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
    - apply (regs_ok_agree' NX0 E0 E0hw _ _ E0hw_agree sr_vars_lt_init_regs). exact init_regs_ok.
    - reflexivity.
    - exact init_kn_hw_ok.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - (* the reserved ledger: the image's intervals, then the launch's vDSO/vvar pair *)
      split; [|split].
      + pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
        pose proof (if_hull _ _ _ IMG) as (G1 & G2 & G3 & G4).
        pose proof (if_resx _ _ _ IMG) as [RX1 RX2]. pose proof resx_bytes_lo.
        exists RESX. split; [reflexivity|].
        split; [| split; [pose proof resx_len; lia | rewrite resx_sum; lia]].
        rewrite resx_eq. repeat constructor;
          cbn [fst snd];
          rewrite !u64_lit
            by (unfold mmap_base_min, mmap_base_max, sp_window_hi in *; lia);
          unfold KHI, mmap_base_min, mmap_base_max, sp_window_hi in *; lia.
      + constructor.
      + replace (m_kernel model0) with (in_kernel inp) by reflexivity.
        replace (vdso_top (m_vmmaps model0)) with VTOP
          by (symmetry; exact (vdso_top_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp)).
        apply incl_appr, incl_refl.
    - reflexivity.
    - reflexivity.
    - constructor.
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      exact (init_sp_ok_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp Hsp).
    - constructor.
    - constructor.
    - intros z Hz. exact Hz.
    - constructor.
    - constructor.
    - rewrite app_nil_r, sum_sizes_app, (if_sizes _ _ _ IMG), resx_sum.
      pose proof resx_bytes_lo. lia.
    - split; [|destruct Hsp as (_ & Hs2 & _); exact Hs2].
      unfold uE. rewrite <- (edenot_agree' NX0 E0 E0hw e_sp0 E0hw_agree) by (vm_compute; reflexivity).
      exact u_e_sp0.
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      unfold E0hw. cbn [ev V_HW V_VDSO V_MSS V_GID V_BRK Nat.eqb].
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7 & _). unfold uE in U7. cbn [edenot V_BRK] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.
    - lia.
    - lia.
    - exact AB1.
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
    - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
    - split; [| intros; reflexivity]. intros n Hn. unfold E0hw. cbn [ev].
      destruct (Nat.eqb n V_HW) eqn:E; [apply Nat.eqb_eq in E; unfold V_HW, NX0 in *; lia|].
      destruct (Nat.eqb n V_VDSO) eqn:E1; [apply Nat.eqb_eq in E1; unfold V_VDSO, NX0 in *; lia|].
      destruct (Nat.eqb n V_MSS) eqn:E2; [apply Nat.eqb_eq in E2; unfold V_MSS, NX0 in *; lia|].
      destruct (Nat.eqb n V_GID) eqn:E3; [apply Nat.eqb_eq in E3; unfold V_GID, NX0 in *; lia|].
      reflexivity.
    - (* the launch's reader: [init_model] copies [in_channel_reader inp], which [inp] sets *)
      reflexivity.
  Qed.
End Init.

(** an input of the shape the section's [inp] builds is that [inp]: the fields [inp] fixes are
    hypotheses here.  LPS 08b1429: [init_config] reads the file system only through [State.in_fs]
    (the image seeded with the declared /tmp entries), so [inp] takes the SEEDED image and no /tmp
    of its own; any declared /tmp is allowed. *)
Lemma init_config_inp : forall segs pc ph sp brk0 mbase rdraw lim inp0,
  in_abort_terminal inp0 = false -> in_va_size inp0 = Sv48 ->
  in_channel_reader inp0 = true -> in_sigpipe_terminal inp0 = false ->
  init_config segs pc ph sp brk0 mbase rdraw lim inp0
  = init_config segs pc ph sp brk0 mbase rdraw lim
      (@inp (in_argv inp0) (in_envp inp0) (in_fs inp0) (in_stdin inp0) (in_uid inp0) (in_gid inp0)
           (in_hwcap inp0) (in_groups inp0) (in_net inp0) (in_nofile inp0) (in_sigmask inp0) (in_urandom inp0)
           (in_kernel inp0) (in_execfn inp0) (in_sigpipe_default inp0)).
Proof.
  intros segs pc ph sp brk0 mbase rdraw lim inp0 Hab Hva Hcr Hst.
  destruct inp0 as [av ev ifs si u g gs n nf sm hw ab va ur tmp kb xf cr sd st].
  cbn [in_abort_terminal in_va_size in_channel_reader in_sigpipe_terminal] in *.
  subst. reflexivity.
Qed.

