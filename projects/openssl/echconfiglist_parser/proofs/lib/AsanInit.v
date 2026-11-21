(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (Init takes the whole ProcInput with the launch and channel-reader premises; the stack image is Linux's whole block, auxv 27 or 29 pairs by CONFIG_RSEQ; the ledger holds the vDSO/vvar pair; a narrower zero window below sp; init_cs_ok over init_kn_r); and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); no ghost range at the launch (co_gres); internal commit ids in comments replaced by public commits or removed. *)
(* Ported to LPS 08b1429: the entry stack image is Linux's whole block (strings at the
   top, the AT_RANDOM bytes and the [arch_align_stack] pad below them, a 27- or 29-pair
   auxv by CONFIG_RSEQ), the launch reserves the vDSO/vvar pair, and the Section takes
   the run's whole [ProcInput]. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
(* Vdso added: :461's vdso_run_init is Vdso's, written unqualified here.  Require is
   transitive for LOADING but Import is not, so the module was loaded and the name was
   not in scope - "The reference vdso_run_init was not found in the current environment".
   Control: four files in this tree write it unqualified and the other three all list
   Vdso on this line - RefStartup.v:13-14, Amb.v:5, DivergeSim.v:9-10, ExitSim.v:9 - and
   this was the only one that did not.  Added inside the existing require block, above
   every Open Scope, so no scope is reopened over the file's numerals. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Vdso.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim StepTac ShapeAlg AgentLib StartupAux RefLayout ArgvEnv AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan AsanPlanSound.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AsanCeil.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* this file reasons about / and mod throughout *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition LIMIT : Z := target_alloc_limit.

(** the per-image facts the initial state needs *)
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
  (** the table's bounds on what the LAUNCH reserves beside the image: the vDSO pair,
      two intervals of at most twenty pages ([State.vdso_len_bounds]) *)
  if_resx  : (2 <= n_resx A)%nat /\ (20 <= p_resx A)%nat
}.

(** the EXACT size of the initial stack image: Linux's block runs from the entry stack
    pointer to the stack VMA's end ([PropExec.length_entry_stack_image_launch]) *)
Definition stack_image_size (sp top : word) : Z :=
  (bv_unsigned top - bv_unsigned sp)%Z.

(** the string area holds argv[0] and its NUL, and at least the exec name's NUL *)
Lemma launch_strings_argv0 : forall (av ev : list (list byte)) (ex : list byte), (0 < length av)%nat ->
  (length (nth 0 av []) + 2 <= launch_string_bytes av ev ex)%nat.
Proof.
  intros [|a t] ev ex H; [cbn in H; lia|].
  unfold launch_string_bytes. cbn [flatten_strings flat_map nth]. rewrite !length_app. cbn [length]. lia.
Qed.

(** expressions over the variables below [b] denote alike under valuations that agree there *)
Fixpoint nb_lt0 (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => Nat.ltb n b
  | EAlu _ a c | EAluw _ a c | EMd _ a c | EMdw _ a c => nb_lt0 b a && nb_lt0 b c
  | EExt _ _ _ a => nb_lt0 b a
  | EBlob _ _ _ _ => false
  end.

Lemma edenot_ev_agree0 : forall b E E' e,
  nb_lt0 b e = true -> (forall n, (n < b)%nat -> ev E n = ev E' n) -> edenot E e = edenot E' e.
Proof.
  intros b E E' e. induction e; cbn [nb_lt0 edenot]; intros H Hag; try reflexivity;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1 Hag), (IHe2 H2 Hag); reflexivity).
  - apply Hag. apply Nat.ltb_lt. exact H.
  - rewrite (IHe H Hag). reflexivity.
  - discriminate.
Qed.

(** LPS 727298f3: the vector above pair 25, per build ([StackLayout.auxv_entries]).  With
    CONFIG_RSEQ, pairs 26 and 27 are AT_RSEQ_FEATURE_SIZE (27) -> 28 and AT_RSEQ_ALIGN (28) ->
    32 and pair 28 is AT_NULL; without it pair 26 is AT_NULL (boost-beast/http_request's
    As/AsanInit.v, the same lemmas) *)
Lemma auxv_words_rseq_on : forall la ph entry uid gid hw ar ae,
  la_rseq la = true ->
  nth 52 (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 27
  /\ nth 53 (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 28
  /\ nth 54 (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 28
  /\ nth 55 (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 32
  /\ nth 56 (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0
  /\ nth 57 (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof.
  intros [ehdr c msz [|]] ph entry uid gid hw ar ae Hr; cbn in Hr; [|discriminate Hr].
  repeat split; reflexivity.
Qed.

Lemma auxv_words_rseq_off : forall la ph entry uid gid hw ar ae,
  la_rseq la = false ->
  nth 52 (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0
  /\ nth 53 (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof.
  intros [ehdr c msz [|]] ph entry uid gid hw ar ae Hr; cbn in Hr; [discriminate Hr|].
  split; reflexivity.
Qed.

(** AT_GID and AT_EGID, pairs 21 and 22 (value words 43 and 45), carry ONE value: the model's
    [StackLayout.auxv_entries] lists [(AT_GID, gid); (AT_EGID, gid)] for its one [gid] argument,
    which [Run.entry_stack_image] fills with the launch's [in_gid] *)
Lemma auxv_words_gid : forall la ph entry uid gid hw ar ae,
  nth 43 (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = gid
  /\ nth 45 (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = gid.
Proof. intros [ehdr c msz [|]] ph entry uid gid hw ar ae; split; reflexivity. Qed.

(** LPS c0dd863a: AT_SYSINFO_EHDR, pair 0 (value word 1), is the launch's [la_sysinfo_ehdr]
    ([Run.launch_auxv]: the vDSO text base) *)
Lemma auxv_words_sysinfo : forall la ph entry uid gid hw ar ae,
  nth 1 (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = la_sysinfo_ehdr la.
Proof. intros [ehdr c msz [|]] ph entry uid gid hw ar ae; reflexivity. Qed.

Lemma rseq_z_true : forall b, rseq_z b = 1 -> b = true.
Proof. intros [|] H; [reflexivity | discriminate H]. Qed.

Lemma rseq_z_false : forall b, rseq_z b <> 1 -> b = false.
Proof. intros [|] H; [exfalso; apply H; reflexivity | reflexivity]. Qed.

(** the vector's word count, 54 or 58, as a bound in [rseq_z] *)
Lemma auxv_count_lt : forall b (j : nat), Z.of_nat j < 54 + 4 * rseq_z b -> (j < 2 * auxv_count b)%nat.
Proof. intros [|] j H; cbn in *; lia. Qed.

Section Init.
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  (** the image's ELF entry: [Run.init_config]'s pc and the auxv's AT_ENTRY *)
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* the entry draw [Run.en_draw]; ed_random = the AT_RANDOM bytes, ed_top = the stack VMA's end *)
  Variable brk0 mbase : word.
  (** the run's whole input, every field of it as the published statements quantify it *)
  Variable inp : ProcInput.

  Let argv : list (list byte) := in_argv inp.
  Let envp : list (list byte) := in_envp inp.
  Let uid : word := in_uid inp.
  Let hw : word := in_hwcap inp.
  Let execfn : list byte := in_execfn inp.
  Let kb : KernelBuild := in_kernel inp.
  (** CONFIG_RSEQ of the run's kernel build: the auxv is 27 or 29 pairs; NOT fixed *)
  Let rseq : bool := kb_rseq kb.
  Let R : Z := rseq_z rseq.

  Hypothesis IMG : img_facts segs A ph.
  Hypothesis Hapc : Z.of_N apc = a_entry A.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  (** [Run.valid_entry]'s fourth conjunct *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  (** [Run.valid_input]'s [valid_creds], uid half, and its hwcap clause *)
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  (** [Run.valid_input]'s launch clause: a name [execve] admits, under E2BIG *)
  Hypothesis Hlaunch : valid_launch inp.
  (** [Run.valid_entry]'s FIFTH conjunct: the start state is exactly a Linux launch *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  (** 08b1429: [Run.valid_input]'s reader clause. [State.init_model] copies
      [in_channel_reader] into the process state, and no step writes it again, so this is
      where [cs_ok]'s [co_rdr] is seeded ([ReadWrite.write_spec]'s channel arm reads it) *)
  Hypothesis Hrdrin : in_channel_reader inp = true.

  Let entryw : word := Z_to_bv 64 (Z.of_N apc).
  Let la : LaunchAuxv := launch_auxv inp sp mbase.
  Let top : word := ed_top rdraw.

  Lemma inp_argv : in_argv inp = argv.        Proof. reflexivity. Qed.
  Lemma inp_envp : in_envp inp = envp.        Proof. reflexivity. Qed.
  Lemma inp_execfn : in_execfn inp = execfn.  Proof. reflexivity. Qed.
  Lemma inp_rseq : kb_rseq (in_kernel inp) = rseq. Proof. reflexivity. Qed.
  Lemma la_rseq_eq : la_rseq la = rseq.       Proof. reflexivity. Qed.
  Lemma R_range : 0 <= R <= 1.                Proof. apply rseq_z_range. Qed.

  Let bsb := entry_stack_image inp mbase ph entryw sp rdraw.   (* the mapped image IS Linux's block: sp .. ed_top *)
  Let usp := bv_unsigned sp.
  Let utop := bv_unsigned top.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let L0 := Z.of_nat (length (nth 0 argv [])).
  Let L1 := Z.of_nat (length (nth 1 argv [])).
  (** [StackLayout.block_items mod 2]: [STACK_ROUND]'s 8-byte gap, in words *)
  Let G := Z.of_nat (block_items argv envp mod 2).
  (** C, sp to the top of the AT_RANDOM bytes *)
  Let CHEAD := Z.of_nat (block_head_size rseq argv envp).
  (** L, the string bytes with their NULs, the exec file name included *)
  Let LSTR := Z.of_nat (launch_string_bytes argv envp execfn).
  (** the [arch_align_stack] pad between the AT_RANDOM bytes and argv[0] *)
  Let W := Z.of_nat (block_pad_len rseq sp top argv envp execfn).
  (** argv[0]'s first byte *)
  Let STR0 := usp + CHEAD + W.

  (** LPS 727298f3: the fourteenth word is [V_GID], the launch's gid ([AsanPlanCore.V_GID]);
      LPS c0dd863a: the fifteenth is [V_EHDR], AT_SYSINFO_EHDR = the text base of the vDSO pair
      the launch places at this base ([Run.vdso_text_base], [AsanPlanCore.V_EHDR]) *)
  Definition vals0 : list word :=
    [Z_to_bv 64 (usp / 32768); Z_to_bv 64 argc; Z_to_bv 64 envc; Z_to_bv 64 L0; Z_to_bv 64 W;
     Z_to_bv 64 (bv_unsigned brk0 / 4096); Z_to_bv 64 ((usp mod 32768) / 4096); Z_to_bv 64 L1; uid; hw;
     Z_to_bv 64 ((usp mod 4096) / 16); Z_to_bv 64 G; Z_to_bv 64 R; in_gid inp;
     vdso_text_base (in_kernel inp) sp mbase].
  (** the initial valuation: the fifteen words, and byte string [K_RND] = the AT_RANDOM draw *)
  Definition E0 : env := Env (fun n => nth n vals0 (Z_to_bv 64 0))
                             (fun k => if Nat.eqb k K_RND then at_random_bytes (ed_random rdraw) else []).

  (** hidden argument bytes: the envp pointer array (with its NULL) and the string area, which is at the TOP of
      the block — argv[0] at [STR0], up to the stack VMA's end *)
  Definition argB0 (a : word) : bool :=
    let z := bv_unsigned a in
    (((usp + 8 * argc + 16 <=? z) && (z <? usp + 8 * argc + 8 * envc + 24))
     || ((STR0 <=? z) && (z <? utop)))%bool.
  (** ... and above the valuation's own stack pointer, which keeps the hidden set
      inside the stack side for every valuation that agrees on the initial variables *)
  Definition argH0 (E : env) (a : word) : bool :=
    (argB0 a && (uE E e_sp0_early <=? bv_unsigned a))%bool.

  (** LPS c0dd863a: the launch variables below [V_EHDR]; [V_EHDR] reads the run's mmap base,
      which [AsanInitL.SINV0L] binds existentially, and [APS.cs_ok]'s [co_ehdr] ties it instead *)
  Definition SINV0 (E : env) (M : word -> option byte) : Prop :=
    (forall n, (n < V_EHDR)%nat -> ev E n = ev E0 n)
    /\ (forall a, argH0 E a = true -> M a = wrap_mem inp mbase ph entryw sp rdraw a).

  (* ----------------------------------------------------------------------- *)
  (** ** Layout arithmetic                                                    *)
  (* ----------------------------------------------------------------------- *)

  Lemma Hlo' : (sp_window_lo <= bv_unsigned sp)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hhi' : (bv_unsigned sp <= sp_window_hi)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hal' : (bv_unsigned sp mod 16 = 0)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hav0 : (0 < length argv)%nat. Proof. destruct Hva as [[? ?] _]; lia. Qed.

  (** instantiate the hypotheses a [RefLayout]/[PropExec] lemma's Section discharged *)
  Ltac inst_hyps H :=
    repeat match type of H with
           | ?P -> _ =>
               let Hp := fresh "Hp" in
               assert (Hp : P) by first [ assumption | exact Hlo' | exact Hhi' | exact Hlaunch | exact Hlau
                                        | exact Hva | exact Hve ];
               specialize (H Hp); clear Hp
           end.

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

  (** C = 8*items + (432 + 32*rseq) + 8*g + 16, with items = argc + envc + 3 *)
  Lemma chead_eq : CHEAD = 8 * argc + 8 * envc + 472 + 32 * R + 8 * G.
  Proof.
    pose proof (auxv_size_rseq rseq) as HA. fold R in HA.
    unfold CHEAD, G, argc, envc, block_head_size, block_items. lia.
  Qed.

  (* OLD: 504 <= CHEAD <= 10752.  NEW: 480 <= CHEAD <= 10752.
     chead_eq gives CHEAD = 8*argc + 8*envc + 472 + 32*R + 8*G, and the four bounds
     feeding it are tight: len_av 1 <= argc, len_ev 0 <= envc, R_range 0 <= R, gap_range
     0 <= G, so the least value is 8 + 0 + 472 + 0 + 0 = 480 and 504 is FALSE, which is
     why lia answers "Cannot find witness".  The upper bound is unchanged and already
     agrees with the 472 constant (1024*8 + 256*8 + 472 + 32 + 8 = 10752), so the 472
     update landed here and the lower bound was left behind.  480 holds for BOTH kernel
     builds: rseq free, R in {0,1}, and the bound does not mention R. *)
  Lemma chead_range : 480 <= CHEAD <= 10752.
  Proof. pose proof chead_eq. pose proof len_av. pose proof len_ev. pose proof gap_range. pose proof R_range. lia. Qed.

  Lemma s0_in_strings : L0 + 2 <= LSTR.
  Proof. unfold LSTR, L0. pose proof (launch_strings_argv0 argv envp execfn Hav0). lia. Qed.

  Lemma lstr_lo : 2 <= LSTR.
  Proof. pose proof s0_in_strings. unfold L0 in *. lia. Qed.

  (** [Run.valid_launch]'s E2BIG half, in this file's names *)
  Lemma lstr_hi : LSTR + 8 * argc + 8 * envc <= 2097152.
  Proof.
    destruct Hlaunch as [_ Hb]. unfold launch_bytes, e2big_limit in Hb.
    rewrite inp_argv, inp_envp, inp_execfn in Hb. unfold LSTR, argc, envc. lia.
  Qed.

  (** The pad [arch_align_stack] left: [r] (0..4095) plus the low-four-bit remainder *)
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

  (* OLD: 8 * argc + 8 * envc + 506 <= Z.of_nat (length bsb).
     NEW: ... + 482 <= ... .  length_bsb_sum (:253) gives length bsb = CHEAD + W + LSTR + 8,
     and the four bounds under it are tight: chead_eq's CHEAD = 8*argc + 8*envc + 472 +
     32*R + 8*G with R_range and gap_range each 0 at the low end, pad_range (:252)
     0 <= W, and lstr_lo 2 <= LSTR.  So the least value is 472 + 0 + 2 + 8 = 482 above
     8*argc + 8*envc, and 506 is FALSE - which is why lia answers "Cannot find witness".
     506 - 482 = 24, the SAME offset by which chead_range's lower bound was stale
     (504 -> 480): one constant moved and left two derived bounds behind.
     Free kernel fields: the bound mentions none and holds for both values of kb_rseq. *)
  Lemma bsb_ge : 8 * argc + 8 * envc + 482 <= Z.of_nat (length bsb).
  Proof.
    pose proof length_bsb_sum. pose proof chead_eq. pose proof lstr_lo. pose proof pad_range.
    pose proof gap_range. pose proof R_range. lia.
  Qed.

  Lemma str0_hi : STR0 + LSTR + 8 = utop.
  Proof. unfold STR0. pose proof pad_eq. lia. Qed.

  (* ----------------------------------------------------------------------- *)
  (** ** Denotations under [E0]                                               *)
  (* ----------------------------------------------------------------------- *)

  Lemma brk_range : img_hi A <= bv_unsigned brk0 <= img_hi A + BRK_ASLR /\ bv_unsigned brk0 mod 4096 = 0.
  Proof.
    destruct Hbrk as (H1 & H2 & H3). unfold brk_aslr_max in H2. unfold page_size in H3.
    rewrite (if_top _ _ _ IMG) in H1, H2. unfold BRK_ASLR. lia.
  Qed.

  Lemma usp_hi : usp + 192 <= 2 ^ 47.
  Proof. pose proof usp_fit. pose proof bsb_ge. pose proof len_av. pose proof len_ev. lia. Qed.

  (** the values of the initial variables, as Z *)
  Lemma uE0 :
    uE E0 (EVar V_S1) = usp / 32768 /\ uE E0 (EVar V_S2) = (usp mod 32768) / 4096
    /\ uE E0 (EVar V_ARGC) = argc /\ uE E0 (EVar V_ENVC) = envc /\ uE E0 (EVar V_L0) = L0
    /\ uE E0 (EVar V_W) = W /\ uE E0 (EVar V_BRK) = bv_unsigned brk0 / 4096
    /\ uE E0 (EVar V_G) = G /\ uE E0 (EVar V_R) = R.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof gap_range. pose proof R_range.
    pose proof (u64_range brk0) as [B1 B2].
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    unfold uE. cbn [edenot E0 ev nth vals0 V_S1 V_S2 V_ARGC V_ENVC V_L0 V_W V_BRK V_G V_R].
    rewrite !u64_lit by lia. repeat split; reflexivity.
  Qed.

  Lemma uE0_S3 : uE E0 (EVar V_S3) = (usp mod 4096) / 16.
  Proof.
    pose proof usp_lo. pose proof usp_hi.
    unfold uE. cbn [edenot E0 ev nth vals0 V_S3]. rewrite u64_lit by lia. reflexivity.
  Qed.

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

  Lemma u_e_pg : uE E0 e_pg = pagedown usp.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _).
    unfold e_pg, eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2. unfold pagedown.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma pagedown_usp : usp - 4080 <= pagedown usp <= usp /\ 0x7fff80000000 <= pagedown usp /\ pagedown usp mod 4096 = 0
                       /\ usp = pagedown usp + 16 * ((usp mod 4096) / 16).
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. unfold pagedown.
    lia.
  Qed.

  Lemma u_e_sp0 : uE E0 e_sp0 = usp.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. pose proof uE0_S3 as U3. pose proof u_e_pg as UP.
    pose proof pagedown_usp as (P1 & P2 & P3 & P4).
    unfold e_sp0, eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite UP, U3.
    rewrite (Z.mod_small (16 * _)) by lia. rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma edenot_e_sp0 : edenot E0 e_sp0 = sp.
  Proof. apply bv_eq. exact u_e_sp0. Qed.

  Lemma u_sp8 : uE E0 e_sp8 = usp / 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _). pose proof uE0_S3 as U3.
    unfold e_sp8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2, U3.
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

  (** the auxv's size, the plan's one symbolic offset *)
  Lemma u_e_auxsz : uE E0 e_auxsz = 432 + 32 * R.
  Proof.
    pose proof R_range. destruct uE0 as (_ & _ & _ & _ & _ & _ & _ & _ & U9).
    unfold e_auxsz, eaddz, escale, uE in *. rewrite mkAlu_denot, mkMd_denot, !edenot_lit.
    rewrite u_add64, u_mul64, !u64_lit by lia. rewrite U9. rewrite !Z.mod_small by lia. lia.
  Qed.

  (** the AT_RANDOM bytes sit [C - 16] above sp *)
  Lemma u_e_atrandom : uE E0 e_atrandom = usp + CHEAD - 16.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof R_range.
    pose proof gap_range. pose proof chead_eq. pose proof bsb_ge. pose proof length_bsb_sum. pose proof lstr_lo. pose proof pad_range.
    destruct uE0 as (_ & _ & _ & _ & _ & _ & _ & U8 & _).
    pose proof u_e_auxv as UA. pose proof u_e_auxsz as UZ. unfold e_atrandom, eadd, escale, uE in *.
    rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UA, UZ, U8. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_str0 : uE E0 e_str0 = STR0.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof R_range.
    pose proof pad_range. pose proof chead_eq. pose proof gap_range. pose proof bsb_ge. pose proof length_bsb_sum. pose proof lstr_lo.
    destruct uE0 as (_ & _ & _ & _ & _ & U6 & _).
    pose proof u_e_atrandom as UA. unfold e_str0, eadd, eaddz, uE, STR0 in *.
    rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite UA, U6. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_str1 : uE E0 e_str1 = STR0 + L0 + 1.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof chead_eq. pose proof gap_range. pose proof bsb_ge. pose proof R_range.
    pose proof length_bsb_sum. pose proof lstr_hi. pose proof s0_in_strings.
    destruct uE0 as (_ & _ & _ & _ & U5 & _).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    pose proof u_e_str0 as US. unfold e_str1, eadd, eaddz, uE, STR0 in *. rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite US, U5. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_atr8 : uE E0 e_atr8 = usp / 8 + argc + envc + 4 * R + G.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof gap_range. pose proof R_range.
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9). pose proof u_sp8 as US.
    unfold e_atr8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia.
    rewrite US, U3, U4, U8, U9. rewrite !Z.mod_small by lia. lia.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (** ** The initial configuration                                             *)
  (* ----------------------------------------------------------------------- *)

  Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.
  Definition FULL0 : word -> option byte := wrap_mem inp mbase ph entryw sp rdraw.
  (** [Run.init_config]'s model: [State.init_model] at the run stack pointer, with the
      launch's vDSO draw copied in by [State.with_vdso] *)
  Definition model0 : Model :=
    with_vdso (vdso_run_init (ed_vdso rdraw))
      (init_model (segments_reserved segs) brk0 mbase sp LIMIT inp).

  (** LPS 727298f3: the start state of the run's own build ([AsanPlanCore.init_acs_r]) *)
  Let cs0 := init_acs_r R A.
  Let hid0 := hid A argH0 E0 cs0 model0.
  Let Mr0 := Mr A argH0 E0 cs0 model0 FULL0.

  (** THE LAUNCH'S RESERVED LEDGER is the image's reservations AND the vDSO pair
      ([State.init_reserved]), placed at [State.vdso_top] of the initial ledger *)
  Let VTOP : Z :=
    page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)).
  Let RESX : list (word * word) := vdso_reserved kb VTOP.

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

  Lemma vtop_range : mmap_base_min - 4095 <= VTOP <= bv_unsigned mbase
                     /\ VTOP mod 4096 = 0.
  Proof.
    pose proof mb_range as ((Y1 & Y2) & Y3). pose proof usp_lo.
    unfold VTOP, page_round_down_Z, page_size, stack_max_size,
           mmap_base_min, mmap_base_max, sp_window_hi, usp in *.
    split; [split|]; lia.
  Qed.

  (** the pair, for ANY kernel build: four vvar pages, then one to sixteen text pages *)
  Lemma resx_shape :
    RESX = [(Z_to_bv 64 (VTOP - vdso_len kb), Z_to_bv 64 (vdso_vvar_pages * page_size));
            (Z_to_bv 64 (VTOP - vdso_len kb + vdso_vvar_pages * page_size),
             Z_to_bv 64 (vdso_text_pages kb * page_size))].
  Proof.
    pose proof vtop_range as [[T1 T2] T3]. pose proof (vdso_len_bounds kb).
    unfold RESX, vdso_reserved. cbv zeta.
    replace (VTOP - vdso_len kb <? page_size) with false
      by (symmetry; apply Z.ltb_ge; unfold page_size, mmap_base_min in *; lia).
    reflexivity.
  Qed.

  Lemma resx_len : (length RESX <= 2)%nat.
  Proof. rewrite resx_shape. cbn [length]. lia. Qed.

  Lemma resx_sum : sum_sizes RESX = vdso_len kb.
  Proof.
    pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
    pose proof (vdso_text_pages_pos kb). pose proof (vdso_text_pages_le kb).
    rewrite resx_shape. cbn [sum_sizes fst snd].
    unfold vdso_len, vdso_vvar_pages, page_size in *.
    rewrite !u64_lit by lia. lia.
  Qed.

  Lemma resx_bytes_lo : 81920 <= resx_bytes A.
  Proof.
    pose proof (if_resx _ _ _ IMG) as [RX1 RX2]. unfold resx_bytes. lia.
  Qed.

  Lemma resx_ok : Forall (resx_entry_ok A) RESX.
  Proof.
    pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
    pose proof (if_hull _ _ _ IMG) as (G1 & G2 & G3 & G4).
    pose proof (vdso_text_pages_pos kb). pose proof (vdso_text_pages_le kb).
    rewrite resx_shape. unfold resx_entry_ok, vdso_len, vdso_vvar_pages, page_size in *.
    repeat constructor; cbn [fst snd];
      rewrite !u64_lit by (unfold mmap_base_min, mmap_base_max, sp_window_hi in *; lia);
      unfold KHI, mmap_base_min, mmap_base_max, sp_window_hi in *; lia.
  Qed.

  (** the initial ceiling: the launch's alloc_top is sp - 8 MiB *)
  Lemma TOP0 : TOP model0 = usp - 8388608.
  Proof.
    unfold TOP. change (alloc_top (m_vmmaps model0)) with (bv_unsigned sp - stack_max_size).
    unfold stack_max_size, usp. lia.
  Qed.

  Lemma hid0_eq : forall a : word, hid0 a = (argH0 E0 a || negb (APS.in_hull A (bv_unsigned a) || (usp - 8388608 <=? bv_unsigned a)))%bool.
  Proof.
    intros a. unfold hid0, hid, vis. rewrite TOP0. destruct model0_facts as (_&_&_&_&Hm&Hn&Hl&_). rewrite Hm. cbn [in_ivs existsb andb].
    rewrite orb_false_r. reflexivity.
  Qed.

  Lemma Mr0_visible : forall a : word, usp - 8388608 <= bv_unsigned a -> argH0 E0 a = false -> Mr0 a = FULL0 a.
  Proof.
    intros a Hc Ha. unfold Mr0, Mr, mrestrict. fold hid0. rewrite hid0_eq, Ha.
    replace (usp - 8388608 <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; exact Hc). rewrite orb_true_r. reflexivity.
  Qed.

  (** 6144513 is [StoreOk.stack_window_depth]: what the 8 MiB leaves below [sp] for
      the largest entry image [StoreOk.stack_window_reach] bounds *)
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

  (** reading visible words of the argument block through [Mr0] = through the raw stack image *)
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

  (* ----------------------------------------------------------------------- *)
  (** ** The four AsanPlanSound hypotheses about SINV/argH                    *)
  (* ----------------------------------------------------------------------- *)

  Lemma argB0_high : forall a, argB0 a = true -> usp <= bv_unsigned a.
  Proof.
    intros a H. unfold argB0 in H. pose proof len_av. pose proof len_ev.
    pose proof chead_range. pose proof pad_range.
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H _]; apply Z.leb_le in H; unfold STR0 in H; lia.
  Qed.

  Lemma argH0_high : forall E a, argH0 E a = true -> CEIL <= bv_unsigned a.
  Proof.
    intros E a H. unfold argH0 in H. apply andb_prop in H as [H _]. apply argB0_high in H.
    destruct Hsp as [Hlo _]. unfold sp_window_lo in Hlo. unfold CEIL. unfold usp in H. lia.
  Qed.

  Lemma argH0_sp0 : forall E a, argH0 E a = true -> bv_unsigned (edenot E e_sp0_early) <= bv_unsigned a.
  Proof. intros E a H. unfold argH0 in H. apply andb_prop in H as [_ H]. apply Z.leb_le in H. unfold uE in H. exact H. Qed.

  Lemma E_SP0 : AP.expr_vars_lt NX0 e_sp0_early = true.
  Proof. reflexivity. Qed.

  Lemma argH0_agree : forall E E' a, env_agree NX0 E E' -> argH0 E a = argH0 E' a.
  Proof. intros E E' a Hag. unfold argH0, uE. rewrite (edenot_agree NX0 E E' e_sp0_early Hag E_SP0). reflexivity. Qed.

  Lemma SINV0_frame : forall E M M', (forall a, argH0 E a = true -> M' a = M a) -> SINV0 E M -> SINV0 E M'.
  Proof. intros E M M' Hf [H1 H2]. split; [exact H1|]. intros a Ha. rewrite (Hf a Ha). apply H2. exact Ha. Qed.

  Lemma SINV0_agree : forall E E' M, env_agree NX0 E E' -> SINV0 E M -> SINV0 E' M.
  Proof.
    intros E E' M Hag [H1 H2]. split.
    - intros n Hn. rewrite <- (proj1 Hag n) by (unfold NX0, V_EHDR in *; lia). apply H1. exact Hn.
    - intros a Ha. apply H2. rewrite (argH0_agree E E' a Hag). exact Ha.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (** ** The knowledge [init_kn A] holds                                       *)
  (* ----------------------------------------------------------------------- *)

  Lemma argH0_E0 : forall a : word, argH0 E0 a = argB0 a.
  Proof.
    intros a. unfold argH0. destruct (argB0 a) eqn:Hb; [|reflexivity]. cbn [andb].
    apply Z.leb_le. rewrite e_sp0_early_eq, u_e_sp0. apply argB0_high. exact Hb.
  Qed.

  Lemma argH0_ev0 : forall E a, (forall n, (n < V_EHDR)%nat -> ev E n = ev E0 n) -> argH0 E a = argB0 a.
  Proof.
    intros E a Hev. rewrite <- argH0_E0. unfold argH0, uE, e_sp0_early.
    cbn [edenot]. rewrite (Hev 0%nat) by (unfold V_EHDR; lia). rewrite (Hev 6%nat) by (unfold V_EHDR; lia).
    rewrite (Hev 10%nat) by (unfold V_EHDR; lia).
    reflexivity.
  Qed.

  Lemma argH0_SINV0 : forall E M a, SINV0 E M -> argH0 E a = argB0 a.
  Proof. intros E M a [Hev _]. apply argH0_ev0. exact Hev. Qed.

  Lemma argH0_range : forall a : word, argH0 E0 a = true ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 8 * envc + 24
    \/ STR0 <= bv_unsigned a < utop.
  Proof.
    intros a H. rewrite argH0_E0 in H. unfold argB0 in H.
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; [left|right]; lia.
  Qed.

  (** the VISIBLE part of the block: argc, the argv pointers and their NULL, the auxv, the gap, the sixteen random
      bytes and the [arch_align_stack] pad — everything between the envp NULL and argv[0] *)
  Lemma not_argH0 : forall a : word,
    (bv_unsigned a < usp + 8 * argc + 16 \/ (usp + 8 * argc + 8 * envc + 24 <= bv_unsigned a < STR0)
     \/ utop <= bv_unsigned a) -> argH0 E0 a = false.
  Proof.
    intros a H. destruct (argH0 E0 a) eqn:Ha; [|reflexivity]. apply argH0_range in Ha.
    pose proof len_av. pose proof len_ev. pose proof chead_eq. pose proof pad_range. pose proof R_range.
    pose proof gap_range. pose proof str0_hi. pose proof lstr_lo. unfold STR0 in *. lia.
  Qed.

  (** every hidden byte is a byte of the image, so it is present *)
  Lemma hidden_present : forall E M a, SINV0 E M -> argH0 E a = true -> exists b, M a = Some b.
  Proof.
    intros E M a HS Ha. pose proof HS as [_ HM].
    rewrite (HM a Ha). rewrite (argH0_SINV0 E M a HS), <- argH0_E0 in Ha.
    pose proof (argH0_range a Ha) as Hr.
    pose proof len_av. pose proof len_ev. pose proof chead_eq. pose proof pad_range. pose proof R_range.
    pose proof gap_range. pose proof str0_hi. pose proof lstr_lo. pose proof length_bsb_sum. pose proof usp_fit.
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw) by (unfold STR0, usp in *; lia). fold bsb.
    unfold stack_to_mem. replace (bv_unsigned sp <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; unfold STR0, usp in *; lia).
    cbv zeta. replace (bv_unsigned a - bv_unsigned sp <? Z.of_nat (length bsb)) with true
      by (symmetry; apply Z.ltb_lt; unfold STR0, usp, utop in *; lia).
    destruct (nth_error bsb (Z.to_nat (bv_unsigned a - bv_unsigned sp))) as [b|] eqn:Hn; [exists b; reflexivity|].
    apply nth_error_None in Hn. unfold STR0, usp, utop in *. lia.
  Qed.

  (** a KWord fact about a visible 8-byte word of the argument block read through the raw image *)
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

  (** [stack_to_mem] is total on its own range, straight from its body:
      75d69e00:theories/LinuxProcessSem/StackLayout.v:615-623 answers
      [nth_error bytes (Z.to_nat off)] exactly when [base <= addr] and [off < |bytes|].
      NO ROM FALLBACK ANYWHERE IN IT - which is why this route is sound where an [rdn]
      one is not: [rdn] reads through [rd1], whose fallback is the segment ROM. *)
  Lemma stack_to_mem_defined : forall (b : word) bs (a : word),
    bv_unsigned b <= bv_unsigned a ->
    bv_unsigned a - bv_unsigned b < Z.of_nat (length bs) ->
    stack_to_mem b bs a <> None.
  Proof.
    intros b bs a Hlo Hhi. unfold stack_to_mem.
    rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi).
    apply nth_error_Some. lia.
  Qed.

  (** [kword_stack]'s hypotheses with a [KUnk] conclusion, phrased over [stack_to_mem] and
      NEVER over [rdn].  Ported unchanged from punycode's Common/AsanInit.v after reading
      THIS tree's [kentry_ok] arms at AxSymExec3Sound.v:658-681 and finding them
      character-identical - three components, [KWord] over [rdn], [KUnk] over the base map
      with no fallback.  Assuming the twins agreed is what produced the false
      [kunk_of_word]; the agreement is a measurement here, not an assumption. *)
  Lemma kunk_stack : forall b k (w : word),
    bv_unsigned (edenot E0 b) + k = bv_unsigned w ->
    usp <= bv_unsigned w -> bv_unsigned w + 8 <= usp + Z.of_nat (length bsb) ->
    (forall x : word, bv_unsigned w <= bv_unsigned x < bv_unsigned w + 8 -> argH0 E0 x = false) ->
    kentry_ok segs E0 Mr0 (KUnk (SA b k) (ELit 8)).
  Proof.
    intros b k w Hw Hlo Hhi Hvis. pose proof usp_fit. pose proof usp_lo. pose proof (u64_range w).
    cbn [kentry_ok]. split.
    - unfold flat, estart. cbn [a_base a_off]. rewrite elenZ_lit by lia. lia.
    - intros i Hi. rewrite elenZ_lit in Hi by lia.
      assert (Ha : bv_unsigned w <= bv_unsigned (Z_to_bv 64 (estart E0 (SA b k) + i)) < bv_unsigned w + 8).
      { unfold estart. cbn [a_base a_off]. rewrite u64_lit by lia. lia. }
      rewrite Mr0_visible by (first [lia | apply Hvis; exact Ha]).
      (* LPS revision repair (75d69e00).  TWO defects in this block, both found by
         compiling punycode's identical copy; neither was ever compiled when written.
         (1) The window test cannot be made FALSE here.  [StoreOk.stack_window_lo_valid]
             puts [stack_window_lo (in_kernel inp) mbase rdraw] at or below
             [bv_unsigned sp + stack_window_reach - stack_max_size] = [usp - 6144513],
             while this address is at or ABOVE [usp] (from [Hlo] and [Ha]).  So
             [stack_window_lo … <=? a] is TRUE, and [Z.leb_gt]'s side goal is false.
         (2) [usp_eq_sp] is not a lemma: it occurs in no tree in this repository and in
             no LPS revision.
         What IS true at or above [sp] is that [wrap_mem]'s zero-fill branch is
         unreachable, because that branch is gated on [a <? sp].  LPS states exactly
         that as [PropExec.wrap_above_sp], and this same file already uses it that way
         at :706 and :980.  RULE 25 is kept on the closing [lia]. *)
      unfold FULL0.
      rewrite (wrap_above_sp inp mbase ph entryw sp rdraw) by (unfold usp in *; lia).
      fold bsb.
      (* RULE 25 WITHDRAWN HERE, MEASURED, and this is the punycode fix I failed to carry
         across when I made it: `clear - Ha Hlo Hhi` SUCCEEDS at this goal and takes `segs`
         with it, and `stack_to_mem_defined` is a Section lemma over `segs`, so the round
         reported "stack_to_mem_defined depends on the variable segs which is not declared
         in the context" (echconfiglist :782 in one farm round; punycode's
         identical copy reported it at :974 in another and was fixed).
         The two goals here are two-term linear facts over Ha/Hlo/Hhi; the
         hang rule 25 guards against was never measured at THIS goal. *)
      unfold usp in *;
      apply stack_to_mem_defined; lia.
  Qed.

  Lemma spb_eq : split_lit e_sp0 = (e_sp0, 0).
  Proof. reflexivity. Qed.

  Let AUXW := auxv_words la ph entryw uid (in_gid inp) hw
                (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn).

  (** the first 26 auxv pairs, which sit at the same place under both kernel builds *)
  Lemma auxv_word_ok : forall (j : nat) v,
    (j < 52)%nat ->
    nth j AUXW (Z_to_bv 64 0) = edenot E0 v ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 v).
  Proof.
    intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof R_range.
    pose proof lstr_lo. pose proof bsb_ge.
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
      assert (Hjc : (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat)
        by (destruct (kb_rseq (in_kernel inp)); cbn; lia).
      pose proof (read_auxv_word segs Sv48 inp mbase ph entryw sp brk0 rdraw) as RW. inst_hyps RW.
      exact (RW j Hjc).
  Qed.

  Lemma auxw_ok : forall i ty v,
    (0 <= i <= 25) ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    nth (Z.to_nat (2 * i + 1)) AUXW (Z_to_bv 64 0) = edenot E0 v ->
    know_ok segs E0 Mr0 (auxw i ty v).
  Proof.
    intros i ty v Hi H1 H2. unfold auxw.
    constructor; [|constructor; [|constructor]].
    - replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia. apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
    - replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia. apply auxv_word_ok; [lia|]. exact H2.
  Qed.

  (** [auxk]'s obligation.  The KEY word is [auxw_ok]'s first conjunct unchanged; the
      VALUE word is claimed only READABLE, via [kunk_stack] at the memory level, because
      no plan variable denotes it.  UNITS, named because three are live in nine lines:
      [i] is a PAIR index; [2*i] and [2*i+1] are WORD indices into [AUXW]; [16*i] and
      [16*i+8] are BYTE offsets from [e_auxb]. *)
  Lemma auxk_ok : forall i ty,
    (0 <= i <= 25) ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    know_ok segs E0 Mr0 (auxk i ty).
  Proof.
    intros i ty Hi H1. unfold auxk.
    (* THE SAME DEFECT AS punycode's Common/AsanInit.v `auxk_ok`, which I repaired
        and did not carry here - the third time in this lane that a twin was left
       behind, so this time I checked the twin before the round did.
       Measured on the farm (echconfiglist, source...975cbe,
       image sha256:2c6b6db8...e590fe, build-nosandbox, --cpu 4 --cpu-limit 4 -j 4, exit 0,
       no `^VOID:`, COMPILED 1691) reports `:853 Tactic failure: Cannot find witness` at
       characters 42-45, which is the `lia` inside `[reflexivity | lia]` - u64_lit's side
       condition
         0 <= bv_unsigned (edenot E0 (fst e_auxb)) + (snd e_auxb + 16 * i + 8) < 2 ^ 64.
       This proof posed NOTHING, so lia had no bound on the auxv base at all.
       The prelude is THIS FILE's own `auxv_word_ok` (:805-812), re-read here rather than
       transposed from punycode (22b): same eleven layout facts, same `split_u` on `e_auxv`
       keyed through `u_e_auxv`, same `snd e_auxb = 24` by computation.  I do NOT `set`
       ab/ak as that lemma does, because this one's bullets name `fst e_auxb` and
       `snd e_auxb` directly and a `set ... in *` would rewrite them out from under the
       `eapply kunk_stack with`.
       RULE 2: nothing new is assumed - every posed fact is an already-proved lemma of this
       section - and `i` stays bounded only by this lemma's own `Hi : 0 <= i <= 25`, the
       26-row fixed part of the auxv at 75d69e00.  No kernel field is pinned.
       THIS FILE IS THE GATE: r4 showed 646 of this unit's files have never been compiled,
       and they are dark behind this one error. *)
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof R_range.
    pose proof lstr_lo. pose proof bsb_ge.
    assert (Hab : split_lit e_auxv = (fst e_auxb, snd e_auxb)) by (unfold e_auxb; destruct (split_lit e_auxv); reflexivity).
    pose proof (split_u E0 e_auxv (fst e_auxb) (snd e_auxb) Hab) as Hs. rewrite u_e_auxv in Hs.
    assert (Hak : snd e_auxb = 24) by (vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    constructor; [|constructor; [|constructor]].
    - replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia.
      apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
    - eapply kunk_stack with (w := Z_to_bv 64 (bv_unsigned (edenot E0 (fst e_auxb)) + (snd e_auxb + 16 * i + 8)));
        [ rewrite u64_lit; [reflexivity | lia]
        | rewrite u64_lit by lia; lia
        | rewrite u64_lit by lia; lia
        (* The prelude above cleared bullets 1-3; a farm round moved this
           lemma's first error from :853 to :884, i.e. from the FIRST bullet to this one -
           four bullets on, not the 27 lines my comment inserted, so the prelude landed.
           This closing `lia` needs `Hx` in numeric form for the same reason the earlier
           ones did: `Hx` bounds `x` against `bv_unsigned w` where `w` is a `Z_to_bv 64 _`,
           so `u64_lit` must fire before the arithmetic is visible.  Same closing form
           punycode's twin took; `try` so the step is correct whether or not
           the rewrite has anything to do. *)
        | intros x Hx; apply not_argH0;
          try (rewrite u64_lit in Hx by lia); unfold usp in *; lia ].
  Qed.

  Lemma kr_ok : forall e lo hi, lo <= uE E0 e <= hi -> kentry_ok segs E0 Mr0 (KRange e lo hi).
  Proof. intros e lo hi H. cbn [kentry_ok]. unfold uE in H. exact H. Qed.

  (** bytes of the zero window below sp, through [Mr0] *)
  Lemma Mr0_below : forall a : word, usp - 6144513 <= bv_unsigned a < usp -> Mr0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. pose proof usp_lo. pose proof len_av.
    rewrite Mr0_visible; [apply FULL0_below; exact Ha | lia | apply not_argH0; lia].
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

  (** argv[0] is at the bottom of the string area, [string_base_addr] bytes below the
      stack VMA's end *)
  Lemma cat_argv0_eq :
    bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) = STR0.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof R_range.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum.
    rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0 Hav0).
    change (total_arg_bytes_nat (firstn 0 (in_argv inp))) with 0%nat.
    rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
    change (in_argv inp) with argv. change (in_envp inp) with envp. change (in_execfn inp) with execfn.
    change (kb_rseq (in_kernel inp)) with rseq.
    unfold STR0, CHEAD, W, usp, top, cat_string_off in *.
    rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia.
  Qed.

  Lemma argv0_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 8) 8 e_str0).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge.
    apply (kword_stack e_sp0 8 e_str0 (sp + nat_to_word (8 + 8 * 0))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
    - pose proof (read_argv_ptr_k segs inp mbase ph entryw sp rdraw 0) as RW.
      assert (Hv : cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0
                   = edenot E0 e_str0).
      { apply bv_eq. rewrite cat_argv0_eq. pose proof u_e_str0 as U. unfold uE in U. rewrite U. reflexivity. }
      rewrite <- Hv. apply RW; [exact Hav0|]. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
  Qed.

  (** the word at sp0+16: argv[1] or the argv NULL *)
  Lemma argv1_word_ok : kentry_ok segs E0 Mr0 (kw_argv1 e_argv1w).
  Proof.
    unfold kw_argv1.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge.
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    assert (Hw1 : edenot E0 e_argv1w = if (1 <? argc) then edenot E0 e_str1 else Z_to_bv 64 0).
    { unfold e_argv1w. cbn [edenot]. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. cbn [edenot] in U3.
      apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit, U3 by lia.
      pose proof (u64_range (edenot E0 e_str1)).
      destruct (1 <? argc); [rewrite Z.mul_1_l, Z.mod_small by lia; reflexivity | rewrite u64_lit by lia; reflexivity]. }
    apply (kword_stack e_sp0 16 e_argv1w (sp + nat_to_word (8 + 8 * 1))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
    - rewrite Hw1. destruct (1 <? argc) eqn:Hc.
      + apply Z.ltb_lt in Hc. assert (Hav1 : (1 < length argv)%nat) by (unfold argc in Hc; lia).
        pose proof (read_argv_ptr_k segs inp mbase ph entryw sp rdraw 1) as RW.
        assert (Hv : cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1
                     = edenot E0 e_str1).
        { apply bv_eq.
          pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof R_range.
          assert (TF : forall l : list (list byte), (0 < length l)%nat ->
                        Z.of_nat (total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1)
            by (intros [|x t] Hl; [cbn in Hl; lia|]; change (firstn 1 (x :: t)) with [x]; cbn -[Z.of_nat Z.add]; lia).
          pose proof (TF argv Hav0) as TF0.
          pose proof u_e_str1 as U. unfold uE in U.
          rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1 Hav1).
          rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
          change (in_argv inp) with argv. change (in_envp inp) with envp. change (in_execfn inp) with execfn.
          change (kb_rseq (in_kernel inp)) with rseq.
          rewrite U. unfold STR0, CHEAD, W, usp, L0, top, cat_string_off in *.
          rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia. }
        rewrite <- Hv. apply RW; [exact Hav1|]. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
      + apply Z.ltb_ge in Hc. assert (Hav1 : length argv = 1%nat) by (unfold argc in Hc; pose proof Hav0; lia).
        pose proof (read_argv_null segs Sv48 inp mbase ph entryw sp brk0 rdraw) as RW. inst_hyps RW.
        rewrite inp_argv in RW. rewrite Hav1 in RW.
        exact RW.
  Qed.

  (** the AT_RANDOM block is byte string [K_RND] = the draw (faithful, no hypothesis) *)
  Lemma atrandom_ok : kentry_ok segs E0 Mr0 (KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge. pose proof R_range.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof lstr_lo.
    assert (Hab : split_lit e_atrandom = (fst e_atrb, snd e_atrb)) by (unfold e_atrb; destruct (split_lit e_atrandom); reflexivity).
    set (ab := fst e_atrb) in *. set (ak := snd e_atrb) in *.
    pose proof (split_u E0 e_atrandom ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    assert (Hak : 0 <= ak <= 456) by (subst ak; vm_compute; split; discriminate).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + CHEAD - 16) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl.
    assert (HE : eb E0 K_RND = at_random_bytes (ed_random rdraw)) by (unfold E0; cbn [eb]; rewrite Nat.eqb_refl; reflexivity).
    rewrite HE.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    split; [rewrite length_at_random_bytes; reflexivity|].
    intros i Hi.
    pose proof (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw) as AO. inst_hyps AO.
    destruct AO as [off (Hp & Hoff & Hmod & Hrd)].
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

  Lemma kimg_ok : kentry_ok segs E0 Mr0 (KImg (img_lo A) (img_hi A)).
  Proof.
    pose proof usp_lo. pose proof (if_hull _ _ _ IMG) as (H1 & H2 & H3 & H4). cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    unfold Mr0, Mr, mrestrict. destruct (hid A argH0 E0 cs0 model0 (Z_to_bv 64 i)); [reflexivity|].
    apply FULL0_low. rewrite u64_lit; lia.
  Qed.

  Lemma rw_window_ok : kentry_ok segs E0 Mr0 (KWr (SA (ELit 0) (rw_lo A)) (ELit (rw_len A))).
  Proof.
    pose proof (if_rw _ _ _ IMG) as ((R1 & R0' & R2) & R3).
    assert (Hst : estart E0 (SA (ELit 0) (rw_lo A)) = rw_lo A) by (unfold estart; cbn [a_base a_off]; rewrite edenot_lit, u64_lit; lia).
    assert (Hl : elenZ E0 (ELit (rw_len A)) = rw_len A) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. split; [unfold flat; rewrite Hst; lia|].
    intros d m Hd Hdm. destruct m as [|m']; [reflexivity|].
    assert (Hu : bv_unsigned (Z_to_bv 64 (rw_lo A + d)) = rw_lo A + d) by (apply u_small; rewrite Nat2Z.inj_succ in Hdm; lia).
    apply store_ok_of_all; rewrite Hu; [lia|].
    intros x Hx. apply R3. lia.
  Qed.

  Lemma atr_ptr_eq : at_random_ptr sp rseq argv envp = edenot E0 e_atrandom.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof chead_eq. pose proof gap_range. pose proof R_range.
    pose proof len_av. pose proof len_ev. pose proof bsb_ge.
    pose proof (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw) as AO. inst_hyps AO.
    destruct AO as [off (Hp & Hoff & _ & _)].
    rewrite inp_argv, inp_envp, inp_rseq in Hp, Hoff.
    apply bv_eq. rewrite Hp, word_add_nat, u64_lit by (unfold CHEAD, usp in *; lia).
    pose proof u_e_atrandom as U. unfold uE in U. rewrite U. unfold CHEAD, usp. lia.
  Qed.

  Lemma init_kn_with_ok : forall atr, kentry_ok segs E0 Mr0 atr -> know_ok segs E0 Mr0 (init_kn_with atr A).
  Proof.
    intros atr Hatr.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof gap_range. pose proof R_range. pose proof chead_eq. pose proof length_bsb_sum. pose proof lstr_lo.
    pose proof brk_range as [B1 B2]. pose proof bsb_ge. pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    pose proof (if_ph _ _ _ IMG) as (P1 & P2 & P3).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    unfold init_kn_with.
    destruct stack_window_ok as [SW1 SW2].
    apply Forall_app; split.
    { apply Forall_cons; [apply kr_ok; rewrite U1; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U2; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_S3; lia|].
      apply Forall_cons; [apply kr_ok; unfold eaddz, uE; rewrite mkAlu_denot, edenot_lit, u_add64, u64_lit by lia;
                          pose proof u_e_atrandom as U; unfold uE in U; rewrite U; rewrite Z.mod_small by lia; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_atr8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_sp0; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_pg; pose proof pagedown_usp; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_sp8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U3; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U4; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U5; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_L1; pose proof L1_range; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_uid; unfold valid_id in Huid; pose proof (u64_range uid); lia|].
      apply Forall_cons; [cbn [kentry_ok]; change (edenot E0 (EVar V_HW)) with hw;
                          destruct Hhw as [Eh|Eh]; apply (f_equal bv_unsigned) in Eh; rewrite Eh;
                          unfold hwcap_rv64gc, hwcap_rv64gcv; rewrite u64_lit by lia; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U9; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U6; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U7; unfold BRK_ASLR in *; lia|].
      apply Forall_cons; [exact SW1|].
      apply Forall_cons; [exact SW2|].
      apply Forall_cons; [exact argc_word_ok|].
      apply Forall_cons; [exact argv0_word_ok|].
      apply Forall_cons; [exact argv1_word_ok|].
      apply Forall_nil. }
    repeat (apply Forall_app; split).
    (* [1-9:] addressed the nine auxw groups POSITIONALLY; the seventeen auxk groups
       added to init_kn_with make twenty-six, so every bullet below it shifted and the
       failure surfaced further down rather than here.  Dispatch by the goal's own shape
       instead, which is independent of how many groups there are.  Measured in punycode
       first: a farm round moved Common/AsanInit.v from :1221 to :924,
       proving the dispatch works and isolating the fault to the helper. *)
    all: try (first [ apply auxk_ok | apply auxw_ok ];
              [ lia
              | unfold AUXW, auxv_words, auxv_entries;
                cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
                try reflexivity .. ]).
    all: try (rewrite edenot_lit; reflexivity).
    1: rewrite edenot_lit, P1; reflexivity.
    1: rewrite edenot_lit, P2; reflexivity.
    1: rewrite edenot_lit, P3; reflexivity.
    1: exact atr_ptr_eq.
    apply Forall_cons; [exact Hatr|].
    apply Forall_cons; [exact kimg_ok|].
    apply Forall_cons; [exact rw_window_ok|].
    apply Forall_nil.
  Qed.

  Lemma init_kn_ok : know_ok segs E0 Mr0 (init_kn A).
  Proof. exact (init_kn_with_ok _ atrandom_ok). Qed.

  (* ----------------------------------------------------------------------- *)
  (** ** LPS 727298f3: the per-build claims [init_kn_r R A] adds (the form of
         boost-beast/http_request's As/AsanInit.v)                            *)
  (* ----------------------------------------------------------------------- *)

  (** [auxv_word_ok] at any word the run's build has (54 without CONFIG_RSEQ, 58 with it) *)
  Lemma auxv_word_ok_r : forall (j : nat) v,
    Z.of_nat j < 54 + 4 * R ->
    nth j AUXW (Z_to_bv 64 0) = edenot E0 v ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 v).
  Proof.
    intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof R_range.
    pose proof lstr_lo. pose proof bsb_ge.
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
      pose proof (auxv_count_lt rseq j Hj) as Hjc.
      pose proof (read_auxv_word segs Sv48 inp mbase ph entryw sp brk0 rdraw) as RW. inst_hyps RW.
      exact (RW j Hjc).
  Qed.

  Lemma auxw_ok_r : forall i ty v,
    0 <= i -> 2 * i + 1 < 54 + 4 * R ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    nth (Z.to_nat (2 * i + 1)) AUXW (Z_to_bv 64 0) = edenot E0 v ->
    know_ok segs E0 Mr0 (auxw i ty v).
  Proof.
    intros i ty v Hi0 Hi H1 H2. unfold auxw.
    constructor; [|constructor; [|constructor]].
    - replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia. apply auxv_word_ok_r; [lia|]. rewrite H1. reflexivity.
    - replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia. apply auxv_word_ok_r; [lia|]. exact H2.
  Qed.

  (** the CONFIG_RSEQ value, and the vector's tail at its literal pair index for that build *)
  Lemma auxv_rseq_ok : know_ok segs E0 Mr0 (auxv_rseq_kn R).
  Proof.
    pose proof R_range as HR. destruct uE0 as (_ & _ & _ & _ & _ & _ & _ & _ & U9).
    unfold auxv_rseq_kn. apply Forall_app; split.
    { apply Forall_cons; [apply kr_ok; rewrite U9; lia | apply Forall_nil]. }
    destruct (Z.eqb_spec R 1) as [H1|H1]; cbv iota.
    - pose proof (auxv_words_rseq_on la ph entryw uid (in_gid inp) hw
                    (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn)
                    (rseq_z_true rseq H1)) as (W52 & W53 & W54 & W55 & W56 & W57).
      repeat (apply Forall_app; split).
      + apply auxw_ok_r; [lia | lia | exact W52 | rewrite edenot_lit; exact W53].
      + apply auxw_ok_r; [lia | lia | exact W54 | rewrite edenot_lit; exact W55].
      + apply auxw_ok_r; [lia | lia | exact W56 | rewrite edenot_lit; exact W57].
    - pose proof (auxv_words_rseq_off la ph entryw uid (in_gid inp) hw
                    (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn)
                    (rseq_z_false rseq H1)) as (W52 & W53).
      apply auxw_ok_r; [lia | lia | exact W52 | rewrite edenot_lit; exact W53].
  Qed.

  (** AT_GID's and AT_EGID's value words, both [EVar V_GID] = the launch's gid ([auxv_words_gid];
      [vals0]'s fourteenth word) *)
  Lemma auxv_gid_ok : know_ok segs E0 Mr0 auxv_gid_kn.
  Proof.
    pose proof (auxv_words_gid la ph entryw uid (in_gid inp) hw
                  (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn)) as [G1 G2].
    unfold auxv_gid_kn.
    apply Forall_cons.
    { replace (snd e_auxb + 16 * 21 + 8) with (snd e_auxb + 8 * Z.of_nat 43) by lia.
      apply auxv_word_ok; [lia | exact G1]. }
    apply Forall_cons.
    { replace (snd e_auxb + 16 * 22 + 8) with (snd e_auxb + 8 * Z.of_nat 45) by lia.
      apply auxv_word_ok; [lia | exact G2]. }
    apply Forall_nil.
  Qed.

  (** LPS c0dd863a: AT_SYSINFO_EHDR's value word, [EVar V_EHDR] = the vDSO text base
      ([auxv_words_sysinfo]; [vals0]'s fifteenth word) *)
  Lemma auxv_ehdr_ok : know_ok segs E0 Mr0 auxv_ehdr_kn.
  Proof.
    pose proof (auxv_words_sysinfo la ph entryw uid (in_gid inp) hw
                  (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn)) as G1.
    unfold auxv_ehdr_kn.
    apply Forall_cons; [| apply Forall_nil].
    replace (snd e_auxb + 8) with (snd e_auxb + 8 * Z.of_nat 1) by lia.
    apply auxv_word_ok; [lia | exact G1].
  Qed.

  Lemma init_kn_r_ok : know_ok segs E0 Mr0 (init_kn_r R A).
  Proof.
    unfold init_kn_r. apply Forall_app; split; [exact init_kn_ok|].
    apply Forall_app; split; [exact auxv_rseq_ok|].
    apply Forall_app; split; [exact auxv_gid_ok | exact auxv_ehdr_ok].
  Qed.

  (* ----------------------------------------------------------------------- *)
  (** ** The initial [cs_ok] and the initial configuration                     *)
  (* ----------------------------------------------------------------------- *)

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

  Lemma u_e_stk : uE E0 e_stk = pagedown usp - 8388608.
  Proof.
    pose proof pagedown_usp as (P1 & P2 & P3 & P4). pose proof usp_hi. unfold e_stk, eaddz, uE. rewrite mkAlu_denot, edenot_lit, u_add64.
    pose proof u_e_pg as U. unfold uE in U. rewrite U.
    rewrite Z_to_bv_unsigned. change (bv_wrap 64 (-8388608)) with (2 ^ 64 - 8388608).
    replace (pagedown usp + (2 ^ 64 - 8388608)) with ((pagedown usp - 8388608) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  Qed.

  Lemma u_e_stklen : uE E0 e_stklen = 0x800000000000 + 8388608 - pagedown usp.
  Proof.
    pose proof pagedown_usp as (P1 & P2 & P3 & P4). pose proof usp_hi. unfold e_stklen, esub, uE. rewrite mkAlu_denot, edenot_lit, u_sub64.
    pose proof u_e_pg as U. unfold uE in U. rewrite U. rewrite u64_lit by lia. apply Z.mod_small. lia.
  Qed.

  Lemma allowA_init : allowA A E0 cs0 =
    [(pagedown (img_lo A), pageup (img_lo A + (img_hi A - img_lo A)));
     (pagedown (shadow_off A + img_lo A / 8), pageup (shadow_off A + (img_lo A + (img_hi A - img_lo A)) / 8));
     (pagedown (pagedown usp - 8388608), pageup ((pagedown usp - 8388608) + (0x800000000000 + 8388608 - pagedown usp)));
     (pagedown (shadow_off A + (pagedown usp - 8388608) / 8), pageup (shadow_off A + ((pagedown usp - 8388608) + (0x800000000000 + 8388608 - pagedown usp)) / 8))].
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    unfold allowA, cs0, init_acs_r, init_acs_of_with, init_vis. cbn [a_vis a_ghost app flat_map allow1 fst snd].
    unfold sh_lo, sh_hi. cbn [fst snd]. rewrite !u_e_stk, !u_e_stklen.
    unfold uE. rewrite !edenot_lit, !u64_lit by lia. reflexivity.
  Qed.

  Lemma abytes_init : A_bytes (allowA A E0 cs0) <= vis_cost (img_hi A - img_lo A) + vis_cost STKLEN_MAX
                      /\ vis_cost (img_hi A - img_lo A) + vis_cost STKLEN_MAX <= LIMIT.
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof (if_shadow _ _ _ IMG) as S1. pose proof usp_hi.
    pose proof pagedown_usp as (Q1 & Q2 & Q3 & Q4).
    rewrite allowA_init. set (pu := pagedown usp) in *. cbn [A_bytes fst snd]. unfold vis_cost, STKLEN_MAX, CEIL, LIMIT, target_alloc_limit.
    replace (img_lo A + (img_hi A - img_lo A)) with (img_hi A) by lia.
    replace (pu - 8388608 + (0x800000000000 + 8388608 - pu)) with 0x800000000000 by lia.
    assert (P1 : forall z, z mod 4096 = 0 -> pagedown z = z) by (intros z Hz; unfold pagedown; lia).
    assert (P2 : forall z, z mod 4096 = 0 -> pageup z = z) by (intros z Hz; unfold pageup; lia).
    rewrite (P1 (img_lo A) I3), (P2 (img_hi A) I4).
    rewrite (P2 0x800000000000 eq_refl).
    pose proof (pageup_minus_pagedown (shadow_off A + img_lo A / 8) (shadow_off A + img_hi A / 8) ltac:(lia)).
    pose proof (pageup_minus_pagedown (shadow_off A + (pu - 8388608) / 8) (shadow_off A + 0x800000000000 / 8) ltac:(lia)).
    assert (pu - 8388608 - 4096 < pagedown (pu - 8388608) <= pu - 8388608) by (unfold pagedown; lia).
    split; lia.
  Qed.

  Theorem init_cs_ok : cs_ok segs A LIMIT SINV0 argH0 (in_fs inp) E0 cs0 R0 FULL0 model0.
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
    destruct abytes_init as [AB1 AB2].
    constructor; cbn [cs0 init_acs_r init_acs_of_with a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_vmops];
      rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
    - exact init_regs_ok.
    - reflexivity.
    - exact init_kn_r_ok.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros _; reflexivity.
    - (* the ledger: the image's reservations and the launch's vDSO pair; no tracked maps;
         the pair is the one [State.init_reserved] appended *)
      pose proof (if_resx _ _ _ IMG) as [RX1 RX2]. pose proof resx_bytes_lo.
      pose proof (vdso_len_bounds kb).
      split; [|split; [|split; [|split]]].
      + exists RESX. split; [reflexivity|].
        split; [exact resx_ok|]. split; [pose proof resx_len; lia | rewrite resx_sum; unfold page_size in *; lia].
      + constructor.
      + replace (m_kernel model0) with kb by reflexivity.
        replace (vdso_top (m_vmmaps model0)) with VTOP
          by (symmetry; exact (vdso_top_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp)).
        apply incl_appr, incl_refl.
      + (* no ghost range at the launch *)
        constructor.
      + (* LPS c0dd863a: [co_ehdr]: [vals0]'s fifteenth word is [Run.vdso_text_base] at the run's
           kernel build, stack pointer and mmap base, which is the initial ledger's [vdso_top]
           less the text pages, by unfolding *)
        reflexivity.
    - reflexivity.
    - reflexivity.
    - constructor.
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      exact (init_sp_ok_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp Hsp).
    - constructor.
    - constructor.
    - rewrite TOP0. pose proof usp_lo. pose proof usp_hi. unfold CEIL, CEILMAX. lia.
    - rewrite TOP0. pose proof u_e_sp0 as U. unfold uE in U. rewrite e_sp0_early_eq, U. reflexivity.
    - intros z Hz. exact Hz.
    - constructor.
    - constructor.
    - (* the image's reservations and the vDSO pair *)
      pose proof (vdso_len_bounds kb). pose proof resx_bytes_lo.
      rewrite app_nil_r, sum_sizes_app, (if_sizes _ _ _ IMG), resx_sum. unfold page_size in *. lia.
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7 & _). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.
    - lia.
    - lia.
    - exact AB1.
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
    - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
    - split; [intros; reflexivity | intros; reflexivity].
    - split; reflexivity.
    - (* 08b1429: the launch's channel reader, copied by [init_model] and kept by [with_vdso] *)
      (* `cbn [...]` takes a delta-list of EVALUABLE references, and `mkModelOf` and
         `mkProcState` are record CONSTRUCTORS, not definitions (75d69e00 State.v:4873
         `Record Model := mkModelOf {`, :4279 `Record ProcState := mkProcState {`), so the
         round reported "Cannot coerce mkModelOf to an evaluable reference"
         (farm/20261106t211157z, AsanInit.v:1269).  Constructor applications are reduced by
         IOTA, which `cbn` performs regardless of the delta-list, so the two names are
         dropped rather than replaced.  The projections and the two real definitions stay. *)
      unfold model0, m_channel_reader. cbn [with_vdso m_proc init_model procst_channel_reader].
      exact Hrdrin.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (** ** What [SINV0] provides to the start-up extensions                     *)
  (* ----------------------------------------------------------------------- *)

  (** AsanInit's [STR0] ([usp + C + pad]) is [AsanNodesStartX]'s ([usp + cat_string_off]) *)
  Lemma str0_cat : STR0 = usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).
  Proof. unfold STR0, CHEAD, W, cat_string_off. rewrite Nat2Z.inj_add. lia. Qed.

  Lemma SINV0_vals_E0 : forall E M, SINV0 E M ->
    uE E e_envp = usp + 8 * argc + 16 /\ ev E V_ENVC = Z_to_bv 64 envc
    /\ uE E e_str0 = usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).
  Proof.
    intros E M [Hev _].
    pose proof u_e_envp as U1. pose proof u_e_str0 as U3. pose proof uE0_envc as U2. unfold uE in U1, U2, U3.
    unfold uE. rewrite (edenot_ev_agree0 V_EHDR E E0 e_envp eq_refl Hev), (edenot_ev_agree0 V_EHDR E E0 e_str0 eq_refl Hev).
    split; [exact U1|]. split; [| rewrite U3; exact str0_cat].
    change (ev E V_ENVC) with (edenot E (EVar V_ENVC)).
    rewrite (edenot_ev_agree0 V_EHDR E E0 (EVar V_ENVC) eq_refl Hev).
    apply bv_eq. rewrite U2. pose proof len_ev. unfold envc in *. rewrite u64_lit by lia. reflexivity.
  Qed.

  Lemma SINV0_sp0_E0 : forall E M, SINV0 E M -> uE E e_sp0_early = usp.
  Proof.
    intros E M [Hev _]. rewrite e_sp0_early_eq. unfold uE.
    rewrite (edenot_ev_agree0 V_EHDR E E0 e_sp0 eq_refl Hev). exact u_e_sp0.
  Qed.

  Lemma SINV0_pg_E0 : forall E M, SINV0 E M -> uE E e_pg_early = pagedown (uE E e_sp0_early).
  Proof.
    intros E M HS. rewrite (SINV0_sp0_E0 E M HS). destruct HS as [Hev _].
    rewrite e_pg_early_eq. unfold uE.
    rewrite (edenot_ev_agree0 V_EHDR E E0 e_pg eq_refl Hev). exact u_e_pg.
  Qed.

  Lemma SINV0_envp_E0 : forall E M (a : word), SINV0 E M ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 ->
    M a = wrap_mem inp mbase ph entryw sp rdraw a.
  Proof.
    intros E M a HS Ha. pose proof HS as [_ HM]. apply HM. rewrite (argH0_SINV0 E M a HS). unfold argB0.
    pose proof len_av. apply orb_true_intro. left. apply andb_true_intro.
    split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  Lemma SINV0_str0_E0 : forall E M (a : word), SINV0 E M ->
    usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn) <= bv_unsigned a
      <= usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn) + Z.of_nat (length (nth 0 argv [])) ->
    M a = wrap_mem inp mbase ph entryw sp rdraw a.
  Proof.
    intros E M a HS Ha. pose proof HS as [_ HM]. apply HM. rewrite (argH0_SINV0 E M a HS). unfold argB0.
    rewrite <- str0_cat in Ha. pose proof str0_hi. pose proof s0_in_strings. unfold L0 in *.
    apply orb_true_intro. right. apply andb_true_intro.
    split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (** [Run.init_config] is the configuration [cs_ok] speaks about *)
  Theorem init_cfg_eq :
    init_config segs apc ph sp brk0 mbase rdraw LIMIT inp = cfg_of segs R0 (a_entry A) FULL0 model0.
  Proof.
    unfold init_config, cfg_of, FULL0, entryw. rewrite init_mkst, Hapc. reflexivity.
  Qed.
End Init.
