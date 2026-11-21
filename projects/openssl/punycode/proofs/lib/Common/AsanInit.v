(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch is the run's whole ProcInput and the entry stack image Linux's whole block; E0 gains the group id for V_GID; the start state's auxv facts are proved for every pair of the run's own 27- or 29-pair vector, the CONFIG_RSEQ tail by a case split on the run's flag, and the AT_RANDOM shadow-index facts at the new block layout; the vDSO in the initial model and the reserved ledger); and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* Ported to LPS 08b1429: the entry stack image is Linux's whole block from sp to the
   stack VMA's end [ed_top] (strings at the top, the AT_RANDOM bytes and the
   [arch_align_stack] pad below them, a 27- or 29-pair auxv by CONFIG_RSEQ), the launch
   reserves the vDSO/vvar pair, and the Section takes the run's whole [ProcInput].
   The fork's page-tail variables stay: [V_P]/[V_Q] now name [ed_top] exactly. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StoreOk StreamSim StepTac ShapeAlg AgentLib StartupAux RefLayoutC ArgvEnvC
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan AsanPlanSound.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AsanCeil.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition LIMIT : Z := target_alloc_limit.
(* [comment removed for export] *)
Definition LIM_MIN : Z := 2 ^ 33.
Lemma LIMIT_ok : LIM_MIN <= LIMIT. Proof. unfold LIM_MIN, LIMIT, target_alloc_limit. lia. Qed.
Lemma SRC_LIMIT_ok : LIM_MIN <= source_alloc_limit. Proof. unfold LIM_MIN, source_alloc_limit. lia. Qed.

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
  (** the table's bounds on what the LAUNCH reserves beside the image: the vDSO pair,
      two intervals of at most twenty pages ([State.vdso_len_bounds]) *)
  if_resx  : (2 <= n_resx A)%nat /\ (20 <= p_resx A)%nat
}.

(** the EXACT size of the initial stack image: Linux's block runs from the entry stack
    pointer to the stack VMA's end ([PropExec.length_entry_stack_image_launch]) *)
Definition stack_image_size (sp top : word) : Z :=
  (bv_unsigned top - bv_unsigned sp)%Z.

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

(** the string area holds argv[0] and argv[1] with their NULs, and at least the exec name's NUL *)
Lemma launch_strings_argv01 : forall (av ev : list (list byte)) (ex : list byte), (0 < length av)%nat ->
  (length (nth 0 av []) + length (nth 1 av []) + 2 <= launch_string_bytes av ev ex)%nat.
Proof.
  intros [|a [|b t]] ev ex H; [cbn in H; lia| |];
    unfold launch_string_bytes; cbn [flatten_strings flat_map nth]; rewrite !length_app; cbn [length]; lia.
Qed.

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
  (* [comment removed for export] *)
  Variable LIM : Z.
  Hypothesis HLIM : LIM_MIN <= LIM.

  Let argv : list (list byte) := in_argv inp.
  Let envp : list (list byte) := in_envp inp.
  Let uid : word := in_uid inp.
  Let gid : word := in_gid inp.   (* AT_GID / AT_EGID; a ProcInput field of its own, never [uid] *)
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
  (* [comment removed for export] *)
  Hypothesis Huid : valid_id uid.
  (** [Run.valid_input]'s launch clause: a name [execve] admits, under E2BIG *)
  Hypothesis Hlaunch : valid_launch inp.
  (** [Run.valid_input]'s reader clause ([Run.valid_input_channel_reader]) *)
  Hypothesis Hrdr : in_channel_reader inp = true.
  (** [Run.valid_entry]'s FIFTH conjunct: the start state is exactly a Linux launch *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  (* [comment removed for export] *)
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).

  Let entryw : word := Z_to_bv 64 (Z.of_N apc).
  Let la : LaunchAuxv := launch_auxv inp sp mbase.
  Let top : word := ed_top rdraw.

  Lemma inp_argv : in_argv inp = argv.        Proof. reflexivity. Qed.
  Lemma inp_envp : in_envp inp = envp.        Proof. reflexivity. Qed.
  Lemma inp_execfn : in_execfn inp = execfn.  Proof. reflexivity. Qed.
  Lemma inp_rseq : kb_rseq (in_kernel inp) = rseq. Proof. reflexivity. Qed.
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
  (** the page of sp, and the page count from it to the stack VMA's end *)
  Let PGSP := pgdown usp.
  Let Q := (utop - PGSP) / 4096.

  Definition vals0 : list word :=
    [Z_to_bv 64 (usp / 32768); Z_to_bv 64 argc; Z_to_bv 64 envc; Z_to_bv 64 L0; Z_to_bv 64 W;
     Z_to_bv 64 (bv_unsigned brk0 / 4096); Z_to_bv 64 ((usp mod 4096) / 16); Z_to_bv 64 L1; uid; hw;
     Z_to_bv 64 ((usp mod 32768) / 4096); Z_to_bv 64 Q; Z_to_bv 64 G; Z_to_bv 64 R; gid].
  (* [comment removed for export] *)
  Definition E0 : env := Env (fun n => nth n vals0 (Z_to_bv 64 0))
                             (fun k => if Nat.eqb k K_RND then at_random_bytes (ed_random rdraw) else []).

  (** hidden argument bytes: the envp pointer array (with its NULL) and the string area,
      which is at the TOP of the block — argv[0] at [STR0], up to the stack VMA's end *)
  Definition argH0 (E : env) (a : word) : bool :=
    let z := bv_unsigned a in
    (((usp + 8 * argc + 16 <=? z) && (z <? usp + 8 * argc + 8 * envc + 24))
     || ((STR0 <=? z) && (z <? utop)))%bool.

  Definition SINV0 (E : env) (M : word -> option byte) : Prop :=
    (forall n, (n < NX0)%nat -> ev E n = ev E0 n)
    /\ (forall a, argH0 E a = true -> M a = wrap_mem inp mbase ph entryw sp rdraw a).

  (* ----------------------------------------------------------------------- *)
  (** ** Layout arithmetic                                                    *)
  (* ----------------------------------------------------------------------- *)

  Lemma Hlo' : (sp_window_lo <= bv_unsigned sp)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hhi' : (bv_unsigned sp <= sp_window_hi)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hal' : (bv_unsigned sp mod 16 = 0)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hav0 : (0 < length argv)%nat. Proof. destruct Hva as [[? ?] _]; lia. Qed.

  (** instantiate the hypotheses a [RefLayoutC]/[PropExec] lemma's Section discharged *)
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

  Lemma chead_range : 480 <= CHEAD <= 10752.
  Proof. pose proof chead_eq. pose proof len_av. pose proof len_ev. pose proof gap_range. pose proof R_range. lia. Qed.

  Lemma s01_in_strings : L0 + L1 + 2 <= LSTR.
  Proof. unfold LSTR, L0, L1. pose proof (launch_strings_argv01 argv envp execfn Hav0). lia. Qed.

  Lemma L1_nonneg : 0 <= L1.
  Proof. unfold L1. lia. Qed.

  Lemma s0_in_strings : L0 + 2 <= LSTR.
  Proof. pose proof s01_in_strings. pose proof L1_nonneg. lia. Qed.

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

  Lemma bsb_len_hi : Z.of_nat (length bsb) <= 2101782.
  Proof. unfold bsb. exact (bsb_bound Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau). Qed.

  Lemma usp_fit : usp + Z.of_nat (length bsb) <= 2 ^ 47.
  Proof.
    rewrite length_bsb_eq. unfold stack_image_size. fold utop usp.
    pose proof (entry_page_top_within_window Sv48 inp mbase sp brk0 rdraw Hlau) as H.
    unfold entry_page_top, va_stack_top, sp_window_hi in H. fold top utop in H. lia.
  Qed.

  Lemma bsb_ge : 8 * argc + 8 * envc + 482 <= Z.of_nat (length bsb).
  Proof.
    pose proof length_bsb_sum. pose proof chead_eq. pose proof lstr_lo. pose proof pad_range.
    pose proof gap_range. pose proof R_range. lia.
  Qed.

  Lemma str0_hi : STR0 + LSTR + 8 = utop.
  Proof. unfold STR0. pose proof pad_eq. lia. Qed.

  (** the stack VMA's end is page-aligned ([Run.valid_stack_top_va]) *)
  Lemma utop_al : utop mod 4096 = 0.
  Proof. destruct Hlau as ((Ht & _ & _) & _ & _). unfold utop, top, page_size in *. exact Ht. Qed.

  Lemma utop_eq : utop = usp + Z.of_nat (length bsb).
  Proof. rewrite length_bsb_eq. unfold stack_image_size. fold utop usp. lia. Qed.

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

  (* [comment removed for export] *)
  Ltac mod_small_inner :=
    repeat match goal with
      |- context [ (?a mod ?m) ] =>
        lazymatch a with context [ _ mod _ ] => fail | _ => rewrite (Z.mod_small a m) by lia end
    end.

  (* [comment removed for export] *)
  Ltac hide_lets := first [clearbody Q | idtac]; first [clearbody PGSP | idtac].

  (* [comment removed for export] *)
  Lemma usp_decomp :
    usp = 32768 * (usp / 32768) + 4096 * ((usp mod 32768) / 4096) + 16 * ((usp mod 4096) / 16)
    /\ 0 <= (usp mod 32768) / 4096 <= 7 /\ 0 <= (usp mod 4096) / 16 <= 255 /\ usp mod 4096 = 16 * ((usp mod 4096) / 16)
    /\ usp mod 32768 = 4096 * ((usp mod 32768) / 4096) + usp mod 4096.
  Proof.
    pose proof usp_lo. pose proof usp_al.
    pose proof (Z.div_mod usp 32768 ltac:(lia)). pose proof (Z.mod_pos_bound usp 32768 ltac:(lia)).
    pose proof (Z.div_mod (usp mod 32768) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (usp mod 32768) 4096 ltac:(lia)).
    pose proof (Z.div_mod usp 4096 ltac:(lia)). pose proof (Z.mod_pos_bound usp 4096 ltac:(lia)).
    pose proof (Z.div_mod (usp mod 4096) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (usp mod 4096) 16 ltac:(lia)).
    pose proof (Z.div_mod usp 16 ltac:(lia)).
    assert (E1 : (usp mod 32768) mod 4096 = usp mod 4096).
    { apply Z.mod_mod_divide. exists 8. reflexivity. }
    pose proof (Z.div_mod (usp mod 32768) 4096 ltac:(lia)) as D2. rewrite E1 in D2.
    assert (E2 : (usp mod 4096) mod 16 = 0).
    { rewrite Z.mod_mod_divide by (exists 256; reflexivity). exact usp_al. }
    assert ((usp mod 32768) / 4096 < 8) by (apply Z.div_lt_upper_bound; lia).
    assert ((usp mod 4096) / 16 < 256) by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_pos (usp mod 32768) 4096 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos (usp mod 4096) 16 ltac:(lia) ltac:(lia)).
    lia.
  Qed.

  (** the page of sp and the stack VMA's end: [top] is page-aligned, so [Q] pages
      reach it EXACTLY (there is no page slack above the block any more) *)
  Lemma PG_range : PGSP <= usp < PGSP + 4096 /\ utop = usp + Z.of_nat (length bsb)
                   /\ utop <= 2 ^ 47 /\ PGSP mod 4096 = 0 /\ utop mod 4096 = 0 /\ utop = PGSP + 4096 * Q /\ 1 <= Q <= 600.
  Proof.
    pose proof usp_lo. pose proof usp_fit as F. pose proof bsb_ge. pose proof bsb_len_hi. pose proof len_av. pose proof len_ev.
    pose proof utop_al as TA. pose proof utop_eq as TE.
    unfold Q, PGSP, pgdown.
    pose proof (Z.mod_pos_bound usp 4096 ltac:(lia)) as Mu.
    assert (Hd : (utop - (usp - usp mod 4096)) mod 4096 = 0) by lia.
    pose proof (Z.div_mod (utop - (usp - usp mod 4096)) 4096 ltac:(lia)) as Dd.
    rewrite Hd in Dd.
    assert (M1 : (usp - usp mod 4096) mod 4096 = 0) by lia.
    repeat split; try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma uE0 :
    uE E0 (EVar V_S1) = usp / 32768 /\ uE E0 (EVar V_S2) = (usp mod 4096) / 16
    /\ uE E0 (EVar V_ARGC) = argc /\ uE E0 (EVar V_ENVC) = envc /\ uE E0 (EVar V_L0) = L0
    /\ uE E0 (EVar V_W) = W /\ uE E0 (EVar V_BRK) = bv_unsigned brk0 / 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof pad_range.
    pose proof (u64_range brk0) as [B1 B2].
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    pose proof usp_decomp as (_ & _ & D3 & _).
    unfold uE. cbn [edenot E0 ev nth vals0 V_S1 V_S2 V_ARGC V_ENVC V_L0 V_W V_BRK].
    rewrite !u64_lit by lia. repeat split; reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma uE0_PQ : uE E0 (EVar V_P) = (usp mod 32768) / 4096 /\ uE E0 (EVar V_Q) = Q.
  Proof.
    pose proof usp_decomp as (_ & D2 & _). pose proof PG_range as (_ & _ & _ & _ & _ & _ & QR).
    unfold uE. cbn [edenot E0 ev nth vals0 V_P V_Q]. rewrite !u64_lit by lia. split; reflexivity.
  Qed.

  Lemma uE0_GR : uE E0 (EVar V_G) = G /\ uE E0 (EVar V_R) = R.
  Proof.
    pose proof gap_range. pose proof R_range.
    unfold uE. cbn [edenot E0 ev nth vals0 V_G V_R]. rewrite !u64_lit by lia. split; reflexivity.
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

  (* [comment removed for export] *)
  Lemma u_e_pgsp : uE E0 e_pgsp = usp - usp mod 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). destruct uE0 as (U1 & U2 & _). destruct uE0_PQ as [UP _].
    unfold e_pgsp, eadd, escale, uE in *. unfold V_S1, V_P in U1, UP. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, UP.
    rewrite !Z.mod_small by lia. lia.
  Qed.
  Lemma u_e_sp0 : uE E0 e_sp0 = usp.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). destruct uE0 as (U1 & U2 & _). destruct uE0_PQ as [UP _].
    unfold e_sp0, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2, UP.
    rewrite !Z.mod_small by lia. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma u_e_spw : uE E0 e_spw = usp.
  Proof. replace e_spw with e_sp0 by (vm_compute; reflexivity). exact u_e_sp0. Qed.
  (* [comment removed for export] *)
  Lemma SINV0_pgsp : forall E M, SINV0 E M -> uE E e_pgsp = pgdown usp.
  Proof.
    intros E M [H1 _]. unfold pgdown. rewrite <- u_e_pgsp. unfold uE, e_pgsp, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    cbn [edenot]. rewrite (H1 0%nat), (H1 10%nat) by (unfold NX0; lia). reflexivity.
  Qed.

  Lemma edenot_e_sp0 : edenot E0 e_sp0 = sp.
  Proof. apply bv_eq. exact u_e_sp0. Qed.

  Lemma u_sp8 : uE E0 e_sp8 = usp / 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). destruct uE0 as (U1 & U2 & _). destruct uE0_PQ as [UP _].
    unfold e_sp8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2, UP.
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
    pose proof R_range. destruct uE0_GR as [_ U9].
    unfold e_auxsz, eaddz, escale, uE in *. rewrite mkAlu_denot, mkMd_denot, !edenot_lit.
    rewrite u_add64, u_mul64, !u64_lit by lia. rewrite U9. rewrite !Z.mod_small by lia. lia.
  Qed.

  (** the AT_RANDOM bytes sit [C - 16] above sp *)
  Lemma u_e_atrandom : uE E0 e_atrandom = usp + CHEAD - 16.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof R_range.
    pose proof gap_range. pose proof chead_eq. pose proof bsb_ge. pose proof length_bsb_sum. pose proof lstr_lo. pose proof pad_range.
    destruct uE0_GR as [U8 _].
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
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7). destruct uE0_GR as [U8 U9]. pose proof u_sp8 as US.
    unfold e_atr8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia.
    rewrite US, U3, U4, U8, U9.
    assert (usp / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). pose proof (Z.div_pos usp 8 ltac:(lia) ltac:(lia)).
    rewrite !Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Definition Xsh : Z := argc + envc + 4 * R + G + 2 * ((usp mod 4096) / 16).   (* [comment removed for export] *)
  Lemma Xsh_range : 1 <= Xsh <= 1024 + 256 + 4 + 1 + 510.
  Proof. pose proof len_av. pose proof len_ev. pose proof gap_range. pose proof R_range. unfold Xsh. pose proof usp_decomp as (_ & _ & D3 & _). lia. Qed.
  Lemma u_e_Xsh : uE E0 e_Xsh = Xsh.
  Proof.
    pose proof Xsh_range. pose proof len_av. pose proof len_ev. pose proof gap_range. pose proof R_range. pose proof usp_decomp as (_ & _ & D3 & _).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7). destruct uE0_GR as [U8 U9]. unfold uE in *.
    unfold e_Xsh, Xsh, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot]. cbn [edenot] in U2, U3, U4, U8, U9.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U2, U3, U4, U8, U9.
    assert (Hu : 0 <= usp mod 4096 / 16 < 256).
    { pose proof (Z.mod_pos_bound usp 4096 ltac:(lia)) as B. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    set (u := usp mod 4096 / 16) in *. clearbody u.
    rewrite !Z.mod_small by lia. lia.
  Qed.
  Lemma u_e_Xm : uE E0 e_Xm = (Xsh + 2) - (Xsh + 2) mod 8.
  Proof.
    pose proof Xsh_range. pose proof u_e_Xsh as UX. unfold uE in *.
    unfold e_Xm, eaddz. rewrite !mkAlu_denot, !edenot_lit. rewrite u_and64.
    replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 2 ^ 3)%Z by reflexivity.
    rewrite u_add64, u64_lit by lia. rewrite UX. rewrite Z.mod_small by lia.
    rewrite land_highmask by lia. reflexivity.
  Qed.
  Lemma u_e_atr8m : uE E0 e_atr8m = 4096 * (usp / 32768) + 512 * ((usp mod 32768) / 4096) + ((Xsh + 2) - (Xsh + 2) mod 8).
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof Xsh_range. pose proof (Z.mod_pos_bound (Xsh + 2) 8 ltac:(lia)). pose proof usp_decomp as (_ & D2 & _).
    destruct uE0 as (U1 & _). destruct uE0_PQ as [UP _]. pose proof u_e_Xm as UM. unfold uE in *.
    unfold e_atr8m, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot]. cbn [edenot] in U1, UP, UM. rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, UP, UM.
    assert (usp / 32768 <= 2 ^ 32) by (apply Z.div_le_upper_bound; lia). pose proof (Z.div_pos usp 32768 ltac:(lia) ltac:(lia)).
    rewrite !Z.mod_small by lia. reflexivity.
  Qed.
  Lemma e_atr8m_range : 0xFFFF0000000 <= uE E0 e_atr8m <= 0xFFFFFFFFFC0.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof gap_range. pose proof R_range. pose proof chead_eq. pose proof length_bsb_sum. pose proof pad_range. pose proof lstr_lo.
    pose proof Xsh_range as XR. pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5).
    rewrite u_e_atr8m.
    (* [comment removed for export] *)
    set (s1 := usp / 32768) in *. set (p := (usp mod 32768) / 4096) in *. set (s2 := (usp mod 4096) / 16) in *.
    pose proof (Z.div_mod (Xsh + 2) 8 ltac:(lia)) as D6. pose proof (Z.mod_pos_bound (Xsh + 2) 8 ltac:(lia)) as M6.
    set (m := (Xsh + 2) mod 8) in *. set (xq := (Xsh + 2) / 8) in *. unfold Xsh in *.
    assert (U8 : usp = 8 * (4096 * s1 + 512 * p + 2 * s2)) by lia.
    nia.
  Qed.
  Lemma u_e_vis3b : uE E0 e_vis3b = 32768 * (usp / 32768).
  Proof.
    pose proof usp_lo. pose proof usp_hi. destruct uE0 as (U1 & _). unfold uE in *.
    unfold e_vis3b, escale. rewrite mkMd_denot, edenot_lit, u_mul64, u64_lit by lia. rewrite U1.
    assert (usp / 32768 <= 2 ^ 32) by (apply Z.div_le_upper_bound; lia). pose proof (Z.div_pos usp 32768 ltac:(lia) ltac:(lia)).
    rewrite Z.mod_small by lia. reflexivity.
  Qed.

  (** distances from the pointer arrays to the stack VMA's end *)
  Lemma u_e_blk : uE E0 e_blk0 = utop - (usp + 8 * argc + 8 * envc)
                  /\ uE E0 e_blkL0 = utop - (usp + 8 * argc + 8 * envc) - L0
                  /\ uE E0 e_blkL01 = utop - (usp + 8 * argc + 8 * envc) - L0 - L1
                  /\ uE E0 e_blk08 = (utop - (usp + 8 * argc + 8 * envc)) / 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof pad_range. pose proof bsb_ge.
    pose proof gap_range. pose proof R_range. pose proof chead_eq. pose proof length_bsb_sum. pose proof s01_in_strings. pose proof lstr_hi.
    pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). pose proof PG_range as (P1 & P2 & P3 & P4 & P5 & P6 & QR). pose proof L1_range.
    assert (HL0 : 0 <= L0 <= 131071) by (unfold L0; pose proof (valid_argv_str_len argv 0 Hva Hav0); lia).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7). destruct uE0_PQ as [UP UQ]. pose proof uE0_L1 as UL1. unfold uE in *.
    unfold PGSP, pgdown in P1, P6.
    (* [comment removed for export] *)
    set (s1 := usp / 32768) in *. set (pp := (usp mod 32768) / 4096) in *. set (s2 := (usp mod 4096) / 16) in *.
    clearbody s1 pp s2. hide_lets.
    assert (HB : utop = usp - 16 * s2 + 4096 * Q) by lia.
    assert (HC : 8 * argc + 8 * envc + L0 + L1 + 2 <= utop - usp) by lia.
    unfold e_blkL0, e_blkL01, e_blk0, e_blk08, esub, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, ?mkAlu_denot, !edenot_lit.
    cbn [edenot]. cbn [edenot] in U2, U3, U4, U5, UQ, UL1.
    rewrite ?u_sub64, ?u_mul64, ?u_add64, ?u_mul64, ?u_add64. rewrite !u64_lit by lia. rewrite ?U2, ?U3, ?U4, ?U5, ?UQ, ?UL1.
    clear P4 P5 D5. mod_small_inner.
    assert (E8 : (utop - (usp + 8 * argc + 8 * envc)) / 8 = 512 * Q - 2 * s2 - (argc + envc)) by lia.
    repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma u_e_vis3n : uE E0 e_vis3n = 4096 * ((usp mod 32768) / 4096) + 4096 * Q.
  Proof.
    pose proof usp_decomp as (_ & D2 & _). pose proof PG_range as (_ & _ & _ & _ & _ & _ & QR). destruct uE0_PQ as [UP UQ]. unfold uE in *.
    unfold e_vis3n, eadd, escale. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit, u_add64, !u_mul64, !u64_lit by lia. rewrite UP, UQ.
    assert (HQ : 0 <= 4096 * Q < 2 ^ 64) by lia. assert (HP : 0 <= 4096 * (usp mod 32768 / 4096) < 2 ^ 64) by lia.
    rewrite (Z.mod_small _ _ HQ), (Z.mod_small _ _ HP). rewrite Z.mod_small by lia. reflexivity.
  Qed.
  Lemma u_e_top8 : uE E0 e_top8 = utop / 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_decomp as (D1 & D2 & _). pose proof PG_range as (P1 & _ & P3 & _ & _ & P6 & QR).
    destruct uE0 as (U1 & _). destruct uE0_PQ as [UP UQ]. unfold uE in *.
    unfold e_top8, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot]. cbn [edenot] in U1, UP, UQ.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, UP, UQ.
    assert (usp / 32768 <= 2 ^ 32) by (apply Z.div_le_upper_bound; lia). pose proof (Z.div_pos usp 32768 ltac:(lia) ltac:(lia)).
    rewrite !Z.mod_small by lia. rewrite P6. unfold PGSP, pgdown. lia.
  Qed.
  Lemma u_e_top : uE E0 e_top = utop.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_decomp as (D1 & D2 & _). pose proof PG_range as (P1 & _ & P3 & _ & _ & P6 & QR).
    destruct uE0 as (U1 & _). destruct uE0_PQ as [UP UQ]. unfold uE in *.
    unfold e_top, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot]. cbn [edenot] in U1, UP, UQ.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, UP, UQ.
    assert (usp / 32768 <= 2 ^ 32) by (apply Z.div_le_upper_bound; lia). pose proof (Z.div_pos usp 32768 ltac:(lia) ltac:(lia)).
    rewrite !Z.mod_small by lia. rewrite P6. unfold PGSP, pgdown. lia.
  Qed.

  (** the bytes above the AT_RANDOM block and the string area beyond argv[0] / argv[1] *)
  Lemma u_e_pgslack : uE E0 e_pgslack = utop - (usp + CHEAD)
                      /\ uE E0 e_pgslack8 = (utop - (usp + CHEAD)) / 8
                      /\ uE E0 e_strW0 = LSTR - L0
                      /\ uE E0 e_strW01 = LSTR - L0 - L1.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof pad_range. pose proof bsb_ge.
    pose proof gap_range. pose proof R_range. pose proof chead_eq. pose proof length_bsb_sum. pose proof s01_in_strings. pose proof lstr_hi.
    pose proof pad_eq. pose proof L1_range.
    pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). pose proof PG_range as (P1 & P2 & P3 & P4 & P5 & P6 & QR).
    assert (HL0 : 0 <= L0 <= 131071) by (unfold L0; pose proof (valid_argv_str_len argv 0 Hva Hav0); lia).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7). destruct uE0_PQ as [UP UQ]. destruct uE0_GR as [U8 U9].
    pose proof uE0_L1 as UL1. unfold uE in *.
    unfold PGSP, pgdown in P1, P6.
    (* [comment removed for export] *)
    set (s1 := usp / 32768) in *. set (pp := (usp mod 32768) / 4096) in *. set (s2 := (usp mod 4096) / 16) in *.
    clearbody s1 pp s2. hide_lets.
    unfold e_strW01, e_strW0, e_pgslack, e_pgslack8, esub, eadd, eaddz, escale. rewrite !mkAlu_denot, !mkMd_denot, ?mkAlu_denot, !edenot_lit.
    (* the rseq term [4 * V_R] sits under an ALU node: a second pass exposes it *)
    rewrite ?mkMd_denot, ?mkAlu_denot, ?edenot_lit.
    cbn [edenot]. cbn [edenot] in U2, U3, U4, U5, U6, UQ, U8, U9, UL1.
    (* the rseq term nests one ALU level deeper than the rest: rewrite to a fixpoint *)
    repeat progress rewrite ?u_sub64, ?u_mul64, ?u_add64. rewrite !u64_lit by lia. rewrite ?U2, ?U3, ?U4, ?U5, ?U6, ?UQ, ?U8, ?U9, ?UL1.
    assert (HB : utop = usp - 16 * s2 + 4096 * Q) by lia.
    clear P4 P5 D5. mod_small_inner.
    repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.
  Definition FULL0 : word -> option byte := wrap_mem inp mbase ph entryw sp rdraw.
  (** [Run.init_config]'s model: [State.init_model] at the run stack pointer, with the
      launch's vDSO draw copied in by [State.with_vdso] *)
  Definition model0 : Model :=
    with_vdso (vdso_run_init (ed_vdso rdraw))
      (init_model (segments_reserved segs) brk0 mbase sp LIM inp).

  Let cs0 := init_acs_of R A.
  Let cs0z := init_acs_of_zero R A.   (* [comment removed for export] *)
  Let hid0 := hid A argH0 E0 cs0 model0.
  Let Mr0 := Mr A argH0 E0 cs0 model0 FULL0.

  (** THE LAUNCH'S RESERVED LEDGER is the image's reservations AND the vDSO pair
      ([State.init_reserved]), placed at [State.vdso_top] of the initial ledger *)
  Let VTOP : Z :=
    page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)).
  Let RESX : list (word * word) := vdso_reserved kb VTOP.

  (* [comment removed for export] *)
  Lemma alloc_top0 : alloc_top (m_vmmaps model0) = usp - 8388608.
  Proof. reflexivity. Qed.

  Lemma model0_facts :
    m_halted model0 = None /\ m_fds model0 = fds_std /\ m_tid model0 = None
    /\ vm_reserved (m_vmmaps model0) = segments_reserved segs ++ RESX /\ vm_maps (m_vmmaps model0) = []
    /\ vm_noaccess (m_vmmaps model0) = [] /\ m_vm_lazy model0 = [] /\ m_vm_materialized model0 = []
    /\ vm_limit (m_vmmaps model0) = LIM /\ vm_brk (m_vmmaps model0) = brk0 /\ vm_start_brk (m_vmmaps model0) = brk0
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

  (* [comment removed for export] *)
  Lemma hid0_eq : forall a : word, hid0 a = (argH0 E0 a || negb (APS.in_hull A (bv_unsigned a) || (usp - 8388608 <=? bv_unsigned a)))%bool.
  Proof.
    intros a. unfold hid0, hid, vis. rewrite alloc_top0. destruct model0_facts as (_&_&_&_&Hm&Hn&Hl&_). rewrite Hm. cbn [in_ivs existsb andb].
    rewrite orb_false_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
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

  (* ----------------------------------------------------------------------- *)
  (** ** The four AsanPlanSound hypotheses about SINV/argH                    *)
  (* ----------------------------------------------------------------------- *)

  Lemma argH0_high : forall E a, argH0 E a = true -> CEIL <= bv_unsigned a /\ usp <= bv_unsigned a.
  Proof.
    intros E a H. unfold argH0 in H. destruct Hsp as [Hlo _]. unfold sp_window_lo in Hlo. unfold CEIL.
    pose proof len_av. pose proof len_ev. pose proof chead_range. pose proof pad_range.
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H _]; apply Z.leb_le in H; unfold usp, argc, envc, STR0 in *; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma NX0_spw : AP.expr_vars_lt NX0 e_spw = true.
  Proof. reflexivity. Qed.

  Lemma argH0_agree : forall E E' a, env_agree NX0 E E' -> argH0 E a = argH0 E' a.
  Proof. reflexivity. Qed.

  Lemma SINV0_frame : forall E M M', (forall a, argH0 E a = true -> M' a = M a) -> SINV0 E M -> SINV0 E M'.
  Proof. intros E M M' Hf [H1 H2]. split; [exact H1|]. intros a Ha. rewrite (Hf a Ha). apply H2. exact Ha. Qed.

  Lemma SINV0_agree : forall E E' M, env_agree NX0 E E' -> SINV0 E M -> SINV0 E' M.
  Proof.
    intros E E' M [Hag _] [H1 H2]. split; [|exact H2]. intros n Hn. rewrite <- (Hag n) by (unfold NX0 in *; lia). apply H1. exact Hn.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (** ** The knowledge [init_kn A] holds                                       *)
  (* ----------------------------------------------------------------------- *)

  Lemma argH0_range : forall a : word, argH0 E0 a = true ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 8 * envc + 24
    \/ STR0 <= bv_unsigned a < utop.
  Proof.
    intros a H. unfold argH0 in H.
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; [left|right]; lia.
  Qed.

  (** the VISIBLE part of the block: argc, the argv pointers and their NULL, the auxv,
      the gap, the sixteen random bytes and the [arch_align_stack] pad *)
  Lemma not_argH0 : forall a : word,
    (bv_unsigned a < usp + 8 * argc + 16 \/ (usp + 8 * argc + 8 * envc + 24 <= bv_unsigned a < STR0)
     \/ utop <= bv_unsigned a) -> argH0 E0 a = false.
  Proof.
    intros a H. destruct (argH0 E0 a) eqn:Ha; [|reflexivity]. apply argH0_range in Ha.
    pose proof len_av. pose proof len_ev. pose proof chead_eq. pose proof pad_range. pose proof R_range.
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

  Let AUXW := auxv_words la ph entryw uid (in_gid inp) hw
                (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn).
  (** The vector's pair count, as the two kernel builds give it: 27 pairs (432 bytes)
      without CONFIG_RSEQ and 29 (464) with it.  Both branches are discharged here, so
      every bound below is stated over the RUN's own flag and pins no kernel field. *)
  Lemma auxv_count_R : (auxv_count (kb_rseq (in_kernel inp)) = 27 + 2 * Z.to_nat R)%nat.
  Proof. unfold R, rseq, kb. destruct (kb_rseq (in_kernel inp)); cbn; reflexivity. Qed.

  Lemma auxv_count_lt : forall j : nat,
    (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat -> (j < 58)%nat.
  Proof. intros j Hj. pose proof R_range. pose proof auxv_count_R. lia. Qed.

  (** EVERY pair of the vector, both kernel builds: the bound was [j < 52] -- pairs 0..25,
      the ones that sit at the same place under both builds -- and the auxv tail
      (CONFIG_RSEQ's two pairs and AT_NULL) lies past it.  [read_auxv_word] already
      answers for every [j < 2 * auxv_count (kb_rseq (in_kernel inp))], so widening the
      hypothesis to the model's own bound costs only the numeric bound below. *)
  Lemma auxv_word_ok : forall (j : nat) v,
    (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat ->
    nth j AUXW (Z_to_bv 64 0) = edenot E0 v ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 v).
  Proof.
    intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    (* the address arithmetic below needs the EXACT bound, not a crude one: at
       [R = 0] the vector is 54 words, so [j <= 53], two words past the old [j < 52],
       and the block-length bound is tight.  Measured: a plain [j < 58] leaves the
       third bullet's [lia] with "Cannot find witness" (measured on openssl/pem's copy
       of this file). *)
    pose proof auxv_count_R as HCR. pose proof R_range as HRr.
    assert (Hj58 : (j < 58)%nat) by lia.
    assert (Hjz : Z.of_nat j <= 53 + 4 * R) by lia.
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
      pose proof (read_auxv_word segs Sv48 inp mbase ph entryw sp brk0 rdraw) as RW. inst_hyps RW.
      exact (RW j Hj).
  Qed.

  (** [i <= 26 + 2 * R] is [auxv_count - 1], the LAST pair of the run's own vector: the
      bound was 25 while pairs 26-28 were unclaimed, and the auxv tail claims them. *)
  Lemma auxw_ok : forall i ty v,
    (0 <= i <= 26 + 2 * R) ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    nth (Z.to_nat (2 * i + 1)) AUXW (Z_to_bv 64 0) = edenot E0 v ->
    know_ok segs E0 Mr0 (auxw i ty v).
  Proof.
    intros i ty v Hi H1 H2. unfold auxw.
    pose proof R_range. pose proof auxv_count_R as HC.
    constructor; [|constructor; [|constructor]].
    - replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia. apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
    - replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia. apply auxv_word_ok; [lia|]. exact H2.
  Qed.

  (** WHY THERE IS NO [kunk_of_word]: IT WOULD BE FALSE, NOT MERELY UNPROVED.
      [kentry_ok]'s [KWord] arm (AxSymExec3Sound.v:655-659) states
      [rdn segs base (adenot E a) w = Some …], and [rdn] reads through [rd1], whose body
      falls back to the segment ROM when the base map answers [None] (visible in
      [rdn_rd1]'s proof, :6141-6148).  [KUnk]'s obligation is
      [forall i, … -> base (Z_to_bv 64 (estart E a + i)) <> None] - the BASE MAP, with no
      fallback.  So a word readable through ROM over an undefined base satisfies [KWord]
      and refutes [KUnk], and [rdn_rd1] gives only the weaker [rd1 … <> None].
      The three siblings that DO hold - [kunk_of_zero], [kunk_of_fill], [kunk_of_blob]
      (:7553-7561) - each start from a hypothesis of the form [base (…) = Some …].
      [KWord] is the one member of that family whose fact is about [rdn], which is exactly
      what makes a fourth sibling look safe.
      So the value word is proved at the MEMORY level instead, where the base map answers. *)

  (** [FULL0] answers inside the entry image: [wrap_mem]'s first arm is
      [stack_to_mem sp bsb] (Common/PropExec.v:2644-2656), which returns
      [nth_error bsb off] whenever [sp <= addr] and [off < length bsb]. *)
  Lemma FULL0_block : forall a : word,
    usp <= bv_unsigned a -> bv_unsigned a < usp + Z.of_nat (length bsb) -> FULL0 a <> None.
  Proof.
    intros a Hlo Hhi.
    assert (Hs : exists b, stack_to_mem sp bsb a = Some b).
    { unfold stack_to_mem. cbv zeta.
      (* [rewrite (proj2 (Z.leb_le _ _) ltac:(... lia))] does NOT work here and its failure
         is misleading: the two [_]s are still evars when the [ltac:] runs, so [lia] is
         handed [?x <= ?y] and the error reads as arithmetic about [sp] when it is a
         failure to instantiate.  [replace ... with true by (symmetry; apply Z.leb_le; ...)]
         is the idiom [FULL0_below] two lemmas above already uses, and it names both sides. *)
      replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with true
        by (symmetry; apply Z.leb_le; unfold usp in *; lia).
      replace (Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length bsb))) with true
        by (symmetry; apply Z.ltb_lt; unfold usp in *; lia).
      destruct (nth_error bsb (Z.to_nat (bv_unsigned a - bv_unsigned sp))) as [b|] eqn:Hn.
      - exists b. reflexivity.
      - exfalso. apply (proj1 (nth_error_None bsb _)) in Hn. unfold usp in *; lia. }
    destruct Hs as [b Hb]. unfold FULL0, wrap_mem. fold bsb. rewrite Hb. discriminate.
  Qed.

  (** [kword_stack]'s hypotheses, a [KUnk] conclusion.  Same route to [Mr0]
      ([Mr0_visible] then [FULL0]), but stopping at "the base map answers" rather than
      naming the value, because the plan's claim list may not mention [inp]. *)
  Lemma kunk_stack : forall b k (w : word),
    bv_unsigned (edenot E0 b) + k = bv_unsigned w ->
    usp <= bv_unsigned w -> bv_unsigned w + 8 <= usp + Z.of_nat (length bsb) ->
    (forall x : word, bv_unsigned w <= bv_unsigned x < bv_unsigned w + 8 -> argH0 E0 x = false) ->
    kentry_ok segs E0 Mr0 (KUnk (SA b k) (ELit 8)).
  Proof.
    intros b k w Hw Hlo Hhi Hvis. pose proof usp_fit. pose proof usp_lo. pose proof (u64_range w).
    cbn [kentry_ok]. rewrite elenZ_lit by lia.
    assert (Hfl : flat E0 (SA b k) 8) by (unfold flat, estart; cbn [a_base a_off]; lia).
    split; [exact Hfl|].
    intros i Hi.
    assert (Hx : bv_unsigned (Z_to_bv 64 (estart E0 (SA b k) + i)) = bv_unsigned w + i).
    { unfold estart; cbn [a_base a_off]. rewrite Hw. rewrite u_small by lia. reflexivity. }
    rewrite Mr0_visible.
    - apply FULL0_block; rewrite Hx; lia.
    - rewrite Hx. lia.
    - apply Hvis. rewrite Hx. lia.
  Qed.

  (** the readability of ONE auxv word, at the same addresses [auxv_word_ok] covers.
      WORD unit, and the same widening: the bound was [j < 52] = [2 x 26], i.e. pairs
      0-25, while the auxv tail lies past it. *)
  Lemma auxv_unk_ok : forall (j : nat), (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat ->
    kentry_ok segs E0 Mr0 (KUnk (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) (ELit 8)).
  Proof.
    intros j Hj. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    (* the exact bound, as in [auxv_word_ok]: [j <= 53 + 4 * R], not a crude [j < 58] *)
    pose proof auxv_count_R as HCR. pose proof R_range as HRr.
    assert (Hj58 : (j < 58)%nat) by lia.
    assert (Hjz : Z.of_nat j <= 53 + 4 * R) by lia.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof R_range.
    pose proof lstr_lo. pose proof bsb_ge.
    assert (Hab : split_lit e_auxv = (fst e_auxb, snd e_auxb)) by (unfold e_auxb; destruct (split_lit e_auxv); reflexivity).
    set (ab := fst e_auxb) in *. set (ak := snd e_auxb) in *.
    pose proof (split_u E0 e_auxv ab ak Hab) as Hs. rewrite u_e_auxv in Hs.
    assert (Hak : ak = 24) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    apply (kunk_stack ab (ak + 8 * Z.of_nat j) (sp + nat_to_word (auxv_off argv envp + 8 * j))%bv).
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold auxv_off, usp in *; [|lia].
      rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul in Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. unfold STR0. lia.
  Qed.

  (** [auxk]'s obligation.  The KEY word is [auxw_ok]'s first conjunct unchanged; the
      VALUE word is [auxv_unk_ok] - present and readable, value unnamed.  Same widened
      bound as [auxw_ok]: [26 + 2 * R] is the run's own last pair. *)
  Lemma auxk_ok : forall i ty,
    (0 <= i <= 26 + 2 * R) ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    know_ok segs E0 Mr0 (auxk i ty).
  Proof.
    intros i ty Hi H1. unfold auxk.
    pose proof R_range. pose proof auxv_count_R as HC.
    constructor; [|constructor; [|constructor]].
    - replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia.
      apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
    - replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia.
      apply auxv_unk_ok. lia.
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

  (** argv[1] follows argv[0]'s bytes and NUL *)
  Lemma cat_argv1_eq : (1 < length argv)%nat ->
    bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1) = STR0 + L0 + 1.
  Proof.
    intros Hav1.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof R_range.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof chead_range.
    pose proof s0_in_strings. pose proof lstr_hi.
    assert (TF : forall l : list (list byte), (0 < length l)%nat ->
                  Z.of_nat (total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1)
      by (intros [|x t] Hl; [cbn in Hl; lia|]; change (firstn 1 (x :: t)) with [x]; cbn -[Z.of_nat Z.add]; lia).
    pose proof (TF argv Hav0) as TF0.
    rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1 Hav1).
    rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
    change (in_argv inp) with argv. change (in_envp inp) with envp. change (in_execfn inp) with execfn.
    change (kb_rseq (in_kernel inp)) with rseq.
    unfold STR0, CHEAD, W, usp, top, L0, cat_string_off in *.
    rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia.
  Qed.

  Lemma uE0_argc : uE E0 (EVar V_ARGC) = argc.
  Proof. destruct uE0 as (_ & _ & H & _). exact H. Qed.

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

  (* [comment removed for export] *)
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

  (** the sixteen AT_RANDOM bytes: through [Mr0] they are the raw image's, at [C - 16] above sp *)
  Lemma atrandom_bytes : forall i, 0 <= i < 16 ->
    Mr0 (Z_to_bv 64 (usp + CHEAD - 16 + i))
    = Some (nth (Z.to_nat i) (at_random_bytes (ed_random rdraw)) (Z_to_bv 8 0)).
  Proof.
    intros i Hi.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge. pose proof R_range.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof lstr_lo.
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

  Lemma atrb_start : estart E0 (SA (fst e_atrb) (snd e_atrb)) = usp + CHEAD - 16.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof chead_range. pose proof length_bsb_sum. pose proof pad_range. pose proof lstr_lo.
    assert (Hab : split_lit e_atrandom = (fst e_atrb, snd e_atrb)) by (unfold e_atrb; destruct (split_lit e_atrandom); reflexivity).
    set (ab := fst e_atrb) in *. set (ak := snd e_atrb) in *.
    pose proof (split_u E0 e_atrandom ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    assert (Hak : 0 <= ak <= 456) by (subst ak; vm_compute; split; discriminate).
    specialize (Hs ltac:(lia) ltac:(lia)).
    unfold estart; cbn [a_base a_off]. lia.
  Qed.

  (** THE DEFAULT: the AT_RANDOM block is byte string [K_RND] = the draw (faithful, no hypothesis) *)
  Lemma atrandom_ok : kentry_ok segs E0 Mr0 (KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof chead_range. pose proof length_bsb_sum. pose proof pad_range. pose proof lstr_lo.
    pose proof atrb_start as Hst.
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl.
    assert (HE : eb E0 K_RND = at_random_bytes (ed_random rdraw)) by (unfold E0; cbn [eb]; rewrite Nat.eqb_refl; reflexivity).
    rewrite HE.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    split; [rewrite length_at_random_bytes; reflexivity|].
    intros i Hi. exact (atrandom_bytes i Hi).
  Qed.

  (* [comment removed for export] *)
  Lemma atrandom_zero_ok : kentry_ok segs E0 Mr0 (KZero (SA (fst e_atrb) (snd e_atrb)) (ELit 16)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof chead_range. pose proof length_bsb_sum. pose proof pad_range. pose proof lstr_lo.
    pose proof atrb_start as Hst.
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    intros i Hi. rewrite (atrandom_bytes i Hi).
    pose proof Hzr as Hz0. unfold AsanCeil.zero_random_draw in Hz0.
    rewrite Hz0, AsanCeil.at_random_bytes_zero. rewrite nth_repeat. reflexivity.
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

  (** THE AUXV TAIL, at the run's OWN flag.  One case split on [kb_rseq (in_kernel inp)],
      both branches discharged, so no kernel field is pinned: at [false] the vector is 27
      pairs and pair 26 is AT_NULL; at [true] it is 29, pairs 26-27 are
      AT_RSEQ_FEATURE_SIZE and AT_RSEQ_ALIGN -- claimed with their VALUES, the model's own
      literals 28 and 32 ([AsanPlanCore.init_kn_tail], which carries the reason: a [KUnk]
      value word is read as an unknown and allocates a fresh variable, which put the two
      kernel builds in different numberings at the level-0 hand-off) -- and AT_NULL is
      pair 28.  Factored out of [init_kn_with_ok] so the split does not run through the
      whole knowledge list.  All three groups are now [auxw], so the [first [auxk_ok |
      auxw_ok]] dispatch below selects the same branch for each; it is left as a [first]
      because the shape, not the count, is what it dispatches on. *)
  Lemma init_kn_tail_ok : know_ok segs E0 Mr0 (init_kn_tail R).
  Proof.
    pose proof R_range. pose proof auxv_count_R as HC.
    unfold init_kn_tail, R, rseq, kb.
    destruct (kb_rseq (in_kernel inp)) eqn:HKB; cbn [rseq_z Z.eqb Z.mul Z.add].
    (* [all:] rather than bullets, so BOTH flag branches get the same script and a
       leftover in either one is reported by the dump below instead of as a bullet
       error.  The obligations [auxw_ok]/[auxk_ok] name [AUXW], whose body reaches the
       flag through the Section's [rseq] and [kb], not through the
       [kb_rseq (in_kernel inp)] that [destruct] rewrote in the goal, so both must be in
       the unfold list or [cbn] cannot pick the [auxv_entries] branch. *)
    all: repeat (apply Forall_app; split).
    all: try (first [ apply auxk_ok | apply auxw_ok ];
              [ unfold R, rseq, kb; rewrite HKB; cbn [rseq_z]; lia
              | unfold AUXW, auxv_words, auxv_entries, rseq, kb; rewrite ?HKB;
                cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul rseq_z];
                try reflexivity .. ]).
    all: try (rewrite edenot_lit; reflexivity).
    all: try reflexivity.
    (* the tail's pair index arrives as [Z.to_nat (2 * 26)] (and [Z.to_nat (2 * 28)] in
       the [true] branch) rather than a numeral, so the [nth] match above stays stuck on
       a fully built row list (measured on openssl/pem's copy of this file).  A whole-goal
       [vm_compute] here does settle it but forces the entire auxv image, which ran out of
       memory at 20 GiB there.  So compute the
       INDEX ALONE -- a one-constructor [Z.to_nat] of a closed product -- and let [cbn]
       select the row; the row's own value (hw, la_*, entryw) stays opaque and
       unchanged. *)
    all: try (match goal with
              | |- context[Z.to_nat ?x] =>
                  let v := eval vm_compute in (Z.to_nat x) in change (Z.to_nat x) with v
              end).
    (* and the row list's own tail is guarded by [la_rseq la], NOT by the
       [kb_rseq (in_kernel inp)] the [destruct] rewrote: [la] is [launch_auxv inp sp mbase]
       and [Run.launch_auxv] copies the flag straight out of the kernel build, so the two
       spellings are convertible ([PropExec.la_rseq_launch_auxv], and the same [change]
       AsanNodesStartX.v:149 already uses).  That guard is why the arms stayed unreduced
       even where the index was a numeral (measured on openssl/pem's copy of this file). *)
    all: try (unfold la).
    all: try (change (la_rseq (launch_auxv inp sp mbase)) with (kb_rseq (in_kernel inp));
              rewrite HKB).
    all: try (cbn [nth flat_map app fst snd]).
    all: try reflexivity.
    all: try (rewrite edenot_lit; reflexivity).
    all: try (cbn; reflexivity).
    all: try apply Forall_nil.
  Qed.

  Lemma init_kn_with_ok : forall atr, kentry_ok segs E0 Mr0 atr -> know_ok segs E0 Mr0 (init_kn_with R atr A).
  Proof.
    intros atr Hatr.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof gap_range. pose proof R_range. pose proof chead_eq. pose proof length_bsb_sum. pose proof lstr_lo.
    pose proof lstr_hi. pose proof s01_in_strings. pose proof L1_range.
    pose proof brk_range as [B1 B2]. pose proof bsb_ge. pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    pose proof (if_ph _ _ _ IMG) as (P1 & P2 & P3).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7). destruct uE0_GR as [U8 U9].
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    unfold init_kn_with.
    destruct stack_window_ok as [SW1 SW2].
    apply Forall_app; split.
    { pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). pose proof PG_range as (G1 & G2 & G3 & G4 & G5 & G6 & QR). destruct uE0_PQ as [UP UQ].
      unfold PGSP, pgdown in G1, G6.
      pose proof u_e_blk as (UB1 & UB2 & UB3 & UB4). pose proof u_e_pgslack as (US1 & US2 & US3 & US4).
      pose proof e_atr8m_range as AR. pose proof u_e_atr8 as UA8. pose proof u_e_top8 as UT8. pose proof u_e_top as UT.
      pose proof u_e_sp0 as USP. pose proof u_sp8 as US8. pose proof u_e_atrandom as UAR.
      (* [comment removed for export] *)
      set (s1 := usp / 32768) in *. set (pp := (usp mod 32768) / 4096) in *. set (s2 := (usp mod 4096) / 16) in *.
      clearbody s1 pp s2. hide_lets.
      clear D5.
      apply Forall_cons; [apply kr_ok; rewrite U1; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U2; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UP; lia|].   (* [comment removed for export] *)
      apply Forall_cons; [apply kr_ok; rewrite UQ; lia|].   (* [comment removed for export] *)
      apply Forall_cons; [apply kr_ok; unfold eaddz, uE; rewrite mkAlu_denot, edenot_lit, u_add64, u64_lit by lia;
                          unfold uE in UAR; rewrite UAR; rewrite Z.mod_small by lia; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UA8; lia|].
      apply Forall_cons; [apply kr_ok; lia|].   (* [comment removed for export] *)
      apply Forall_cons; [apply kr_ok; rewrite US1; lia|].
      apply Forall_cons; [apply kr_ok; rewrite US2; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UT8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UT; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UB3; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UB2; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UB1; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UB4; lia|].
      apply Forall_cons; [apply kr_ok; rewrite US4; lia|].
      apply Forall_cons; [apply kr_ok; rewrite US3; lia|].
      apply Forall_cons; [apply kr_ok; rewrite USP; lia|].
      apply Forall_cons; [apply kr_ok; rewrite US8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U3; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U4; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U5; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_L1; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_uid; unfold valid_id in Huid; pose proof (u64_range uid); lia|].
      apply Forall_cons; [apply kr_ok; change (uE E0 (EVar V_HW)) with (bv_unsigned hw); pose proof (u64_range hw); lia|].   (* [comment removed for export] *)
      apply Forall_cons; [apply kr_ok; rewrite U8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U9; lia|].
      (* the new [V_GID] row sits between [V_R] and [V_W] in [init_kn_with]'s list, so it
         needs its own bullet here -- the ladder is POSITIONAL, and a missing bullet shows as
         "Found no subterm matching uE E0 (EVar V_W)" at the [V_W] bullet, one row early.  [change] rather than a
         [rewrite] through a named lemma, the V_HW row's idiom one line above: it closes by
         CONVERSION, and the claim is the full word range, which every [word] satisfies,
         so no [valid_id] premise is needed anywhere.  (The walk reads AT_GID and AT_EGID
         only to compare them, and both are the same [EVar V_GID]; it never needs the
         value bounded.) *)
      apply Forall_cons; [apply kr_ok; change (uE E0 (EVar V_GID)) with (bv_unsigned gid); pose proof (u64_range gid); lia|].
      apply Forall_cons; [apply kr_ok; rewrite U6; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U7; unfold BRK_ASLR in *; lia|].
      apply Forall_cons; [exact SW1|].
      apply Forall_cons; [exact SW2|].
      apply Forall_cons; [exact argc_word_ok|].
      apply Forall_cons; [exact argv0_word_ok|].
      apply Forall_cons; [exact argv1_word_ok|].
      apply Forall_nil. }
    (* SEAL THE TAIL BEFORE SPLITTING.  [init_kn_tail R] is
       [(if r =? 0 then [] else auxw 26 27 (ELit 28) ++ auxw 27 28 (ELit 32))
          ++ auxw (26 + 2*r) 0 (ELit 0)],
       and [apply Forall_app] unfolds through a transparent Definition, so the plain
       [repeat (apply Forall_app; split)] SPLIT THE TAIL and left two goals at the
       symbolic index [Z.to_nat (2 * (26 + 2 * R))] that no [vm_compute] can settle
       (measured on openssl/pem's copy of this file).
       [clearbody] makes the tail a variable, so the split stops at it and the one lemma
       that owns the flag case ([init_kn_tail_ok]) closes it whole. *)
    assert (HTL : know_ok segs E0 Mr0 (init_kn_tail R)) by exact init_kn_tail_ok.
    set (TL := init_kn_tail R) in *. clearbody TL.
    repeat (apply Forall_app; split).
    all: try exact HTL.
    (* [1-9:] addressed the nine auxw groups POSITIONALLY, so the seventeen added groups
       shift every bullet below it and the failure surfaces four lines down at [exact Hatr]
       rather than here.  Dispatch by the goal's own shape instead, which is independent of
       how many groups there are: [auxk_ok] for a key-only group, [auxw_ok] for a full one.
       [try] because the non-auxv groups fall through to the bullets below unchanged.
       Shape ported from the same donor, :1242-1253. *)
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
    (* AT_ENTRY's value word is the one row the ladder above leaves: its index arrives as
       [Z.to_nat (2 * 18 + 1)] rather than a numeral, so the row list stays unselected --
       the same stuck scrutinee [init_kn_tail_ok] hit (the goal is a 100-arm match ending in
       [= edenot E0 (ELit (a_entry A))]).  Normalise the INDEX ALONE, never the whole goal:
       a whole-goal [vm_compute] forces the auxv image.  The selected row is [entryw], which is
       [Z_to_bv 64 (Z.of_N apc)], and [Hapc] says [Z.of_N apc = a_entry A]. *)
    all: try (match goal with
              | |- context[Z.to_nat ?x] =>
                  let v := eval vm_compute in (Z.to_nat x) in change (Z.to_nat x) with v
              end;
              cbn [nth flat_map app fst snd];
              first [ reflexivity
                    | rewrite edenot_lit; reflexivity
                    | rewrite edenot_lit; unfold entryw; rewrite Hapc; reflexivity
                    | unfold entryw; rewrite edenot_lit, Hapc; reflexivity
                    | unfold entryw; rewrite Hapc, edenot_lit; reflexivity ]).
    apply Forall_cons; [exact Hatr|].
    apply Forall_cons; [exact kimg_ok|].
    apply Forall_cons; [exact rw_window_ok|].
    apply Forall_nil.
  Qed.

  Lemma init_kn_ok : know_ok segs E0 Mr0 (init_kn R A).
  Proof. exact (init_kn_with_ok _ atrandom_ok). Qed.
  (* [comment removed for export] *)
  Lemma init_kn_zero_ok : know_ok segs E0 Mr0 (init_kn_zero R A).
  Proof. exact (init_kn_with_ok _ atrandom_zero_ok). Qed.

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

  (* [comment removed for export] *)
  Lemma u_e_stkw : uE E0 (eaddz e_pgsp (-8388608)) = PGSP - 8388608
                   /\ uE E0 (eadd (ELit 8388608) (escale 16 (EVar V_S2))) = 8388608 + usp mod 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). pose proof u_e_pgsp as U. destruct uE0 as (_ & U2 & _).
    unfold uE in U, U2 |- *. unfold PGSP, pgdown. split.
    - unfold eaddz. rewrite mkAlu_denot, edenot_lit, u_add64.
      rewrite U. rewrite u_lit64. change ((-8388608) mod two64) with (two64 - 8388608). unfold two64.
      pose proof (Z.mod_pos_bound usp 4096 ltac:(lia)). lia.
    - unfold eadd, escale. rewrite mkAlu_denot, mkMd_denot, !edenot_lit, u_add64, u_mul64, !u64_lit by lia. rewrite U2.
      rewrite !Z.mod_small by lia. lia.
  Qed.

  (** the initial image's length: [top - sp] *)
  Lemma u_en_blk : uE E0 en_blk = Z.of_nat (length bsb).
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). pose proof PG_range as (P1 & P2 & P3 & P4 & P5 & P6 & QR).
    destruct uE0 as (_ & U2 & _). destruct uE0_PQ as [_ UQ]. unfold uE in U2, UQ |- *.
    unfold PGSP, pgdown in P1, P6.
    unfold en_blk, esub, escale. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit, u_sub64, !u_mul64, !u64_lit by lia. rewrite U2, UQ.
    rewrite (Z.mod_small (4096 * Q)) by lia. rewrite (Z.mod_small (16 * _)) by lia. rewrite Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Definition N2 : Z := 8388608 + usp mod 4096.
  Definition P3 : Z := 32768 * (usp / 32768).
  Definition N3 : Z := 4096 * ((usp mod 32768) / 4096) + 4096 * Q.
  Lemma PN3_range : usp - 32768 < P3 <= usp /\ P3 + N3 = utop /\ 4096 <= N3 <= 32768 + 4096 * 600 /\ 8388608 <= N2 < 8388608 + 4096
                    /\ PGSP - 8388608 + N2 = usp.
  Proof.
    pose proof usp_lo. pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). pose proof PG_range as (P1 & P2 & P3' & P4 & P5 & P6 & QR). unfold P3, N3, N2.
    pose proof (Z.div_mod usp 32768 ltac:(lia)). pose proof (Z.mod_pos_bound usp 32768 ltac:(lia)). pose proof (Z.mod_pos_bound usp 4096 ltac:(lia)).
    unfold PGSP, pgdown in *. lia.
  Qed.
  Lemma allowA_init : allowA A E0 cs0 =
    [(pagedown (img_lo A), pageup (img_lo A + (img_hi A - img_lo A)));
     (pagedown (shadow_off A + img_lo A / 8), pageup (shadow_off A + (img_lo A + (img_hi A - img_lo A)) / 8));
     (pagedown (PGSP - 8388608), pageup (PGSP - 8388608 + N2));
     (pagedown (shadow_off A + (PGSP - 8388608) / 8), pageup (shadow_off A + (PGSP - 8388608 + N2) / 8));
     (pagedown P3, pageup (P3 + N3));
     (pagedown (shadow_off A + P3 / 8), pageup (shadow_off A + (P3 + N3) / 8))].
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof u_e_stkw as [US UN2]. pose proof u_e_vis3b as UB. pose proof u_e_vis3n as UN. pose proof u_e_sp0 as USP.
    unfold allowA, cs0, init_acs_of, init_acs_of_with, init_vis. cbn [a_vis a_ghost app flat_map allow1 fst snd].
    unfold sh_lo, sh_hi. cbn [fst snd]. rewrite US, UN2. rewrite UB, UN. fold N2. fold P3. fold N3.
    unfold uE. rewrite !edenot_lit, !u64_lit by lia. unfold N2. reflexivity.
  Qed.

  Lemma abytes_init : A_bytes (allowA A E0 cs0) <= vis_cost (img_hi A - img_lo A) + vis_cost 8392704 + vis_cost 4194304
                      /\ vis_cost (img_hi A - img_lo A) + vis_cost 8392704 + vis_cost 4194304 <= LIM.
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof (if_shadow _ _ _ IMG) as S1. pose proof usp_lo as UL.
    pose proof PG_range as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & QR). pose proof PN3_range as (PR & PE & NR & NR2 & NE).
    rewrite allowA_init. cbn [A_bytes fst snd]. unfold vis_cost. pose proof HLIM as HL; unfold LIM_MIN in HL.
    replace (img_lo A + (img_hi A - img_lo A)) with (img_hi A) by lia.
    assert (P1 : forall z, z mod 4096 = 0 -> pagedown z = z) by (intros z Hz; unfold pagedown; lia).
    assert (P2 : forall z, z mod 4096 = 0 -> pageup z = z) by (intros z Hz; unfold pageup; lia).
    rewrite (P1 (img_lo A) I3), (P2 (img_hi A) I4). clear P1 P2.
    (* [comment removed for export] *)
    hide_lets.
    clear - I1 I2 I3 I4 S1 UL Q3 PR PE NR NR2 NE HL.
    pose proof (pageup_minus_pagedown (shadow_off A + img_lo A / 8) (shadow_off A + img_hi A / 8) ltac:(lia)) as M1.
    pose proof (pageup_minus_pagedown (PGSP - 8388608) (PGSP - 8388608 + N2) ltac:(lia)) as M2.
    pose proof (pageup_minus_pagedown (shadow_off A + (PGSP - 8388608) / 8) (shadow_off A + (PGSP - 8388608 + N2) / 8) ltac:(lia)) as M3.
    pose proof (pageup_minus_pagedown P3 (P3 + N3) ltac:(lia)) as M4.
    pose proof (pageup_minus_pagedown (shadow_off A + P3 / 8) (shadow_off A + (P3 + N3) / 8) ltac:(lia)) as M5.
    split; lia.
  Qed.

  (** the ledger at the launch: the image's reservations and the launch's vDSO pair;
      no tracked maps; the pair is the one [State.init_reserved] appended *)
  Lemma co_res_init :
    (exists rx : list (word * word),
        vm_reserved (m_vmmaps model0) = segments_reserved segs ++ rx
        /\ Forall (resx_entry_ok A) rx /\ (length rx <= n_resx A)%nat /\ sum_sizes rx <= resx_bytes A)
    /\ Forall (fun iv => Forall (iv_disjoint iv) (vm_reserved (m_vmmaps model0))) (vm_maps (m_vmmaps model0))
    /\ incl (vdso_reserved (m_kernel model0) (vdso_top (m_vmmaps model0))) (vm_reserved (m_vmmaps model0)).
  Proof.
    pose proof (if_resx _ _ _ IMG) as [RX1 RX2]. pose proof resx_bytes_lo.
    pose proof (vdso_len_bounds kb).
    split; [|split].
    - exists RESX. split; [reflexivity|].
      split; [exact resx_ok|]. split; [pose proof resx_len; lia | rewrite resx_sum; unfold page_size in *; lia].
    - constructor.
    - replace (m_kernel model0) with kb by reflexivity.
      replace (vdso_top (m_vmmaps model0)) with VTOP
        by (symmetry; exact (vdso_top_init_model (segments_reserved segs) brk0 mbase sp LIM inp)).
      apply incl_appr, incl_refl.
  Qed.

  Lemma totsz_init : sum_sizes ((segments_reserved segs ++ RESX) ++ []) <= img_hi A - img_lo A + resx_bytes A.
  Proof.
    pose proof (vdso_len_bounds kb). pose proof resx_bytes_lo.
    rewrite app_nil_r, sum_sizes_app, (if_sizes _ _ _ IMG), resx_sum. unfold page_size in *. lia.
  Qed.

  Theorem init_cs_ok : cs_ok segs A LIM SINV0 argH0 usp (in_fs inp) E0 cs0 R0 FULL0 model0.   (* [comment removed for export] *)
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
    destruct abytes_init as [AB1 AB2].
    pose proof co_res_init as CR. pose proof totsz_init as TS.
    constructor; cbn [cs0 init_acs_of init_acs_of_with a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
      rewrite ?M1, ?M2, ?M3, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
    - exact init_regs_ok.
    - reflexivity.
    - exact init_kn_ok.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros _; reflexivity.
    - first [exact CR | (rewrite M5 in CR; exact CR)].
    - reflexivity.
    - first [reflexivity | exact I | constructor].
    - constructor.   (* [comment removed for export] *)
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      exact (init_sp_ok_init_model (segments_reserved segs) brk0 mbase sp LIM inp Hsp).  (* [comment removed for export] *)
    - constructor.
    - constructor.
    - intros z Hz. exact Hz.
    - constructor.
    - constructor.
    - rewrite M4. exact TS.
    - constructor.   (* [comment removed for export] *)
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.
    - lia.
    - lia.
    - exact AB1.
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
    - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
    - split; [intros; reflexivity | intros; reflexivity].
    - (* [comment removed for export] *) split; [reflexivity | exact u_e_spw].
    - (* [comment removed for export] *) pose proof usp_lo. pose proof usp_fit. rewrite alloc_top0. unfold CEIL, TOPMAX. lia.
    - (* [comment removed for export] *) intros _; first [exact M7 | reflexivity].
    - (* [comment removed for export] *) intros iv Hiv _. rewrite ?M7 in Hiv. destruct Hiv.
    - (* [comment removed for export] *) rewrite ?M6. apply Forall_nil.
    - (* the reader: [State.init_model] copies [in_channel_reader] *) exact Hrdr.
  Qed.

  (* [comment removed for export] *)
  Theorem init_cs_ok_zero : cs_ok segs A LIM SINV0 argH0 usp (in_fs inp) E0 cs0z R0 FULL0 model0.   (* [comment removed for export] *)
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
    destruct abytes_init as [AB1 AB2].
    change (allowA A E0 cs0) with (allowA A E0 (init_acs_of_zero R A)) in AB1.   (* [comment removed for export] *)
    pose proof co_res_init as CR. pose proof totsz_init as TS.
    constructor; unfold cs0z; cbn [init_acs_of_zero init_acs_of_with a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
      rewrite ?M1, ?M2, ?M3, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
    - exact init_regs_ok.
    - reflexivity.
    - exact init_kn_zero_ok.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros _; reflexivity.
    - first [exact CR | (rewrite M5 in CR; exact CR)].
    - reflexivity.
    - first [reflexivity | exact I | constructor].
    - constructor.   (* [comment removed for export] *)
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      exact (init_sp_ok_init_model (segments_reserved segs) brk0 mbase sp LIM inp Hsp).  (* [comment removed for export] *)
    - constructor.
    - constructor.
    - intros z Hz. exact Hz.
    - constructor.
    - constructor.
    - rewrite M4. exact TS.
    - constructor.   (* [comment removed for export] *)
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.
    - lia.
    - lia.
    - exact AB1.
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
    - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
    - split; [intros; reflexivity | intros; reflexivity].
    - (* [comment removed for export] *) split; [reflexivity | exact u_e_spw].
    - (* [comment removed for export] *) pose proof usp_lo. pose proof usp_fit. rewrite alloc_top0. unfold CEIL, TOPMAX. lia.
    - (* [comment removed for export] *) intros _; first [exact M7 | reflexivity].
    - (* [comment removed for export] *) intros iv Hiv _. rewrite ?M7 in Hiv. destruct Hiv.
    - (* [comment removed for export] *) rewrite ?M6. apply Forall_nil.
    - exact Hrdr.
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
    unfold uE. rewrite (edenot_ev_agree0 NX0 E E0 e_envp eq_refl Hev), (edenot_ev_agree0 NX0 E E0 e_str0 eq_refl Hev).
    split; [exact U1|]. split; [| rewrite U3; exact str0_cat].
    change (ev E V_ENVC) with (edenot E (EVar V_ENVC)).
    rewrite (edenot_ev_agree0 NX0 E E0 (EVar V_ENVC) eq_refl Hev).
    apply bv_eq. rewrite U2. pose proof len_ev. unfold envc in *. rewrite u64_lit by lia. reflexivity.
  Qed.

  Lemma SINV0_envp_E0 : forall E M (a : word), SINV0 E M ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 ->
    M a = wrap_mem inp mbase ph entryw sp rdraw a.
  Proof.
    intros E M a [_ HM] Ha. apply HM. unfold argH0.
    apply orb_true_intro. left. apply andb_true_intro.
    split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  Lemma SINV0_str0_E0 : forall E M (a : word), SINV0 E M ->
    usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn) <= bv_unsigned a
      <= usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn) + Z.of_nat (length (nth 0 argv [])) ->
    M a = wrap_mem inp mbase ph entryw sp rdraw a.
  Proof.
    intros E M a [_ HM] Ha. apply HM. unfold argH0.
    rewrite <- str0_cat in Ha. pose proof str0_hi. pose proof s0_in_strings. unfold L0 in *.
    apply orb_true_intro. right. apply andb_true_intro.
    split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (* [comment removed for export] *)
  Theorem init_cfg_eq :
    init_config segs apc ph sp brk0 mbase rdraw LIM inp = cfg_of segs R0 (a_entry A) FULL0 model0.
  Proof.
    unfold init_config, cfg_of, FULL0, entryw. rewrite init_mkst, Hapc. reflexivity.
  Qed.
End Init.
