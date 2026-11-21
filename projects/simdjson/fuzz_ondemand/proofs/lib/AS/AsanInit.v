(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the start state is proved of the run's whole launch input: the 27- or 29-pair auxv by the kernel's CONFIG_RSEQ flag with every type word claimed, the alignment-gap and group-id variables, the stack window below sp, and the vDSO pair at the end of the reserved list within the table's bounds; argH0 also hides the argument strings past the first two, the alignment gap and the padding; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); taken in part from projects/simdjson/fuzz_atpointer/proofs/lib/AS/Z1s.v, 572 lines within its lines 7-1387. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk StreamSim StepTac ShapeAlg AgentLib StartupAux RefLayout ArgvEnv
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan AsanPlanSound.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import AsanCeil.

From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import LiaFastAS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= zify_fast_euclid.

Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition LIMIT : Z := target_alloc_limit.

Record img_facts (segs : list Segment) (A : atable) (ph : PhdrInfo) : Prop := IMG_FACTS {
  if_ph    : ph_addr_z A = Z.of_N (ph_addr ph) /\ ph_ent_z A = Z.of_N (ph_ent ph) /\ ph_num_z A = Z.of_N (ph_num ph);
  if_hull  : 0 <= img_lo A <= img_hi A /\ img_hi A <= 2 ^ 32 /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0;
  if_top   : reserved_top (segments_reserved segs) = img_hi A;
  if_res   : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                    (segments_reserved segs);
  if_sizes : sum_sizes (segments_reserved segs) = img_hi A - img_lo A;
  if_rw    : (0 <= rw_lo A /\ 0 <= rw_len A /\ rw_lo A + rw_len A < 2 ^ 64)
             /\ forall m (x : word), rw_lo A <= bv_unsigned x < rw_lo A + rw_len A -> wview segs m x <> None;
  if_shadow : 0 <= shadow_off A <= 2 ^ 47
}.

(* LPS 75d69e00: the image runs from the entry stack pointer to the stack VMA's
   end, which [setup_arg_pages] page-aligns, so its size is exactly
   [ed_top - sp] ([Run.entry_launch_ok_va], [PropExec.length_entry_stack_image_launch]).
   It WAS a closed formula over argv/envp, and that formula is now FALSE three
   ways: its [+160] is the old ten-pair auxv (the vector is 432 bytes, 464 with
   CONFIG_RSEQ), it has no term for the exec file name that [copy_string_kernel]
   now copies, and it models the old short block that ended 16 bytes above the
   AT_RANDOM draw. *)
Definition stack_image_size (sp top : word) : Z :=
  (bv_unsigned top - bv_unsigned sp)%Z.

(* AT_NULL closes the vector: pair 28 with CONFIG_RSEQ, pair 26 without
   ([StackLayout.auxv_entries]).  From the 727298f3 port of
   bzip2/bzip2_compress_target, proofs/lib/K/AS/AsanInit.v. *)
Lemma auxv_words_null : forall la ph entry uid gid hw ar ae,
  nth (Z.to_nat (2 * (26 + 2 * rseq_z (la_rseq la))))
      (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0
  /\ nth (Z.to_nat (2 * (26 + 2 * rseq_z (la_rseq la)) + 1))
         (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. intros [ehdr c msz [|]] ph entry uid gid hw ar ae; split; reflexivity. Qed.

Section Init.
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  (* LPS 727298f3: the run's WHOLE input, every field as the published
     statements quantify it.  It WAS a [Definition inp] that pinned the exec
     name to [default_execfn], [/tmp] to [], the descriptor limit, urandom,
     the signal mask and the abort/sigpipe flags; [S3s_stmt_e] quantifies over
     every [valid_input_either] input and [wrap_mem] reads the exec name and
     the kernel, so the pinned form described other launches than the run's.
     The design of the 727298f3 port of bzip2/bzip2_compress_target,
     proofs/lib/K/AS/AsanInit.v. *)
  Variable inp : ProcInput.

  Let argv : list (list byte) := in_argv inp.
  Let envp : list (list byte) := in_envp inp.
  Let uid : word := in_uid inp.
  Let gid : word := in_gid inp.
  Let hw : word := in_hwcap inp.
  (* the launch's filesystem, [/tmp] seeded in: what the run's [m_fs] holds *)
  Let fs : Fs.Fs := in_fs inp.

  Hypothesis IMG : img_facts segs A ph.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.

  Hypothesis Hfit : entry_stack_fits sp argv envp.

  Hypothesis Huid : valid_id uid.

  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).

  (* [Run.valid_input]'s exec-name/E2BIG conjunct, and [Run.valid_entry]'s
     fifth: the start state is exactly a Linux launch.  [Hlau] is what pins the
     stack VMA's end, so it is what bounds the pad [W] and the image's length.
     Both are required by [PropExec.length_entry_stack_image_launch] and by [RefLayout]'s
     [Section Layout], whose six hypotheses are Hva Hve Hvl Hlau Hsp_lo Hsp_hi. *)
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  (* [Run.valid_input]'s reader clause ([cs_ok]'s [co_rdr]) *)
  Hypothesis Hrdr : in_channel_reader inp = true.

  (* Every one of these is derived from something already in scope, so each is a
     [Let] and discharges as a let-binding, costing callers nothing -- the rule
     [RZ] below already follows.  [entryw] is [a_entry A] rather than a new
     [apc] variable: [init_cfg_eq] keeps its own quantifier and rewrites with
     its hypothesis, so the section needs no [apc]. *)
  Let kb : KernelBuild := in_kernel inp.
  Let rseq : bool := kb_rseq (in_kernel inp).
  Let execfn : list byte := in_execfn inp.
  Let entryw : word := Z_to_bv 64 (a_entry A).
  Let la : LaunchAuxv := launch_auxv inp sp mbase.
  Let top : word := ed_top rdraw.

  Lemma inp_argv : in_argv inp = argv.    Proof. reflexivity. Qed.
  Lemma inp_envp : in_envp inp = envp.    Proof. reflexivity. Qed.
  Lemma inp_uid : in_uid inp = uid.       Proof. reflexivity. Qed.
  Lemma inp_gid : in_gid inp = gid.       Proof. reflexivity. Qed.
  Lemma inp_hwcap : in_hwcap inp = hw.    Proof. reflexivity. Qed.
  Lemma inp_rseq : kb_rseq (in_kernel inp) = rseq. Proof. reflexivity. Qed.
  Lemma la_rseq_eq : la_rseq la = rseq.   Proof. reflexivity. Qed.
  (* used by lstr_hi and pad_bounds_Z; it was referenced before it existed *)
  Lemma inp_execfn : in_execfn inp = execfn.  Proof. reflexivity. Qed.

  (* THE BLOCK IS THE WHOLE IMAGE at this revision: [build_stack_bytes] runs
     from [sp] to the stack VMA's end [ed_top], which [setup_arg_pages]
     page-aligns, so there is no page tail above it (Run.v:1326-1340).  [bsb]
     and [SIMG] are therefore the SAME list; they differed only while the model
     laid a block shorter than the kernel's.  [SIMG] is kept as the name the
     memory lemmas fold against, and [bsb] as the name the arithmetic uses. *)
  Let SIMG := entry_stack_image inp mbase ph entryw sp rdraw.
  Let bsb := SIMG.
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let L0 := Z.of_nat (length (nth 0 argv [])).
  Let L1 := Z.of_nat (length (nth 1 argv [])).

  (* The plan's CONFIG_RSEQ flag, moved up from its old position below [model0]
     because the layout arithmetic needs it.  Still a [Let]. *)
  Let RZ : Z := rseq_z rseq.
  Let utop := bv_unsigned top.
  (* [StackLayout.block_items mod 2]: STACK_ROUND's eight-byte gap, in words *)
  Let G := Z.of_nat (block_items argv envp mod 2).
  (* C, from sp to the top of the sixteen AT_RANDOM bytes *)
  Let CHEAD := Z.of_nat (block_head_size rseq argv envp).
  (* L, the string bytes with their NULs, the exec file name included *)
  Let LSTR := Z.of_nat (launch_string_bytes argv envp execfn).
  (* the [arch_align_stack] pad between the AT_RANDOM bytes and argv[0].  It WAS
     derived from the block length by division; it is now the model's own
     [block_pad_len], and it is what plan variable V_W denotes. *)
  Let W := Z.of_nat (block_pad_len rseq sp top argv envp execfn).
  (* argv[0]'s first byte.  The string area is at the TOP of the block now, not
     between the auxv and the AT_RANDOM bytes. *)
  Let STR0 := usp + CHEAD + W.

  (* TWELVE values: AS/AsanPlanCore.v pins NX0 = 12 with V_UID = 8, V_HW = 9, V_G = 10
     and V_GID = 11, so [hw] stays, the gap [G] is appended and the gid after
     it (AT_GID / AT_EGID).  V_S2 remains (usp mod 32768) / 16 because
     [e_sp0] is 32768 * V_S1 + 16 * V_S2. *)
  Definition vals0 : list word :=
    [Z_to_bv 64 (usp / 32768); Z_to_bv 64 argc; Z_to_bv 64 envc; Z_to_bv 64 L0; Z_to_bv 64 W;
     Z_to_bv 64 (bv_unsigned brk0 / 4096); Z_to_bv 64 ((usp mod 32768) / 16); Z_to_bv 64 L1; uid; hw;
     Z_to_bv 64 G; gid].

  Definition E0 : env := Env (fun n => nth n vals0 (Z_to_bv 64 0))
                             (fun k => if Nat.eqb k K_RND then at_random_bytes (ed_random rdraw) else []).

  (* the envp pointer array with its NULL -- the first hidden region, unchanged *)
  Definition argH0_old (E : env) (a : word) : bool :=
    let z := bv_unsigned a in
    ((usp + 8 * argc + 16 <=? z) && (z <? usp + 8 * argc + 8 * envc + 24))%bool.

  (* The hidden argument bytes: the envp pointer array (with its NULL), argv[2..] with
     argv's NULL, the STACK_ROUND gap below the AT_RANDOM bytes, and the pad and STRING
     AREA from the top of the AT_RANDOM bytes to the stack VMA's end.  Visible: argc,
     argv[0], argv[1], the auxv and the AT_RANDOM bytes, the start state's facts.  The
     hidden bytes are the launch image's ([SINV0]); [check] does not read [argH0]. *)
  Definition argH0 (E : env) (a : word) : bool :=
    let z := bv_unsigned a in
    (argH0_old E a || ((usp + 24 <=? z) && (z <? usp + 8 * argc + 16))
     || ((usp + CHEAD - 16 - 8 * G <=? z) && (z <? usp + CHEAD - 16))
     || ((usp + CHEAD <=? z) && (z <? utop)))%bool.
  Lemma argH0_of_old : forall E a, argH0_old E a = true -> argH0 E a = true.
  Proof. intros E a H. unfold argH0. cbv zeta. rewrite H. reflexivity. Qed.

  Definition SINV0 (E : env) (M : word -> option byte) : Prop :=
    (forall n, (n < NX0)%nat -> ev E n = ev E0 n)
    /\ (forall a, argH0 E a = true -> M a = wrap_mem inp mbase ph entryw sp rdraw a).


  Lemma argH0_agree : forall E E' a, env_agree NX0 E E' -> argH0 E a = argH0 E' a.
  Proof. reflexivity. Qed.

  Lemma SINV0_frame : forall E M M', (forall a, argH0 E a = true -> M' a = M a) -> SINV0 E M -> SINV0 E M'.
  Proof. intros E M M' Hf [H1 H2]. split; [exact H1|]. intros a Ha. rewrite (Hf a Ha). apply H2. exact Ha. Qed.

  Lemma SINV0_agree : forall E E' M, env_agree NX0 E E' -> SINV0 E M -> SINV0 E' M.
  Proof.
    intros E E' M [Hag _] [H1 H2]. split; [|exact H2]. intros n Hn. rewrite <- (Hag n) by (unfold NX0 in *; lia). apply H1. exact Hn.
  Qed.

  Lemma Hlo' : (sp_window_lo <= bv_unsigned sp)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
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

  (* The length is now the exact [ed_top - sp] from [PropExec.length_entry_stack_image_launch]
     (PropExec.v:2303).  The old proof unfolded [build_stack_bytes] and summed the
     pieces; that cannot work any more, because [bsb] is [entry_stack_image],
     a separate Definition (Run.v:1344) that CALLS [build_stack_bytes], so
     [unfold build_stack_bytes] never reaches a [string_addrs _ argv] redex. *)
  Lemma length_bsb_eq : Z.of_nat (length bsb) = stack_image_size sp top.
  Proof.
    unfold bsb, SIMG, stack_image_size, top.
    exact (length_entry_stack_image_launch Sv48 inp mbase ph entryw sp brk0 rdraw Hlau).
  Qed.

  (* [AUXSZ] is the plan's auxv size (AsanPlanCore.v:3044); [StackLayout.auxv_size] is the
     model's.  They agree at both flags: 16 * 27 = 432 and 16 * 29 = 464.  The
     model proves this as [AsanPlanCore.AUXSZ_of], which this tree does not
     carry, so it is proved here. *)
  Lemma AUXSZ_of : forall b : bool, AUXSZ (rseq_z b) = Z.of_nat (auxv_size b).
  Proof. intros [|]; reflexivity. Qed.

  Lemma RZ_range : 0 <= RZ <= 1.
  Proof. unfold RZ, rseq_z. destruct rseq; lia. Qed.

  Lemma gap_range : 0 <= G <= 1.
  Proof.
    unfold G. pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia.
  Qed.

  (* C = 8 * items + AUXSZ RZ + 8 * g + 16, with items = argc + envc + 3 *)
  Lemma chead_eq : CHEAD = 8 * argc + 8 * envc + 472 + 32 * RZ + 8 * G.
  Proof.
    pose proof (AUXSZ_of rseq) as HA. unfold AUXSZ in HA. change (rseq_z rseq) with RZ in HA.
    unfold CHEAD, G, argc, envc, block_head_size, block_items. lia.
  Qed.

  Lemma chead_range : 480 <= CHEAD <= 10752.
  Proof.
    pose proof chead_eq. pose proof len_av. pose proof len_ev.
    pose proof gap_range. pose proof RZ_range. lia.
  Qed.

  Lemma argH0_high : forall E a, argH0 E a = true -> CEIL <= bv_unsigned a.
  Proof.
    intros E a H. pose proof chead_range. pose proof gap_range.
    unfold argH0, argH0_old in H. cbv zeta in H. destruct Hsp as [Hlo _]. unfold sp_window_lo in Hlo. unfold CEIL.
    pose proof (valid_argv_len argv Hva).
    repeat (apply orb_prop in H as [H|H]); apply andb_prop in H as [H _]; apply Z.leb_le in H; unfold usp, argc, envc in *; lia.
  Qed.

  (* L >= 2: argv[0]'s NUL and the exec name's NUL.  Through [Hav0], since
     [execfn] is free here (the 727298f3 port of bzip2, K/AS/AsanInit.v). *)
  Lemma lstr_lo : 2 <= LSTR.
  Proof.
    unfold LSTR, launch_string_bytes.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
    pose proof (Nat2Z.is_nonneg (length execfn)).
    pose proof Hav0 as Hnz.
    destruct argv as [|a t] eqn:Ea; [cbn in Hnz; lia|].
    cbn [flatten_strings flat_map]. rewrite !length_app. cbn [length]. lia.
  Qed.

  Lemma s0_in_strings : L0 + 1 <= LSTR.
  Proof.
    unfold LSTR, launch_string_bytes, L0.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
    pose proof (Nat2Z.is_nonneg (length execfn)).
    pose proof Hav0 as Hnz.
    destruct argv as [|a t] eqn:Ea; [cbn in Hnz; lia|].
    cbn [flatten_strings flat_map nth]. rewrite !length_app. cbn [length]. lia.
  Qed.

  (* [Run.valid_launch]'s E2BIG half, in this file's names *)
  Lemma lstr_hi : LSTR + 8 * argc + 8 * envc <= 2097152.
  Proof.
    destruct Hlaunch as [_ Hb]. unfold launch_bytes, e2big_limit in Hb.
    rewrite inp_argv, inp_envp, inp_execfn in Hb. unfold LSTR, argc, envc. lia.
  Qed.

  (* The pad [arch_align_stack] left.  [launch_sp_hi] is align_down16(top-8-L) - C
     and [launch_sp_lo] the same less 4095, so the pad is the kernel's draw plus
     the low-four-bit remainder: at most 4110, not 4095. *)
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
    unfold W, block_pad_len, LSTR, CHEAD, utop, usp, top in *.
    rewrite Z2Nat.id by lia. reflexivity.
  Qed.

  Lemma pad_range : 0 <= W <= 4110.
  Proof. pose proof pad_bounds_Z. pose proof pad_eq. lia. Qed.

  Lemma length_bsb_sum : Z.of_nat (length bsb) = CHEAD + W + LSTR + 8.
  Proof.
    pose proof pad_eq. rewrite length_bsb_eq. unfold stack_image_size. fold utop usp. lia.
  Qed.

  (* [build_stack_bytes_within_span] was DELETED by the revision (noted at
     PropExec.v:2289): its span bound is false for the kernel's block.  The exact
     length from [length_entry_stack_image_launch] (PropExec.v:2303) replaces it, and
     [entry_page_top_within_window] (PropExec.v) caps [ed_top] by the stack window. *)
  Lemma usp_fit : usp + Z.of_nat (length bsb) <= 2 ^ 47.
  Proof.
    unfold bsb, SIMG, usp.
    rewrite (length_entry_stack_image_launch Sv48 inp mbase ph entryw sp brk0 rdraw Hlau).
    pose proof (entry_page_top_within_window Sv48 inp mbase sp brk0 rdraw Hlau) as H.
    (* LPS 727298f3: [va_stack_top Sv48] is [sp_window_hi] = 2^47; reduce the match
       and unfold it so [lia] sees the numeral. *)
    unfold entry_page_top in H. cbn [va_stack_top] in H. unfold sp_window_hi in H. lia.
  Qed.

  (* Kept as a PAIR so the eight external `pose proof bsb_ge as [G _]` sites do
     not move.  The floor rises from 200 to 482 -- the auxv alone is 432 now --
     and the second conjunct, which used to say the old W divided evenly, is now
     the exact decomposition, which is what callers actually want. *)
  Lemma bsb_ge : 8 * argc + 8 * envc + 482 <= Z.of_nat (length bsb)
                 /\ Z.of_nat (length bsb) = CHEAD + W + LSTR + 8.
  Proof.
    pose proof length_bsb_sum as HS. pose proof chead_eq. pose proof lstr_lo.
    pose proof pad_range. pose proof gap_range. pose proof RZ_range.
    split; [lia | exact HS].
  Qed.

  (* Kept as a TRIPLE so the seven external `as (W1 & W2 & W3)` sites do not
     move.  W is the [arch_align_stack] pad now, so its bound is 4110 rather
     than 280000, and the middle conjunct is the decomposition rather than the
     old `8 * W = ...` division fact. *)
  Lemma W_range : 0 <= W /\ Z.of_nat (length bsb) = CHEAD + W + LSTR + 8 /\ W <= 4110.
  Proof.
    pose proof pad_range. pose proof length_bsb_sum. split; [lia|]. split; [assumption | lia].
  Qed.

  Lemma brk_range : img_hi A <= bv_unsigned brk0 <= img_hi A + BRK_ASLR /\ bv_unsigned brk0 mod 4096 = 0.
  Proof.
    destruct Hbrk as (H1 & H2 & H3). unfold brk_aslr_max in H2. unfold page_size in H3.
    rewrite (if_top _ _ _ IMG) in H1, H2. unfold BRK_ASLR. lia.
  Qed.

  Lemma usp_hi : usp + 192 <= 2 ^ 47.
  Proof. pose proof usp_fit. pose proof bsb_ge as [BG _]. pose proof len_av. pose proof len_ev. lia. Qed.

  Lemma uE0 :
    uE E0 (EVar V_S1) = usp / 32768 /\ uE E0 (EVar V_S2) = (usp mod 32768) / 16
    /\ uE E0 (EVar V_ARGC) = argc /\ uE E0 (EVar V_ENVC) = envc /\ uE E0 (EVar V_L0) = L0
    /\ uE E0 (EVar V_W) = W /\ uE E0 (EVar V_BRK) = bv_unsigned brk0 / 4096
    /\ uE E0 (EVar V_G) = G.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
    pose proof gap_range. pose proof pad_range.
    pose proof (u64_range brk0) as [B1 B2].
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva ltac:(destruct Hva as [Hl _]; lia)). lia. }
    unfold uE. cbn [edenot E0 ev nth vals0 V_S1 V_S2 V_ARGC V_ENVC V_L0 V_W V_BRK V_G].
    rewrite !u64_lit by lia. repeat split; reflexivity.
  Qed.

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

  Lemma SINV0_sp : forall E M, SINV0 E M -> uE E e_sp0 = usp.
  Proof.
    intros E M [H1 _]. rewrite <- u_e_sp0. unfold e_sp0, eadd, escale, uE. rewrite !mkAlu_denot, !mkMd_denot. cbn [edenot].
    rewrite (H1 V_S1) by (unfold NX0, V_S1; lia). rewrite (H1 V_S2) by (unfold NX0, V_S2; lia). reflexivity.
  Qed.

  Lemma u_e_band : uE E0 e_band = usp - 8388608.
  Proof.
    pose proof usp_lo. pose proof usp_hi. rewrite APS.e_band_eq. unfold eaddz, uE. rewrite mkAlu_denot, edenot_lit, u_add64, u_lit64.
    change (bv_unsigned (edenot E0 e_sp0)) with (uE E0 e_sp0). rewrite u_e_sp0. change ((-8388608) mod two64) with 18446744073701163008.
    replace (usp + 18446744073701163008) with ((usp - 8388608) + 1 * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
  Qed.
  Lemma u_e_bandlen : uE E0 e_bandlen = 2 ^ 47 + 8388608 - usp.
  Proof.
    pose proof usp_lo. pose proof usp_hi. unfold e_bandlen, esub, uE. rewrite mkAlu_denot, edenot_lit, u_sub64, u64_lit by lia.
    change (bv_unsigned (edenot E0 e_sp0)) with (uE E0 e_sp0). rewrite u_e_sp0. apply Z.mod_small. lia.
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

  (* THE AUXV IS 432 BYTES NOW, 464 WITH CONFIG_RSEQ, NOT 160.  Every constant
     below was computed from the old ten-pair table: the literal 184 is
     24 + 160, and AT_RANDOM used to sit at the TOP of the block.  The revision
     rewrote the table (ARCH_DLINFO first, ten riscv64 entries, AT_HWCAP moving
     from the fourth pair to the eleventh), so these are restated over CHEAD
     and STR0 rather than re-derived with a new numeral -- a numeral would be
     wrong again at the other flag.  This unit defines NO auxv table of its own
     (0 definitions of auxv_size/auxv_count/auxv_entries across it), so there
     is nothing here to port; these are bounds over the model's span. *)
  Lemma u_e_atrandom : uE E0 (e_atrandom RZ) = usp + CHEAD - 16.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof gap_range. pose proof chead_eq. pose proof bsb_ge as [G0 _]. pose proof RZ_range.
    destruct uE0 as (_ & _ & _ & _ & _ & _ & _ & U8).
    pose proof u_e_auxv as UA. unfold e_atrandom, eadd, eaddz, escale, uE, AUXSZ in *.
    rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UA, U8. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_str0 : uE E0 (e_str0 RZ) = STR0.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof chead_eq. pose proof gap_range. pose proof bsb_ge as [G0 _]. pose proof RZ_range.
    destruct uE0 as (_ & _ & _ & _ & _ & U6 & _).
    pose proof u_e_atrandom as UA. unfold e_str0, eadd, eaddz, uE, STR0 in *.
    rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite UA, U6. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_str1 : uE E0 (e_str1 RZ) = STR0 + L0 + 1.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof chead_eq. pose proof gap_range. pose proof bsb_ge as [G0 _].
    pose proof RZ_range. pose proof length_bsb_sum. pose proof lstr_hi.
    destruct uE0 as (_ & _ & _ & _ & U5 & _).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    pose proof u_e_str0 as US. unfold e_str1, eadd, eaddz, uE, STR0 in *. rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite US, U5. rewrite !Z.mod_small by lia. lia.
  Qed.

  (* slot 4 denotes the arch_align_stack PAD now, and the eighth word the gap,
     so this sum ends in G and not in W *)
  Lemma u_e_atr8 : uE E0 e_atr8 = usp / 8 + argc + envc + G.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof gap_range.
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8). pose proof u_sp8 as U9.
    unfold e_atr8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia.
    rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit, !u_add64, !u_mul64, !u64_lit in U9 by lia.
    rewrite U1, U2, U3, U4, U8 in *. rewrite !Z.mod_small by lia. rewrite !Z.mod_small in U9 by lia. lia.
  Qed.

  Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.
  Definition FULL0 : word -> option byte := wrap_mem inp mbase ph entryw sp rdraw.
  (* LPS 75d69e00: [Run.init_config] is [mkCfg (init_machine_state inp)
     (with_vdso (vdso_run_init (ed_vdso mi_draw)) (init_model ...))]
     (75d69e00:theories/LinuxProcessSem/Run.v:1426-1430), so [model0] is that
     model and not the bare [init_model] -- otherwise [init_cfg_eq] below is
     false.  [State.init_model] in turn seeds [vm_reserved] with
     [State.init_reserved reserved mbase sp kb
        = reserved ++ vdso_reserved kb (page_round_down_Z
            (Z.min mbase (sp - stack_max_size)))]
     (State.v:7716-7721, :7786), which is why [model0_facts]'s ledger conjunct
     below carries [RESX]. *)
  Definition model0 : Model :=
    with_vdso (vdso_run_init (ed_vdso rdraw))
      (init_model (segments_reserved segs) brk0 mbase sp LIMIT inp).

  (* Stated about [model0] rather than about [init_model ...]: [model0] now wraps
     [with_vdso], which leaves [vm_init_sp] alone, so this still closes by
     conversion -- but a statement naming [init_model] no longer matches the goal
     after [unfold model0].  Internal to this file; not one of Section Init's
     exported names, so no caller moves. *)
  Lemma atop0 : alloc_top (m_vmmaps model0) = usp - 8388608.
  Proof. unfold alloc_top, stack_max_size. reflexivity. Qed.

  (* [State.vdso_top] of the initial ledger, and the pair itself.  Both are
     [Let]s, not [Variable]s: they are derived from [mbase], [sp] and [inp],
     all already in scope, so they discharge as let-bindings and cost this
     section's callers nothing -- the same reason [RZ] below is a [Let]. *)
  Let VTOP : Z :=
    page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)).
  Let RESX : list (word * word) := vdso_reserved (in_kernel inp) VTOP.

  (* [RZ] is defined with the layout Lets above, where [CHEAD] first needs it;
     it is still read off this section's own [inp], so [init_cs_ok]'s argument
     list is unchanged and its callers need no edit.  [init_acs_of] takes it
     because the revision's auxv puts AT_NULL at pair [26 + 2 * r] (AsanPlanCore.v:3530). *)
  Let cs0 := init_acs_of RZ A.
  Let cs0z := init_acs_of_zero RZ A.
  Let hid0 := hid A argH0 E0 cs0 model0.
  Let Mr0 := Mr A argH0 E0 cs0 model0 FULL0.

  Lemma model0_facts :
    m_halted model0 = None /\ m_fds model0 = fds_std /\ m_tid model0 = None
    /\ vm_reserved (m_vmmaps model0) = segments_reserved segs ++ RESX /\ vm_maps (m_vmmaps model0) = []
    /\ vm_noaccess (m_vmmaps model0) = [] /\ m_vm_lazy model0 = [] /\ m_vm_materialized model0 = []
    /\ vm_limit (m_vmmaps model0) = LIMIT /\ vm_brk (m_vmmaps model0) = brk0 /\ vm_start_brk (m_vmmaps model0) = brk0
    /\ vm_mmap_base (m_vmmaps model0) = mbase /\ eager_used model0 = 0.
  Proof. repeat split; reflexivity. Qed.

  Lemma hid0_eq : forall a : word, hid0 a = (argH0 E0 a || negb (APS.in_hull A (bv_unsigned a) || (usp - 8388608 <=? bv_unsigned a)))%bool.
  Proof.
    intros a. unfold hid0, hid, vis. destruct model0_facts as (_&_&_&_&Hm&Hn&Hl&_). rewrite Hm. cbn [in_ivs existsb andb].
    rewrite atop0. rewrite orb_false_r. reflexivity.
  Qed.

  Lemma Mr0_visible : forall a : word, usp - 8388608 <= bv_unsigned a -> argH0 E0 a = false -> Mr0 a = FULL0 a.
  Proof.
    intros a Hc Ha. unfold Mr0, Mr, mrestrict. fold hid0. rewrite hid0_eq, Ha.
    replace (usp - 8388608 <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; exact Hc). rewrite orb_true_r. reflexivity.
  Qed.

  (* LPS 727298f3: the zeroed window below sp is [Run.stack_window_lo], the
     larger of [ed_top - 8 MiB] and the mmap base plus the guard gap, so only
     [StoreOk.stack_window_depth] = 6144513 bytes of it are guaranteed.  From
     727298f3:theories/Common/AsanInit.v [FULL0_below] / [FULL0_low]. *)
  Lemma FULL0_below : forall a : word, usp - 6144513 <= bv_unsigned a < usp -> FULL0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. unfold FULL0, wrap_mem.
    assert (HW : stack_window_lo (in_kernel inp) mbase rdraw
                 <= bv_unsigned sp + stack_window_reach - stack_max_size)
      by exact (stack_window_lo_valid inp sp brk0 mbase rdraw Hlaunch Hlau).
    assert (Hs : stack_to_mem sp SIMG a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold SIMG. rewrite Hs.
    unfold stack_window_reach, stack_max_size, usp in *.
    replace (Z.leb (stack_window_lo (in_kernel inp) mbase rdraw) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  Qed.

  Lemma FULL0_low : forall a : word, bv_unsigned a < usp - 8388608 -> FULL0 a = None.
  Proof.
    intros a Ha. unfold FULL0, wrap_mem.
    pose proof (stack_window_lo_ge_sp inp sp brk0 mbase rdraw Hlau) as HW.
    assert (Hs : stack_to_mem sp SIMG a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold SIMG. rewrite Hs. unfold stack_max_size, usp in *.
    replace (Z.leb (stack_window_lo (in_kernel inp) mbase rdraw) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  Lemma rdn_Mr0_stack : forall (a : word) n,
    usp <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
    (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> argH0 E0 x = false) ->
    rdn segs Mr0 a n = rdn segs (stack_to_mem sp SIMG) a n.
  Proof.
    intros a n Ha Hn Hvis. pose proof usp_lo. unfold SIMG.
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

  Lemma argH0_ge : forall E a, argH0 E a = true -> usp + 24 <= bv_unsigned a.
  Proof.
    intros E a H. unfold argH0, argH0_old in H. cbv zeta in H. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [BG _].
    pose proof chead_range. pose proof pad_range. pose proof gap_range.
    repeat (apply orb_prop in H as [H|H]); apply andb_prop in H as [H _]; apply Z.leb_le in H; try unfold STR0 in *; lia.
  Qed.

  (* The hidden region: the envp pointer array, argv[2..] and its NULL, the STACK_ROUND
     gap, and the pad and string area up to the stack VMA's end.  Visible above sp:
     argc, argv[0], argv[1], the auxv vector and the sixteen AT_RANDOM bytes. *)
  Lemma argH0_range : forall a : word, argH0 E0 a = true ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 8 * envc + 24
    \/ usp + 24 <= bv_unsigned a < usp + 8 * argc + 16
    \/ usp + CHEAD - 16 - 8 * G <= bv_unsigned a < usp + CHEAD - 16
    \/ usp + CHEAD <= bv_unsigned a < utop.
  Proof.
    intros a H. unfold argH0, argH0_old in H. cbv zeta in H.
    repeat (apply orb_prop in H as [H|H]); apply andb_prop in H as [H1 H2];
      apply Z.leb_le in H1; apply Z.ltb_lt in H2; lia.
  Qed.

  Lemma not_argH0 : forall a : word,
    (bv_unsigned a < usp + 24
     \/ (usp + 8 * argc + 8 * envc + 24 <= bv_unsigned a < usp + CHEAD - 16 - 8 * G)
     \/ (usp + CHEAD - 16 <= bv_unsigned a < usp + CHEAD)
     \/ utop <= bv_unsigned a) -> argH0 E0 a = false.
  Proof.
    intros a H. destruct (argH0 E0 a) eqn:Ha; [|reflexivity]. apply argH0_range in Ha.
    pose proof len_av. pose proof len_ev. pose proof chead_eq. pose proof pad_range.
    pose proof gap_range. pose proof lstr_lo. pose proof RZ_range. pose proof pad_eq. lia.
  Qed.

  Lemma kword_stack : forall b k v (w : word),
    bv_unsigned (edenot E0 b) + k = bv_unsigned w ->
    usp <= bv_unsigned w -> bv_unsigned w + 8 <= usp + Z.of_nat (length bsb) ->
    (forall x : word, bv_unsigned w <= bv_unsigned x < bv_unsigned w + 8 -> argH0 E0 x = false) ->
    rdn segs (stack_to_mem sp SIMG) w 8%nat = Some (word_le8 (edenot E0 v)) ->
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

  (* The layout lemmas of [RefLayout]'s Section Layout, applied at this section's launch.
     Tried with the hypothesis lists that Section's lemmas can take, longest first. *)
  Local Ltac zp0 L H :=
    first [ pose proof (L segs Sv48 inp mbase ph entryw sp brk0 rdraw Hva Hve Hlaunch Hlau Hlo' Hhi') as H
          | pose proof (L segs Sv48 inp mbase ph entryw sp brk0 rdraw Hva Hve Hlaunch Hlau Hhi') as H
          | pose proof (L segs Sv48 inp mbase ph entryw sp brk0 rdraw Hva Hlaunch Hlau Hhi') as H
          | pose proof (L segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as H
          | pose proof (L segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlau Hhi') as H
          | pose proof (L segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau) as H ].

  Lemma auxv_count_RZ : Z.of_nat (auxv_count rseq) = 27 + 2 * RZ.
  (* [kb_rseq (in_kernel inp)] is the body of the section's [Let rseq], so it is split
     through [bool_dec] and rewritten in the goal only (as bzip2's [auxv_rseq_ok]). *)
  Proof.
    unfold RZ, rseq, rseq_z, auxv_count.
    destruct (Bool.bool_dec (kb_rseq (in_kernel inp)) true) as [Hr|Hr];
      [| apply Bool.not_true_is_false in Hr]; rewrite Hr; reflexivity.
  Qed.

  Let AUXW := auxv_words la ph entryw uid gid hw
                (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn).

  (* the auxv words: 58 (29 pairs) with CONFIG_RSEQ, 54 (27 pairs) without.  It WAS
     [j < 20].  From the 727298f3 port of bzip2, K/AS/AsanInit.v. *)
  Lemma auxv_word_ok : forall (j : nat) v,
    (j < 2 * auxv_count rseq)%nat ->
    nth j AUXW (Z_to_bv 64 0) = edenot E0 v ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 v).
  Proof.
    intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum.
    pose proof lstr_lo. pose proof bsb_ge as [BG _]. pose proof RZ_range. pose proof auxv_count_RZ.
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
    - rewrite <- Hv. zp0 read_auxv_word RW. exact (RW j Hj).
  Qed.

  Lemma auxw_ok : forall i ty v,
    (0 <= i < Z.of_nat (auxv_count rseq)) ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    nth (Z.to_nat (2 * i + 1)) AUXW (Z_to_bv 64 0) = edenot E0 v ->
    know_ok segs E0 Mr0 (auxw i ty v).
  Proof.
    intros i ty v Hi H1 H2. unfold auxw.
    constructor; [|constructor; [|constructor]].
    - replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia. apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
    - replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia. apply auxv_word_ok; [lia|]. exact H2.
  Qed.

  (* a type word alone (the pairs whose value stays unknown).  From the
     727298f3 port of bzip2, K/AS/AsanInit.v. *)
  Lemma auxt_ok : forall i ty,
    (0 <= i < Z.of_nat (auxv_count rseq)) ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 16 * i)) 8 (ELit ty)).
  Proof.
    intros i ty Hi H1.
    replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia.
    apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
  Qed.

  (* the whole vector is readable ([KUnk]): visible block memory below argv[0].
     From the 727298f3 port of bzip2, K/AS/AsanInit.v. *)
  Lemma auxv_unk_ok : kentry_ok segs E0 Mr0 (KUnk (SA (fst e_auxb) (snd e_auxb)) (ELit (AUXSZ RZ))).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum.
    pose proof lstr_lo. pose proof bsb_ge as [BG _]. pose proof RZ_range.
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
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
    unfold stack_to_mem. fold usp. rewrite u64_lit by (unfold usp in *; lia).
    replace (usp <=? usp + 8 * argc + 8 * envc + 24 + i) with true by (symmetry; apply Z.leb_le; lia).
    cbv zeta.
    replace (usp + 8 * argc + 8 * envc + 24 + i - usp <? Z.of_nat (length SIMG)) with true
      by (symmetry; apply Z.ltb_lt; unfold bsb in *; lia).
    intros Hn. apply nth_error_None in Hn. unfold bsb in *. lia.
  Qed.

  Lemma kr_ok : forall e lo hi, lo <= uE E0 e <= hi -> kentry_ok segs E0 Mr0 (KRange e lo hi).
  Proof. intros e lo hi H. cbn [kentry_ok]. unfold uE in H. exact H. Qed.

  Lemma Mr0_below : forall a : word, usp - 6144513 <= bv_unsigned a < usp -> Mr0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. pose proof usp_lo. pose proof len_av.
    rewrite Mr0_visible; [apply FULL0_below; exact Ha | unfold usp in *; lia | apply not_argH0; lia].
  Qed.

  (* LPS 727298f3: the plan's start state claims the 6144513-byte window
     ([AsanPlanCore.init_kn_with]), not 8 MiB. *)
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

  (* LPS 727298f3: the argv words, the AT_RANDOM block and the initial knowledge at the
     revision's block (strings at the top, 27/29-pair auxv).  From the 727298f3 port of
     bzip2/bzip2_compress_target, proofs/lib/K/AS/AsanInit.v, at this
     unit's plan (no V_GID; [init_kn_with] claims nine fixed pairs and AT_NULL). *)
  Lemma argc_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 0) 8 (EVar V_ARGC)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [BG _].
    apply (kword_stack e_sp0 0 (EVar V_ARGC) sp).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. unfold usp. lia.
    - unfold usp. lia.
    - unfold usp in *. lia.
    - intros x Hx. apply not_argH0. unfold usp in *. lia.
    - pose proof (read_argc inp mbase ph entryw segs sp rdraw) as RW.
      assert (Hv : len_word argv = edenot E0 (EVar V_ARGC)).
      { apply bv_eq. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. rewrite U3.
        unfold len_word, argc in *. rewrite u64_lit by lia. reflexivity. }
      rewrite inp_argv in RW. rewrite <- Hv. apply RW. fold SIMG. fold bsb. unfold usp in *. lia.
  Qed.

  (* argv[0] is at the bottom of the string area, below the stack VMA's end *)
  Lemma cat_argv0_eq :
    bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) = STR0.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof RZ_range.
    rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0 Hav0).
    change (total_arg_bytes_nat (firstn 0 (in_argv inp))) with 0%nat.
    rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
    change (kb_rseq (in_kernel inp)) with rseq. change (in_execfn inp) with execfn.
    change (in_argv inp) with argv. change (in_envp inp) with envp.
    unfold STR0, CHEAD, W, usp, rseq, top, cat_string_off in *.
    rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia.
  Qed.

  Lemma argv0_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 8) 8 (e_str0 RZ)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [BG _].
    apply (kword_stack e_sp0 8 (e_str0 RZ) (sp + nat_to_word (8 + 8 * 0))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
    - pose proof (read_argv_ptr_k segs inp mbase ph entryw sp rdraw 0) as RW.
      assert (Hv : cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0
                   = edenot E0 (e_str0 RZ)).
      { apply bv_eq. rewrite cat_argv0_eq. pose proof u_e_str0 as U. unfold uE in U. rewrite U. reflexivity. }
      rewrite <- Hv. apply RW; [exact Hav0|]. fold SIMG. fold bsb. unfold usp in *. lia.
  Qed.

  (* the word at sp0+16: argv[1] or the argv NULL *)
  Lemma argv1_word_ok : kentry_ok segs E0 Mr0 (kw_argv1 (e_argv1w RZ)).
  Proof.
    unfold kw_argv1.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [BG _].
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    assert (Hw1 : edenot E0 (e_argv1w RZ) = if (1 <? argc) then edenot E0 (e_str1 RZ) else Z_to_bv 64 0).
    { unfold e_argv1w. cbn [edenot]. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. cbn [edenot] in U3.
      apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit, U3 by lia.
      pose proof (u64_range (edenot E0 (e_str1 RZ))).
      destruct (1 <? argc); [rewrite Z.mul_1_l, Z.mod_small by lia; reflexivity | rewrite u64_lit by lia; reflexivity]. }
    apply (kword_stack e_sp0 16 (e_argv1w RZ) (sp + nat_to_word (8 + 8 * 1))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
    - rewrite Hw1. destruct (1 <? argc) eqn:Hc.
      + apply Z.ltb_lt in Hc. assert (Hav1 : (1 < length argv)%nat) by (unfold argc in Hc; lia).
        pose proof (read_argv_ptr_k segs inp mbase ph entryw sp rdraw 1) as RW.
        assert (Hv : cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1
                     = edenot E0 (e_str1 RZ)).
        { apply bv_eq.
          pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof RZ_range.
          assert (TF : forall l : list (list byte), (0 < length l)%nat ->
                        Z.of_nat (total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1)
            by (intros [|x t] Hl; [cbn in Hl; lia|]; change (firstn 1 (x :: t)) with [x]; cbn -[Z.of_nat Z.add]; lia).
          pose proof (TF argv Hav0) as TF0.
          pose proof u_e_str1 as U. unfold uE in U.
          rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1 Hav1).
          rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
          change (kb_rseq (in_kernel inp)) with rseq. change (in_execfn inp) with execfn.
          change (in_argv inp) with argv. change (in_envp inp) with envp.
          rewrite U. unfold STR0, CHEAD, W, usp, L0, rseq, top, cat_string_off in *.
          rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia. }
        rewrite <- Hv. apply RW; [exact Hav1|]. fold SIMG. fold bsb. unfold usp in *. lia.
      + apply Z.ltb_ge in Hc. assert (Hav1 : length argv = 1%nat) by (unfold argc in Hc; pose proof Hav0; lia).
        zp0 read_argv_null RW.
        rewrite inp_argv in RW. rewrite Hav1 in RW.
        exact RW.
  Qed.

  (* THE DEFAULT: the AT_RANDOM block is byte string [K_RND] = the draw *)
  Lemma atrandom_ok : kentry_ok segs E0 Mr0 (KBlob (SA (fst (e_atrb RZ)) (snd (e_atrb RZ))) (ELit 16) K_RND).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [BG _].
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof lstr_lo.
    pose proof RZ_range.
    assert (Hab : split_lit (e_atrandom RZ) = (fst (e_atrb RZ), snd (e_atrb RZ)))
      by (unfold e_atrb; destruct (split_lit (e_atrandom RZ)); reflexivity).
    set (ab := fst (e_atrb RZ)) in *. set (ak := snd (e_atrb RZ)) in *.
    pose proof (split_u E0 (e_atrandom RZ) ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    assert (Hak : ak = 24 + AUXSZ RZ) by exact (e_atrb_off rseq). unfold AUXSZ in Hak.
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + CHEAD - 16) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl.
    assert (HE : eb E0 K_RND = at_random_bytes (ed_random rdraw)) by (unfold E0; cbn [eb]; rewrite Nat.eqb_refl; reflexivity).
    rewrite HE.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    split; [rewrite length_at_random_bytes; reflexivity|].
    intros i Hi.
    zp0 at_random_off HAR. destruct HAR as [off (Hp & Hoff & Hmod & Hrd)].
    rewrite inp_argv, inp_envp, inp_rseq in Hp, Hoff, Hrd.
    assert (Hu : bv_unsigned (at_random_ptr sp rseq argv envp) = usp + CHEAD - 16).
    { rewrite Hp, word_add_nat, u64_lit by (unfold usp in *; lia). unfold CHEAD. lia. }
    specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold SIMG in Hrd. fold bsb in Hrd.
    rewrite (AsanCeil.firstn1_skipn_nth _ _ (Z_to_bv 8 0)) in Hrd by (rewrite length_at_random_bytes; lia).
    assert (Ha : (at_random_ptr sp rseq argv envp + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + CHEAD - 16 + i)).
    { apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
    rewrite Ha in Hrd.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold STR0, usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw) by (rewrite u64_lit; unfold usp in *; lia).
    fold SIMG. fold bsb.
    cbn [rdn] in Hrd.
    destruct (stack_to_mem sp bsb (Z_to_bv 64 (usp + CHEAD - 16 + i))) as [b|] eqn:Hstk.
    - cbn in Hrd. injection Hrd as ->. reflexivity.
    - exfalso. unfold stack_to_mem in Hstk. fold usp in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
      replace (usp <=? usp + CHEAD - 16 + i) with true in Hstk by (symmetry; apply Z.leb_le; lia).
      cbv zeta in Hstk.
      replace (usp + CHEAD - 16 + i - usp <? Z.of_nat (length bsb)) with true in Hstk by (symmetry; apply Z.ltb_lt; lia).
      apply nth_error_None in Hstk. lia.
  Qed.

  (* ZERO DRAW: the zero entry, under the (false) zero-draw hypothesis *)
  Lemma atrandom_zero_ok : kentry_ok segs E0 Mr0 (KZero (SA (fst (e_atrb RZ)) (snd (e_atrb RZ))) (ELit 16)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [BG _].
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof lstr_lo.
    pose proof RZ_range.
    assert (Hab : split_lit (e_atrandom RZ) = (fst (e_atrb RZ), snd (e_atrb RZ)))
      by (unfold e_atrb; destruct (split_lit (e_atrandom RZ)); reflexivity).
    set (ab := fst (e_atrb RZ)) in *. set (ak := snd (e_atrb RZ)) in *.
    pose proof (split_u E0 (e_atrandom RZ) ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    assert (Hak : ak = 24 + AUXSZ RZ) by exact (e_atrb_off rseq). unfold AUXSZ in Hak.
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + CHEAD - 16) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    intros i Hi.
    zp0 at_random_off HAR. destruct HAR as [off (Hp & Hoff & Hmod & Hrd)].
    rewrite inp_argv, inp_envp, inp_rseq in Hp, Hoff, Hrd.
    assert (Hu : bv_unsigned (at_random_ptr sp rseq argv envp) = usp + CHEAD - 16).
    { rewrite Hp, word_add_nat, u64_lit by (unfold usp in *; lia). unfold CHEAD. lia. }
    specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold SIMG in Hrd. fold bsb in Hrd.
    pose proof Hzr as Hz0. unfold AsanCeil.zero_random_draw in Hz0.
    rewrite Hz0, AsanCeil.at_random_bytes_zero, repeat_firstn_skipn in Hrd by lia.
    assert (Ha : (at_random_ptr sp rseq argv envp + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + CHEAD - 16 + i)).
    { apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
    rewrite Ha in Hrd.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold STR0, usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw) by (rewrite u64_lit; unfold usp in *; lia).
    fold SIMG. fold bsb.
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

  Lemma atr_ptr_eq : at_random_ptr sp rseq argv envp = edenot E0 (e_atrandom RZ).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof chead_eq. pose proof gap_range.
    pose proof len_av. pose proof len_ev. pose proof bsb_ge as [BG _]. pose proof RZ_range.
    zp0 at_random_off HAR. destruct HAR as [off (Hp & Hoff & _ & _)].
    rewrite inp_argv, inp_envp, inp_rseq in Hp, Hoff.
    apply bv_eq. rewrite Hp, word_add_nat, u64_lit by (unfold CHEAD, usp in *; lia).
    pose proof u_e_atrandom as U. unfold uE in U. rewrite U. unfold CHEAD, usp. lia.
  Qed.

  (* AT_NULL, the one claimed pair whose index moves with the flag: pair [26 + 2 * RZ] *)
  Lemma auxv_null_ok : know_ok segs E0 Mr0 (auxw (26 + 2 * RZ) 0 (ELit 0)).
  Proof.
    pose proof auxv_count_RZ. pose proof RZ_range.
    destruct (auxv_words_null la ph entryw uid gid hw
                (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn)) as [N1 N2].
    apply auxw_ok; [lia | exact N1 | rewrite edenot_lit; exact N2].
  Qed.

  (* the CONFIG_RSEQ pair (26, 27), claimed only at [RZ = 1], where it is in
     the vector.  From the 727298f3 port of bzip2, K/AS/AsanInit.v. *)
  Lemma auxv_rseq_ok :
    know_ok segs E0 Mr0 (if Z.eqb RZ 1 then auxw 26 27 (ELit 28) ++ auxw 27 28 (ELit 32) else []).
  Proof.
    pose proof auxv_count_RZ. pose proof RZ_range.
    unfold RZ, rseq, rseq_z in *. unfold AUXW, la, launch_auxv in *.
    (* [kb_rseq (in_kernel inp)] is the body of the section's [Let rseq]: split
       on it through [bool_dec] and rewrite in the goal only *)
    destruct (Bool.bool_dec (kb_rseq (in_kernel inp)) true) as [Hr|Hr]; [| apply Bool.not_true_is_false in Hr];
      rewrite Hr; cbn [Z.eqb Pos.eqb]; [|constructor].
    apply Forall_app; split; apply auxw_ok;
      unfold AUXW, rseq, la, launch_auxv, auxv_words, auxv_entries, auxv_count in *; cbn [la_rseq];
      rewrite ?Hr;
      first [ (cbn; lia)
            | (cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
               first [reflexivity | (rewrite edenot_lit; reflexivity)])
            | fail 1 "Z1S-AUXRSEQ:" ].
  Qed.

  Lemma init_kn_with_ok : forall atr, kentry_ok segs E0 Mr0 atr -> know_ok segs E0 Mr0 (init_kn_with RZ atr A).
  Proof.
    intros atr Hatr.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof gap_range. pose proof chead_eq. pose proof length_bsb_sum. pose proof lstr_lo.
    pose proof brk_range as [B1 B2]. pose proof bsb_ge as [BG _]. pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    pose proof (if_ph _ _ _ IMG) as (P1 & P2 & P3). pose proof RZ_range. pose proof auxv_count_RZ.
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    unfold init_kn_with.
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
      apply Forall_cons; [apply kr_ok; rewrite U6; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U7; unfold BRK_ASLR in *; lia|].
      apply Forall_cons; [exact SW1|].
      apply Forall_cons; [exact SW2|].
      apply Forall_cons; [exact argc_word_ok|].
      apply Forall_cons; [exact argv0_word_ok|].
      apply Forall_cons; [exact argv1_word_ok|].
      apply Forall_nil. }
    (* the nine fixed pairs (indices below 26, so the same at both flags), then AT_NULL,
       then the AT_RANDOM entry, the image hull and the writable window.  The list is
       RIGHT-nested, so each pair is peeled off with its own [Forall_app]. *)
    do 9 (apply Forall_app; split;
      [ apply auxw_ok;
        [ lia
        | unfold AUXW, auxv_words, auxv_entries;
          cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
          reflexivity
        | unfold AUXW, auxv_words, auxv_entries;
          cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
          first [ reflexivity
                | exact atr_ptr_eq
                | (rewrite edenot_lit; reflexivity)
                | (rewrite edenot_lit, P1; reflexivity)
                | (rewrite edenot_lit, P2; reflexivity)
                | (rewrite edenot_lit, P3; reflexivity)
                | fail 1 "Z1S-INITKN-PAIR:" ] ]
      | ]).
    apply Forall_app; split; [exact auxv_null_ok|].
    apply Forall_cons; [exact Hatr|].
    apply Forall_cons; [exact kimg_ok|].
    apply Forall_cons; [exact rw_window_ok|].
    (* design 1: the pairs the launch fixes or a plan variable denotes (AT_CLKTCK,
       AT_BASE, AT_FLAGS, AT_ENTRY, AT_GID, AT_EGID), the CONFIG_RSEQ pair, the
       readable vector and the eleven type words of the pairs whose value stays
       unknown -- the order of [AsanPlanCore.init_kn_with]'s appended block *)
    do 6 (apply Forall_app; split;
      [ apply auxw_ok;
        [ lia
        | unfold AUXW, auxv_words, auxv_entries;
          cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
          reflexivity
        | unfold AUXW, auxv_words, auxv_entries;
          cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
          first [ reflexivity
                | (rewrite edenot_lit; reflexivity)
                | fail 1 "Z1S-INITKN-PAIR2:" ] ]
      | ]).
    apply Forall_app; split; [exact auxv_rseq_ok|].
    apply Forall_cons; [exact auxv_unk_ok|].
    do 11 (apply Forall_cons;
      [ first [ (apply auxt_ok;
                 [ lia
                 | unfold AUXW, auxv_words, auxv_entries;
                   cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
                   reflexivity ])
              | fail 1 "Z1S-AUXT:" ] |]).
    apply Forall_nil.
  Qed.

  Lemma init_kn_ok : know_ok segs E0 Mr0 (init_kn RZ A).
  Proof. exact (init_kn_with_ok _ atrandom_ok). Qed.

  Lemma init_kn_zero_ok : know_ok segs E0 Mr0 (init_kn_zero RZ A).
  Proof. exact (init_kn_with_ok _ atrandom_zero_ok). Qed.

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

  Lemma allowA_init : allowA A E0 cs0 =
    [(pagedown (img_lo A), pageup (img_lo A + (img_hi A - img_lo A)));
     (pagedown (shadow_off A + img_lo A / 8), pageup (shadow_off A + (img_lo A + (img_hi A - img_lo A)) / 8));
     (pagedown (usp - 8388608), pageup (usp - 8388608 + (2 ^ 47 + 8388608 - usp)));
     (pagedown (shadow_off A + (usp - 8388608) / 8), pageup (shadow_off A + (usp - 8388608 + (2 ^ 47 + 8388608 - usp)) / 8))].
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    unfold allowA, cs0, init_acs_of, init_acs_of_with, init_vis. cbn [a_vis a_ghost app flat_map allow1 fst snd].
    unfold sh_lo, sh_hi. cbn [fst snd]. rewrite u_e_band, u_e_bandlen.
    unfold uE. rewrite !edenot_lit, !u64_lit by (unfold KHI in *; lia). reflexivity.
  Qed.

  Lemma abytes_init : A_bytes (allowA A E0 cs0) <= vis_cost (img_hi A - img_lo A) + vis_cost BANDLEN
                      /\ vis_cost (img_hi A - img_lo A) + vis_cost BANDLEN <= LIMIT.
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof (if_shadow _ _ _ IMG) as S1.
    pose proof usp_lo. pose proof usp_hi.
    rewrite allowA_init. cbn [A_bytes fst snd]. unfold vis_cost, BANDLEN, LIMIT, target_alloc_limit.
    replace (img_lo A + (img_hi A - img_lo A)) with (img_hi A) by lia.
    replace (usp - 8388608 + (2 ^ 47 + 8388608 - usp)) with (2 ^ 47) by lia.
    assert (P1 : forall z, z mod 4096 = 0 -> pagedown z = z) by (intros z Hz; unfold pagedown; lia).
    assert (P2 : forall z, z mod 4096 = 0 -> pageup z = z) by (intros z Hz; unfold pageup; lia).
    rewrite (P1 (img_lo A) I3), (P2 (img_hi A) I4).
    pose proof (pageup_minus_pagedown (shadow_off A + img_lo A / 8) (shadow_off A + img_hi A / 8) ltac:(lia)).
    pose proof (pageup_minus_pagedown (usp - 8388608) (2 ^ 47) ltac:(lia)).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    pose proof (pageup_minus_pagedown (shadow_off A + (usp - 8388608) / 8) (shadow_off A + 2 ^ 47 / 8) ltac:(lia)).
    unfold sp_window_lo in *.
    split; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Qed.

  (* --- the launch's extra reservations, for co_res / co_totsz / co_split: the vDSO pair,
     for ANY kernel build (the 727298f3 port of bzip2, K/AS/AsanInit.v) --- *)

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

  (** the pair, for ANY kernel build (the run's [in_kernel inp] is free in its vDSO text pages here):
      four vvar pages, then one to sixteen text pages (pem [Common/AsanInit.v] [resx_shape]) *)
  Lemma resx_shape :
    RESX = [(Z_to_bv 64 (VTOP - vdso_len kb), Z_to_bv 64 (vdso_vvar_pages * page_size));
            (Z_to_bv 64 (VTOP - vdso_len kb + vdso_vvar_pages * page_size),
             Z_to_bv 64 (vdso_text_pages kb * page_size))].
  Proof.
    pose proof vtop_range as [[T1 T2] T3]. pose proof (vdso_len_bounds kb).
    unfold RESX, vdso_reserved. cbv zeta. change (in_kernel inp) with kb.
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

  Lemma resx_ok : Forall (resx_entry_ok A) RESX.
  Proof.
    pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
    pose proof (vdso_text_pages_pos kb). pose proof (vdso_text_pages_le kb).
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    rewrite resx_shape. unfold resx_entry_ok, vdso_len, vdso_vvar_pages, page_size in *.
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd];
      rewrite !u64_lit by (unfold mmap_base_min, mmap_base_max, sp_window_hi in *; lia);
      unfold KHI, mmap_base_min, mmap_base_max, sp_window_hi in *;
      (split; [lia|]); (split; [Z.div_mod_to_equations; lia|]); (split; [Z.div_mod_to_equations; lia|]); repeat split; lia.
  Qed.

  (** the table's bound on what the LAUNCH reserves beside the image: the vDSO pair is two
      intervals and at most twenty pages ([State.vdso_len_bounds]).  Declared here, beside its
      only users, so the layout lemmas above do not carry it. *)
  Hypothesis HRESX : (2 <= n_resx A)%nat /\ (20 <= p_resx A)%nat.

  Lemma resx_bytes_lo : 81920 <= resx_bytes A.
  Proof. destruct HRESX as [RX1 RX2]. unfold resx_bytes. lia. Qed.


  Theorem init_cs_ok : cs_ok segs A NX0 LIMIT SINV0 argH0 fs E0 cs0 R0 FULL0 model0.
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
    - (* co_res: the launch reserves the vDSO pair beside the image *)
      pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
      destruct HRESX as [RX1 RX2]. pose proof resx_bytes_lo.
      exists RESX. split; [reflexivity|].
      split; [exact resx_ok | split; [pose proof resx_len; lia | rewrite resx_sum; pose proof (vdso_len_bounds kb); unfold page_size in *; lia]].
    - reflexivity.
    - reflexivity.
    - constructor.
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      exact (init_sp_ok_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp Hsp).
    - (* co_ceil: the stack band starts at or above the constant ceiling *)
      rewrite atop0. pose proof usp_lo. unfold CEIL, usp in *. lia.
    - constructor.
    - constructor.
    - intros z Hz. exact Hz.
    - constructor.
    - constructor.
    - (* co_totsz: the image's reservations and the vDSO pair *)
      rewrite app_nil_r, sum_sizes_app, (if_sizes _ _ _ IMG), resx_sum.
      pose proof resx_bytes_lo. pose proof (vdso_len_bounds kb). unfold page_size in *. lia.
    - (* co_split: the high mark is the vDSO pair's BASE; the fork's [a_ylo = KHI] is below it *)
      pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
      pose proof (vdso_len_bounds kb). exists (VTOP - vdso_len kb).
      unfold KHI, mmap_base_min, mmap_base_max, sp_window_hi in *.
      pose proof (vdso_text_pages_pos kb). pose proof (vdso_text_pages_le kb).
      split; [unfold page_size in *; lia|].
      split; [unfold vdso_len, vdso_vvar_pages, page_size in *; Z.div_mod_to_equations; lia|].
      split; [unfold page_size in *; lia|].
      rewrite app_nil_r. intros b sz Hin. apply in_app_or in Hin as [Hin|Hin].
      + pose proof (proj1 (Forall_forall _ _) (if_res _ _ _ IMG) _ Hin) as [R1 R2]. cbn [fst snd] in R1, R2.
        left. unfold kHighMemBeg. lia.
      + right. rewrite resx_shape in Hin. cbn [In] in Hin.
        pose proof (vdso_text_pages_pos kb). pose proof (vdso_text_pages_le kb).
        unfold vdso_len, vdso_vvar_pages, page_size in *.
        destruct Hin as [E|[E|[]]]; inversion E; subst; cbn [fst];
          rewrite u64_lit by lia; lia.
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7 & _). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.
    - lia.
    - lia.
    - exact AB1.
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
    - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
    - split; [intros; reflexivity | intros; reflexivity].
    -   intros E' Hag. change (vm_init_sp (m_vmmaps model0)) with sp.
      split; [|destruct Hsp as (_ & Hhi & _); exact Hhi].
      unfold uE. erewrite <- (APS.edenot_agree' NX0 E0 E' e_sp0 Hag); [rewrite edenot_e_sp0; reflexivity | reflexivity].
    -   intros a Ha. rewrite atop0. pose proof (argH0_ge E0 a Ha). lia.
    -   intros iv Hiv _. rewrite M7 in Hiv. destruct Hiv.
    -   rewrite ?M6. apply Forall_nil.
    - (* co_mres: no tracked mappings yet *)
      match goal with |- Forall _ ?l => replace l with (@nil (word * word))
        by (first [exact (eq_sym M5) | exact M5 | reflexivity]) end.
      constructor.
    - (* co_vdso: the ledger ends with the launch's own pair *)
      replace (m_kernel model0) with (in_kernel inp) by reflexivity.
      replace (vdso_top (m_vmmaps model0)) with VTOP
        by (symmetry; exact (vdso_top_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp)).
      rewrite ?M4. apply incl_appr, incl_refl.
    - (* co_rdr: [init_model] seeds the reader bit from [in_channel_reader inp]
         ([Hrdr]); [with_vdso] keeps [m_proc]. *)
      first [exact Hrdr | (cbn; exact Hrdr) | (unfold model0; cbn; rewrite Hrdr; reflexivity)].
  Qed.

  Theorem init_cs_ok_zero : cs_ok segs A NX0 LIMIT SINV0 argH0 fs E0 cs0z R0 FULL0 model0.
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
    destruct abytes_init as [AB1 AB2].
    change (allowA A E0 cs0) with (allowA A E0 (init_acs_of_zero RZ A)) in AB1.
    constructor; unfold cs0z; cbn [init_acs_of_zero init_acs_of_with a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
      rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
    - exact init_regs_ok.
    - reflexivity.
    - exact init_kn_zero_ok.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - (* co_res: the launch reserves the vDSO pair beside the image *)
      pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
      destruct HRESX as [RX1 RX2]. pose proof resx_bytes_lo.
      exists RESX. split; [reflexivity|].
      split; [exact resx_ok | split; [pose proof resx_len; lia | rewrite resx_sum; pose proof (vdso_len_bounds kb); unfold page_size in *; lia]].
    - reflexivity.
    - reflexivity.
    - constructor.
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      exact (init_sp_ok_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp Hsp).
    - (* co_ceil: the stack band starts at or above the constant ceiling *)
      rewrite atop0. pose proof usp_lo. unfold CEIL, usp in *. lia.
    - constructor.
    - constructor.
    - intros z Hz. exact Hz.
    - constructor.
    - constructor.
    - (* co_totsz: the image's reservations and the vDSO pair *)
      rewrite app_nil_r, sum_sizes_app, (if_sizes _ _ _ IMG), resx_sum.
      pose proof resx_bytes_lo. pose proof (vdso_len_bounds kb). unfold page_size in *. lia.
    - (* co_split: the high mark is the vDSO pair's BASE; the fork's [a_ylo = KHI] is below it *)
      pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
      pose proof (vdso_len_bounds kb). exists (VTOP - vdso_len kb).
      unfold KHI, mmap_base_min, mmap_base_max, sp_window_hi in *.
      pose proof (vdso_text_pages_pos kb). pose proof (vdso_text_pages_le kb).
      split; [unfold page_size in *; lia|].
      split; [unfold vdso_len, vdso_vvar_pages, page_size in *; Z.div_mod_to_equations; lia|].
      split; [unfold page_size in *; lia|].
      rewrite app_nil_r. intros b sz Hin. apply in_app_or in Hin as [Hin|Hin].
      + pose proof (proj1 (Forall_forall _ _) (if_res _ _ _ IMG) _ Hin) as [R1 R2]. cbn [fst snd] in R1, R2.
        left. unfold kHighMemBeg. lia.
      + right. rewrite resx_shape in Hin. cbn [In] in Hin.
        pose proof (vdso_text_pages_pos kb). pose proof (vdso_text_pages_le kb).
        unfold vdso_len, vdso_vvar_pages, page_size in *.
        destruct Hin as [E|[E|[]]]; inversion E; subst; cbn [fst];
          rewrite u64_lit by lia; lia.
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7 & _). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.
    - lia.
    - lia.
    - exact AB1.
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
    - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
    - split; [intros; reflexivity | intros; reflexivity].
    -   intros E' Hag. change (vm_init_sp (m_vmmaps model0)) with sp.
      split; [|destruct Hsp as (_ & Hhi & _); exact Hhi].
      unfold uE. erewrite <- (APS.edenot_agree' NX0 E0 E' e_sp0 Hag); [rewrite edenot_e_sp0; reflexivity | reflexivity].
    -   intros a Ha. rewrite atop0. pose proof (argH0_ge E0 a Ha). lia.
    -   intros iv Hiv _. rewrite M7 in Hiv. destruct Hiv.
    -   rewrite ?M6. apply Forall_nil.
    - (* co_mres *)
      match goal with |- Forall _ ?l => replace l with (@nil (word * word))
        by (first [exact (eq_sym M5) | exact M5 | reflexivity]) end.
      constructor.
    - (* co_vdso: the ledger ends with the launch's own pair *)
      replace (m_kernel model0) with (in_kernel inp) by reflexivity.
      replace (vdso_top (m_vmmaps model0)) with VTOP
        by (symmetry; exact (vdso_top_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp)).
      rewrite ?M4. apply incl_appr, incl_refl.
    - (* co_rdr *) first [exact Hrdr | (cbn; exact Hrdr) | (unfold model0; cbn; rewrite Hrdr; reflexivity)].
  Qed.

  Theorem init_cfg_eq : forall apc : N, Z.of_N apc = a_entry A ->
    init_config segs apc ph sp brk0 mbase rdraw LIMIT inp = cfg_of segs R0 (a_entry A) FULL0 model0.
  Proof.
    (* [Hpc] must land in BOTH places the entry pc appears: the machine's
       initial program counter, and the auxv's AT_ENTRY, which the stack image
       reads through [entryw].  [FULL0] and [entryw] are unfolded for the
       second. *)
    intros apc Hpc. unfold init_config, cfg_of, FULL0, entryw. rewrite init_mkst, Hpc. reflexivity.
  Qed.
End Init.
