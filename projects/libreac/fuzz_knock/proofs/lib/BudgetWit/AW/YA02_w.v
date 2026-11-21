(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA02.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YA02.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (changed img_facts, stack_image_size, inp, bsb, SIMG, L1 and 49 more; added auxv_words_null, auxv_words_rseq, rseq_z_1, e_atrb_off, entryw, rseq and 38 more; removed W_range); launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); cs_ok's channel-reader field co_rdr, proved at the launch and carried to the fdchan sites. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1d YK1a YK15 YK00 YK19 YK12 YK03 YK04.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.BudgetWit.AW Require Import YK05_w.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK08 YK0g.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK0c YK0e YK0f.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.BudgetWit.AW Require Import YA0c_w.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.BudgetWit.AW Require Import YA0e_w.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK06.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* Theorem Labs, 2026-11: the limit of the statements' budget premise, Budgets.Standard.lim_source (16 GiB),
   instead of target_alloc_limit (512 GiB). *)
Definition LIMIT : Z := 0x400000000.
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
(* STATEMENT CHANGED, old beside new.  The image is no longer computed from
   (argv, envp) at all: at 75d69e00 it is Linux's whole block from sp to the
   stack VMA's end, so its size is a function of (sp, top).
     OLD  stack_image_size (argv envp : list (list byte)) : Z :=
            let struct_size := 8 + (|argv|+1)*8 + (|envp|+1)*8 + 160 in
            let len := struct_size + total_arg_bytes argv + total_arg_bytes envp in
            len + ((8 - len mod 8) mod 8) + 16
     NEW  stack_image_size (sp top : word) : Z := bv_unsigned top - bv_unsigned sp
   The old one is FALSE, not stale: it has the old 160-byte auxv, puts the
   strings inside the struct, and knows nothing of the exec file name or the
   arch_align_stack pad.  Donor text and reasoning:
   projects/jsoncons/fuzz_bigint/proofs/lib/AsanInitK.v:49-62.  Its only
   consumer in this tree is YA0b.v:113-115, which unfolded it -- that
   unfolding goes with it. *)
Definition stack_image_size (sp top : word) : Z :=
  (bv_unsigned top - bv_unsigned sp)%Z.
(* AT_NULL closes the vector: pair 28 with CONFIG_RSEQ, pair 26 without
   ([StackLayout.auxv_entries], 75d69e00 StackLayout.v:229-266), so its two
   words are [2 * (26 + 2 * r)] and one more, at the flag's
   [r = rseq_z (la_rseq la)].  Never a literal 26 or 28.  Donor shape:
   projects/jsoncons/fuzz_bigint/proofs/lib/AsanInitK.v:70-75. *)
Lemma auxv_words_null : forall la ph entry uid gid hw ar ae,
  nth (Z.to_nat (2 * (26 + 2 * rseq_z (la_rseq la))))
      (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0
  /\ nth (Z.to_nat (2 * (26 + 2 * rseq_z (la_rseq la)) + 1))
         (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. intros [ehdr c msz [|]] ph entry uid gid hw ar ae; split; reflexivity. Qed.
(* The CONFIG_RSEQ pair, present when the flag is on: pairs 26 and 27, (27, 28) and (28, 32). *)
Lemma auxv_words_rseq : forall la ph entry uid gid hw ar ae, la_rseq la = true ->
  nth 52 (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 27
  /\ nth 53 (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 28
  /\ nth 54 (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 28
  /\ nth 55 (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 32.
Proof. intros [ehdr c msz [|]] ph entry uid gid hw ar ae H; [repeat split; reflexivity | discriminate H]. Qed.
Lemma rseq_z_1 : forall b, (rseq_z b =? 1) = true -> b = true.
Proof. intros [|] H; [reflexivity | discriminate H]. Qed.
(* The AT_RANDOM block's literal offset off [e_auxb]'s base: the pointer
   vector's NULLs and argc (24) plus the auxv itself, under BOTH layouts.  It
   is NOT a single literal any more -- 456 at [rseq = false], 488 at
   [rseq = true] -- which is what made [atrandom_ok]'s old [ak = 184] false.
   The tie to the model's own auxv size is [YK09.AUXSZ_of], which is
   hypothesis-free. *)
Lemma e_atrb_off : forall b, snd (e_atrb (rseq_z b)) = 24 + AUXSZ (rseq_z b).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Section c.
Variable segs : list Segment.
Variable A : atable.
Variable ph : PhdrInfo.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 mbase : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variable stdin : InputStream.
Variable uid gid : word.
Variable hw : word.
Variable groups : list word.
Variable net : NetQueue.
Variables nofile sigmask : word.
Variable urnd : InputStream.
Variable tmp : Fs.Fs.
(* The revision widened [State.mkProcInput_full] from fifteen places to twenty.
   [kb] stays a Variable so every free field of the build is free: a run under
   [Run.valid_input] satisfies [in_kernel inp = recorded_kernel (in_kernel inp)],
   and [recorded_kernel] preserves [kb_rseq] (75d69e00 Run.v:4575-4577), so a
   caller instantiates [kb] with its own build. *)
Variable kb : KernelBuild.
(* The exec file name is free for the same reason, and NOT [State.default_execfn]:
   this Section must accept the input the published statement quantifies over, and
   [Run.valid_input] constrains the name only through [valid_launch] -- it never
   pins it.  A pin here would be a premise no caller could discharge. *)
Variable execfn : list byte.
(* SIGPIPE's disposition at exec, FREE: [Run.valid_input] at 727298f3 pins
   [in_channel_reader] to true and [in_sigpipe_terminal] to false but leaves
   [in_sigpipe_default] free, so this Section takes it as a Variable rather than a
   literal (bzip2's proof keeps it free the same way). *)
Variable sdef : bool.
(* The image's ELF entry: [Run.init_config]'s pc, and the auxv's AT_ENTRY.  It is
   a Section Variable because the auxv -- hence the stack image -- reads it; it WAS
   only [init_cfg_eq]'s local quantifier at the end of this Section. *)
Variable apc : N.
Hypothesis IMG : img_facts segs A ph.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk segs brk0.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Huid : valid_id uid.
Hypothesis Hhw : valid_hwcap hw.
Definition inp : ProcInput :=
  mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw
    false Sv48 urnd tmp (recorded_kernel kb) execfn true sdef false.
Hypothesis Hnof : valid_nofile nofile.
Hypothesis Hsig : valid_sigmask inp.
Hypothesis Hapc : Z.of_N apc = a_entry A.
(* [Run.valid_launch]: the exec file name is a name [execve] admits and the launch
   fits under E2BIG. *)
Hypothesis Hvl : valid_launch inp.
(* [Run.valid_entry]'s FIFTH conjunct (75d69e00 Run.v:3723-3740), beside the four
   this Section already assumes: the start state is exactly a Linux launch.  It
   pins the stack VMA's end, the entry stack pointer inside the [arch_align_stack]
   window and the mmap base, so it is what bounds the pad [V_W] and the image's
   length.  It reads [kb_aslr] off [in_kernel inp] and leaves [kb_rseq] free. *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
Let entryw : word := Z_to_bv 64 (Z.of_N apc).
(* The run's CONFIG_RSEQ flag, kept SYMBOLIC: it is the one field of the launch
   that [Run.valid_input] leaves free, and the one that reaches [cat_string_off].
   Never pinned to [default_kernel]. *)
Let rseq := kb_rseq (in_kernel inp).
Let top := ed_top rdraw.
(* The mapped image IS Linux's block, sp .. [ed_top]: at 75d69e00
   [entry_stack_image] is [build_stack_bytes ...] exactly, the slack having become
   [ed_top], so [bsb] and [SIMG] are the SAME list. *)
Let bsb := entry_stack_image inp mbase ph entryw sp rdraw.
Let SIMG := entry_stack_image inp mbase ph entryw sp rdraw.
Let usp := bv_unsigned sp.
Let utop := bv_unsigned top.
Definition TOP : Z := bv_unsigned sp - 8388608.
Let argc := Z.of_nat (length argv).
Let envc := Z.of_nat (length envp).
Let L0 := Z.of_nat (length (nth 0 argv [])).
Let L1 := Z.of_nat (length (nth 1 argv [])).
(* the plan's CONFIG_RSEQ flag as 0 or 1: YK09's [rseq_z] at the free field *)
Let RZ := rseq_z rseq.
(* [StackLayout.block_items mod 2]: STACK_ROUND's 8-byte gap, in words.  This is
   the plan's variable [V_G] at index 9 (YK09.v:2273-2282). *)
Let G := Z.of_nat (block_items argv envp mod 2).
(* V_W CHANGED MEANING, not merely value.
     OLD  W := (|bsb| - 16 - (8*argc + 8*envc + 184)) / 8
          -- a COUNT of string words, the strings sitting just above the auxv.
     NEW  W := Z.of_nat (block_pad_len rseq sp top argv envp execfn)
          -- the [arch_align_stack] pad, in BYTES.
   Forced by the plan's [e_str0 r := eadd (eaddz (e_atrandom r) 16) (EVar V_W)]:
   V_W is now the distance from the top of the AT_RANDOM bytes up to argv[0],
   because the strings moved ABOVE the random bytes.  The old formula is not
   stale, it is FALSE. *)
Let W := Z.of_nat (block_pad_len rseq sp top argv envp execfn).
(* argv[0]'s first byte.  YK0h.v:281-283 has
   [cat_string_off = block_head_size + block_pad_len], so this IS the model's
   [usp + CHEAD + W]. *)
Let STR0 := usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).
(* C, sp to the top of the AT_RANDOM bytes *)
Let CHEAD := Z.of_nat (block_head_size rseq argv envp).
(* L, the string bytes with their NULs, the exec file name included *)
Let LSTR := Z.of_nat (launch_string_bytes argv envp execfn).
(* the input's fields, by conversion, so the arithmetic below stays a function of
   (sp, rdraw, argv, envp, execfn, kb) and not of the whole input *)
Lemma inp_argv : in_argv inp = argv.        Proof. reflexivity. Qed.
Lemma inp_envp : in_envp inp = envp.        Proof. reflexivity. Qed.
Lemma inp_execfn : in_execfn inp = execfn.  Proof. reflexivity. Qed.
Lemma inp_rseq : kb_rseq (in_kernel inp) = rseq. Proof. reflexivity. Qed.
(* ELEVEN entries: index 9 is the plan's [V_G] (STACK_ROUND's gap) and [hw] moved
   to index 10, matching YA01's [V_HW := 10] / [NX0G := 11].  Index 9 WAS [hw],
   and [V_G] is scaled by 8 inside [e_atrandom] / [e_str0] / [e_str1] / [e_atr8],
   so the old vector computed those four addresses with the HWCAP word standing in
   for the gap -- silently wrong, which is why this moved first. *)
(* TWELVE entries: index 11 is [gid], the plan's [V_GID] (YA01.v), which AT_GID and
   AT_EGID carry. *)
Definition vals0 : list word :=
[Z_to_bv 64 (usp / 32768); Z_to_bv 64 argc; Z_to_bv 64 envc; Z_to_bv 64 L0; Z_to_bv 64 W;
Z_to_bv 64 (bv_unsigned brk0 / 4096); Z_to_bv 64 ((usp mod 32768) / 16); Z_to_bv 64 L1; uid;
Z_to_bv 64 G; hw; gid].
Definition E0 : env := Env (fun n => nth n vals0 (Z_to_bv 64 0))
(fun k => if Nat.eqb k K_RND then at_random_bytes (ed_random rdraw) else []).
(* STATEMENT CHANGED, old beside new.  The second disjunct named the strings at
   [usp + 8*argc + 8*envc + 184 .. + 8*W], just above the auxv; at 75d69e00 they
   are at the TOP of the stack VMA, so the old range is FALSE, not stale.  Its
   replacement is [STR0 .. utop], the model's own shape. *)
Definition argH0 (E : env) (a : word) : bool :=
let z := bv_unsigned a in
(((usp + 8 * argc + 16 <=? z) && (z <? usp + 8 * argc + 8 * envc + 24))
|| ((STR0 <=? z) && (z <? utop)))%bool.
Definition SINV0 (E : env) (M : word -> option byte) : Prop :=
(forall n, (n < NX0G)%nat -> ev E n = ev E0 n)
/\ (forall a, argH0 E a = true -> M a = wrap_mem inp mbase ph entryw sp rdraw a)
/\ eb E = eb E0.
Lemma argH0_high : forall E a, argH0 E a = true -> TOP <= bv_unsigned a.
Proof.
intros E a H. unfold argH0 in H. destruct Hsp as [Hlo _]. unfold sp_window_lo in Hlo. unfold TOP.
pose proof (valid_argv_len argv Hva).
pose proof (Nat2Z.is_nonneg (cat_string_off rseq sp top argv envp execfn)).
apply orb_prop in H as [H|H]; apply andb_prop in H as [H _]; apply Z.leb_le in H;
  unfold usp, argc, envc, STR0 in H; lia.
Qed.
Lemma argH0_agree : forall E E' a, env_agree NX0G E E' -> argH0 E a = argH0 E' a.
Proof. reflexivity. Qed.
Lemma SINV0_frame : forall E M M', (forall a, argH0 E a = true -> M' a = M a) -> SINV0 E M -> SINV0 E M'.
Proof. intros E M M' Hf (H1 & H2 & H3). split; [exact H1|]. split; [|exact H3]. intros a Ha. rewrite (Hf a Ha). apply H2. exact Ha. Qed.
Lemma SINV0_agree : forall E E' M, env_agree NX0G E E' -> SINV0 E M -> SINV0 E' M.
Proof.
intros E E' M [Hag Hb] (H1 & H2 & H3). split; [| split; [exact H2 | rewrite <- Hb; exact H3]]. intros n Hn. rewrite <- (Hag n) by (unfold NX0G in *; lia). apply H1. exact Hn.
Qed.
Lemma Hlo' : (sp_window_lo <= bv_unsigned sp)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
Lemma Hhi' : (bv_unsigned sp <= sp_window_hi)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
Lemma Hav0 : (0 < length argv)%nat. Proof. destruct Hva as [[? ?] _]; lia. Qed.
Lemma len_av : 1 <= argc <= 1024.
Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
Lemma len_ev : 0 <= envc <= 256.
Proof. unfold envc. destruct Hve as [H _]. lia. Qed.
Lemma usp_lo : 0x7fff80000000 <= usp.
Proof. unfold usp. destruct Hsp as [H _]. exact H. Qed.
Lemma usp_al : usp mod 16 = 0.
Proof. unfold usp. destruct Hsp as (_ & _ & H). exact H. Qed.
Lemma RZ_range : 0 <= RZ <= 1.
Proof. exact (rseq_z_range rseq). Qed.
(* the vector's length, the ONE case split on the free flag the arithmetic needs *)
Lemma auxv_count_RZ : Z.of_nat (auxv_count rseq) = 27 + 2 * RZ.
Proof. unfold RZ, rseq_z, auxv_count. destruct (kb_rseq (in_kernel inp)); reflexivity. Qed.
Lemma gap_range : 0 <= G <= 1.
Proof. unfold G. pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia. Qed.
(* C = 8*items + auxv_size rseq + 8*g + 16, with items = argc + envc + 3 and the
   auxv [AUXSZ RZ = 432 + 32*RZ] bytes: 29 entries with CONFIG_RSEQ, 27 without
   (75d69e00 StackLayout.v:276-277, :399).  Tied to the model through the
   hypothesis-free [YK09.AUXSZ_of]; no literal 432/464 is written. *)
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
(* L >= 2: argv[0]'s NUL and the exec file name's NUL are both in the string area.
   [execfn] is a free Variable, so this goes through [Hav0] rather than through
   [default_execfn], and holds for every exec name. *)
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
destruct Hvl as [_ Hb]. unfold launch_bytes, e2big_limit in Hb.
rewrite inp_argv, inp_envp, inp_execfn in Hb. unfold LSTR, argc, envc. lia.
Qed.
(* The pad [arch_align_stack] left.  [launch_sp_hi] is [align_down16(top - 8 - L) - C]
   and [launch_sp_lo] the same with [top - 8 - L - 4095], so the pad is r (0..4095)
   plus the remainder the low-four-bit mask leaves -- at most 4110, NOT 4095. *)
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
(* REPLACES W_range's [W <= 280000], which was the old word-count bound; [W] is the
   pad in BYTES now and is no longer a quotient, so W_range's mod-8 conjunct has no
   replacement and no consumer. *)
Lemma pad_range : 0 <= W <= 4110.
Proof. pose proof pad_bounds_Z. pose proof pad_eq. lia. Qed.
(* [build_stack_bytes_within_span] is DELETED at 75d69e00 and its old closed form
   is FALSE for the kernel's block (75d69e00 Common/PropExec.v:2527-2533): a launch
   whose [arch_align_stack] pad is near 4095 bytes lays a block longer than the
   span, and the span says nothing about the strings' NULs or the exec file name.
   Its replacement is the EQUALITY [length_entry_stack_image_launch]
   (75d69e00 Common/PropExec.v:2534), vendored at YK11.v:2091. *)
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
Proof. unfold bsb. exact (bsb_bound Sv48 inp mbase ph entryw sp brk0 rdraw Hvl Hlau). Qed.
(* ONE rewrite now that the Section is ported: [length_entry_stack_image_launch] at
   [Sv48 inp mbase ph entryw sp brk0 rdraw Hlau] leaves
   [bv_unsigned (ed_top rdraw) <= 2 ^ 47], the second conjunct of
   [valid_stack_top_va] (75d69e00 Run.v:3610-3615), which is [Hlau]'s first
   component.  Nothing here pins the kernel. *)
Lemma usp_fit : usp + Z.of_nat (length bsb) <= 2 ^ 47.
Proof.
rewrite length_bsb_eq. unfold stack_image_size. fold utop usp.
pose proof (entry_page_top_within_window Sv48 inp mbase sp brk0 rdraw Hlau) as H.
unfold entry_page_top, va_stack_top, sp_window_hi in H. fold top utop in H. lia.
Qed.
(* STATEMENT CHANGED, old beside new:
     OLD  8*argc + 8*envc + 200 <= |bsb|
          /\ (|bsb| - 16 - (8*argc + 8*envc + 184)) mod 8 = 0
     NEW  8*argc + 8*envc + 482 <= |bsb|
   The mod-8 conjunct existed ONLY to justify the old W's division by 8, and W is
   no longer a quotient.  The bound rises 200 -> 482 because the auxv grew to 432
   bytes at 27 pairs and the block now also carries STACK_ROUND's gap, the sixteen
   random bytes, the pad, the strings and the eight-byte slot.  Stated at the
   SMALLER layout (RZ = 0, G = 0, L = 2) so it holds for every value of the free
   field [kb_rseq]. *)
Lemma bsb_ge : 8 * argc + 8 * envc + 482 <= Z.of_nat (length bsb).
Proof.
pose proof length_bsb_sum. pose proof chead_eq. pose proof lstr_lo. pose proof pad_range.
pose proof gap_range. pose proof RZ_range. lia.
Qed.
Lemma str0_hi : STR0 + LSTR + 8 = utop.
Proof.
unfold STR0, cat_string_off. pose proof pad_eq.
fold CHEAD. fold W. lia.
Qed.
Lemma brk_range : img_hi A <= bv_unsigned brk0 <= img_hi A + BRK_ASLR /\ bv_unsigned brk0 mod 4096 = 0.
Proof.
destruct Hbrk as (H1 & H2 & H3). unfold brk_aslr_max in H2. unfold page_size in H3.
rewrite (if_top _ _ _ IMG) in H1, H2. unfold BRK_ASLR. lia.
Qed.
Lemma usp_hi : usp + 192 <= 2 ^ 47.
Proof. pose proof usp_fit. pose proof bsb_ge as Gb. pose proof len_av. pose proof len_ev. lia. Qed.
Lemma uE0 :
uE E0 (EVar V_S1) = usp / 32768 /\ uE E0 (EVar V_S2) = (usp mod 32768) / 16
/\ uE E0 (EVar V_ARGC) = argc /\ uE E0 (EVar V_ENVC) = envc /\ uE E0 (EVar V_L0) = L0
/\ uE E0 (EVar V_W) = W /\ uE E0 (EVar V_BRK) = bv_unsigned brk0 / 4096.
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof pad_range. pose proof gap_range.
pose proof (u64_range brk0) as [B1 B2].
assert (HL0 : 0 <= L0 <= 131071).
{ unfold L0. pose proof (valid_argv_str_len argv 0 Hva ltac:(destruct Hva as [Hl _]; lia)). lia. }
unfold uE. cbn [edenot E0 ev nth vals0 V_S1 V_S2 V_ARGC V_ENVC V_L0 V_W V_BRK].
rewrite !u64_lit by lia. repeat split; reflexivity.
Qed.
(* [uE0] is a seven-tuple over S1/S2/ARGC/ENVC/L0/W/BRK and does not carry the
   plan's new [V_G]; every bullet that used to land on index 9 reads this. *)
Lemma uE0_G : uE E0 (EVar V_G) = G.
Proof.
pose proof gap_range. unfold uE. cbn [edenot E0 ev nth vals0 V_G].
rewrite u64_lit by lia. reflexivity.
Qed.
Lemma L1_range : 0 <= L1 <= 131071.
Proof.
unfold L1. destruct (Nat.lt_ge_cases 1 (length argv)) as [Hl|Hl].
- pose proof (valid_argv_str_len argv 1 Hva Hl). lia.
- rewrite nth_overflow by lia. cbn. lia.
Qed.
Lemma uE0_L1 : uE E0 (EVar V_L1) = L1.
Proof. pose proof L1_range. unfold uE. cbn [edenot E0 ev nth vals0 V_L1]. rewrite u64_lit by lia. reflexivity. Qed.
Lemma uE0_uid : uE E0 (EVar V_UID) = bv_unsigned uid.
Proof. reflexivity. Qed.
(* index 10 now, not 9 *)
Lemma edenot_hw : edenot E0 (EVar V_HW) = hw.
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
Lemma SINV0_sp0 : forall E M, SINV0 E M -> uE E e_sp0 = TOP + 8388608.
Proof.
intros E M [H1 _]. unfold TOP.
replace (uE E e_sp0) with (uE E0 e_sp0); [rewrite u_e_sp0; unfold usp; lia|].
unfold e_sp0, eadd, escale, uE. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot].
rewrite (H1 V_S1) by (unfold V_S1, NX0G; lia). rewrite (H1 V_S2) by (unfold V_S2, NX0G; lia). reflexivity.
Qed.
Lemma SINV0_s1 : forall E M, SINV0 E M ->
uE E e_sp0 = TOP + 8388608 /\ uE E (EVar V_S1) = (TOP + 8388608) / 32768 /\ (TOP + 8388608) mod 16 = 0.
Proof.
intros E M H. split; [exact (SINV0_sp0 E M H)|]. destruct H as [H1 _]. unfold TOP.
replace (bv_unsigned sp - 8388608 + 8388608) with usp by (unfold usp; lia). split; [|exact usp_al].
pose proof (proj1 uE0) as U1. unfold uE in U1 |- *. cbn [edenot] in U1 |- *.
rewrite (H1 V_S1) by (unfold V_S1, NX0G; lia). exact U1.
Qed.
Lemma top_ok0 : top_ok TOP.
Proof. pose proof Hsp as (Hlo & Hhi & _). clear - Hlo Hhi. unfold top_ok, TOP, CEIL. unfold sp_window_lo in Hlo. unfold sp_window_hi in Hhi. lia. Qed.
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
(* STATEMENT CHANGED, old beside new:
     OLD  uE E0 e_atrandom = usp + |bsb| - 16
     NEW  uE E0 (e_atrandom RZ) = usp + CHEAD - 16
   The sixteen AT_RANDOM bytes sit at the top of the HEAD, not at the top of the
   IMAGE: [create_elf_tables] lays the vector down from them and [copy_strings] has
   already put the strings above them.  The old right-hand side is FALSE, not
   stale -- it names a place that is now inside the string area.  [AUXSZ] is
   unfolded here only so [lia] sees a linear term in [RZ]; the tie to the model's
   [auxv_size] is [AUXSZ_of]. *)
Lemma u_e_atrandom : uE E0 (e_atrandom RZ) = usp + CHEAD - 16.
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
pose proof chead_eq. pose proof chead_range. pose proof gap_range. pose proof RZ_range.
pose proof u_e_auxv as UA. pose proof uE0_G as UG.
unfold e_atrandom, eadd, eaddz, escale, uE, AUXSZ in *.
rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UA, UG.
rewrite !Z.mod_small by lia. lia.
Qed.
(* STATEMENT CHANGED, old beside new:
     OLD  uE E0 e_str0 = usp + 8*argc + 8*envc + 184
     NEW  uE E0 (e_str0 RZ) = STR0
   184 was the struct plus the OLD 160-byte auxv with the strings just above it;
   they are now at the top of the stack VMA, so the old right-hand side is FALSE.
   [STR0] is [usp + cat_string_off rseq sp top argv envp execfn], a function of the
   FREE [kb_rseq] and of the [arch_align_stack] pad, never a constant. *)
Lemma u_e_str0 : uE E0 (e_str0 RZ) = STR0.
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
pose proof chead_eq. pose proof chead_range. pose proof gap_range. pose proof RZ_range.
pose proof pad_range. pose proof pad_eq. pose proof lstr_lo. pose proof length_bsb_sum.
destruct uE0 as (_ & _ & _ & _ & _ & U6 & _).
pose proof u_e_atrandom as UA.
unfold e_str0, eadd, eaddz, uE in *. rewrite !mkAlu_denot, !edenot_lit.
rewrite !u_add64, !u64_lit by lia. rewrite UA, U6.
rewrite !Z.mod_small by lia.
unfold STR0, cat_string_off. fold CHEAD. fold W. lia.
Qed.
(* Same move, one string along: argv[1] is argv[0] + L0 + 1. *)
Lemma u_e_str1 : uE E0 (e_str1 RZ) = STR0 + L0 + 1.
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
pose proof chead_eq. pose proof chead_range. pose proof gap_range. pose proof RZ_range.
pose proof pad_range. pose proof pad_eq. pose proof str0_hi. pose proof s0_in_strings.
pose proof length_bsb_sum. pose proof lstr_lo.
destruct uE0 as (_ & _ & _ & _ & U5 & _).
assert (HL0 : 0 <= L0 <= 131071).
{ unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
pose proof u_e_str0 as US. unfold e_str1, eadd, eaddz, uE in *.
rewrite !mkAlu_denot, !edenot_lit.
rewrite !u_add64, !u64_lit by lia. rewrite US, U5.
rewrite !Z.mod_small by lia. lia.
Qed.
(* STATEMENT CHANGED, old beside new:
     OLD  uE E0 e_atr8 = usp / 8 + argc + envc + W
     NEW  uE E0 e_atr8 = usp / 8 + argc + envc + G
   The plan's [e_atr8] reads [EVar V_G] where it read [EVar V_W] (YK09.v:2296),
   because the quantity it bounds is the shadow of the argument block below the
   random bytes -- the auxv size cancels out of it, which is why it is the one
   expression of this family that takes no [r].  [W] and [G] are no longer
   related: [W] is the pad in BYTES. *)
Lemma u_e_atr8 : uE E0 e_atr8 = usp / 8 + argc + envc + G.
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof gap_range.
destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7). pose proof u_sp8 as U8. pose proof uE0_G as UG.
unfold e_atr8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
rewrite !u_add64, !u_mul64, !u64_lit by lia.
rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit, !u_add64, !u_mul64, !u64_lit in U8 by lia.
rewrite U1, U2, U3, U4, UG in *. rewrite !Z.mod_small by lia. rewrite !Z.mod_small in U8 by lia. lia.
Qed.
Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.
Definition FULL0 : word -> option byte := wrap_mem inp mbase ph entryw sp rdraw.
(* [Run.init_config] wraps the model in [with_vdso (vdso_run_init (ed_vdso draw))]
   at 75d69e00 (Run.v:1426-1431); [init_cfg_eq] below is an equality with that
   configuration, so the wrapper belongs here.  It touches only the vDSO field, so
   unchanged projections still reduce; the reserved ledger also contains the vDSO pair. *)
Definition model0 : Model :=
  with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
    (init_model (segments_reserved segs) brk0 mbase sp LIMIT inp).
Let cs0 := init_acs_of RZ A.
Let cs0z := init_acs_of_zero RZ A.
Let hid0 := hid A TOP argH0 E0 cs0 model0.
Let Mr0 := Mr A TOP argH0 E0 cs0 model0 FULL0.
Lemma model0_facts :
m_halted model0 = None /\ m_fds model0 = fds_std /\ m_tid model0 = None
/\ vm_reserved (m_vmmaps model0) = segments_reserved segs
   ++ vdso_reserved (m_kernel model0) (vdso_top (m_vmmaps model0))
/\ vm_maps (m_vmmaps model0) = []
/\ vm_noaccess (m_vmmaps model0) = [] /\ m_vm_lazy model0 = [] /\ m_vm_materialized model0 = []
/\ vm_limit (m_vmmaps model0) = LIMIT /\ vm_brk (m_vmmaps model0) = brk0 /\ vm_start_brk (m_vmmaps model0) = brk0
/\ vm_mmap_base (m_vmmaps model0) = mbase /\ eager_used model0 = 0.
Proof.
repeat split; try reflexivity.
unfold model0. rewrite !m_vmmaps_with_vdso, m_kernel_with_vdso, m_kernel_init_model.
apply vm_reserved_init_model.
Qed.
Let VTOP : Z :=
  page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)).
(* The initial pair's position uses the launch's mmap base (from Hlau, as Run.v's
   [entry_launch_ok_va_base] gives it) and usp_lo (hence Hsp), not the stack-image
   predicates. Keep that capture when changing this proof. *)
Lemma vtop_range : mmap_base_min - 4095 <= VTOP <= bv_unsigned mbase
  /\ VTOP mod 4096 = 0.
Proof.
pose proof (entry_launch_ok_va_base Sv48 (mkEntry sp brk0 mbase rdraw) inp Hlau) as Hmb.
cbn [en_mmap_base] in Hmb. rewrite valid_mmap_base_va_sv48 in Hmb.
pose proof Hmb as (Y1 & Y2 & Y3). pose proof usp_lo.
unfold VTOP, page_round_down_Z, page_size, stack_max_size,
  mmap_base_min, mmap_base_max, sp_window_hi, usp in *.
split; [split|]; lia.
Qed.
Lemma model0_res_bounds :
let rx := vdso_reserved (m_kernel model0) (vdso_top (m_vmmaps model0)) in
(length rx <= 2)%nat /\ sum_sizes rx <= 20 * 4096 /\
Forall (fun iv => KHI <= bv_unsigned (fst iv)) rx.
Proof.
cbv zeta. unfold model0.
rewrite !m_kernel_with_vdso, !m_vmmaps_with_vdso,
  !m_kernel_init_model, !vdso_top_init_model. fold VTOP.
pose proof vtop_range as [[T1 T2] T3].
pose proof (entry_launch_ok_va_base Sv48 (mkEntry sp brk0 mbase rdraw) inp Hlau) as Hmb.
cbn [en_mmap_base] in Hmb. rewrite valid_mmap_base_va_sv48 in Hmb.
pose proof Hmb as (Y1 & Y2 & Y3).
pose proof (vdso_len_bounds (in_kernel inp)) as HL.
pose proof (vdso_text_pages_pos (in_kernel inp)) as HP.
pose proof (vdso_text_pages_le (in_kernel inp)) as HS.
unfold vdso_reserved. cbv zeta.
destruct (Z.ltb_spec (VTOP - vdso_len (in_kernel inp)) page_size) as [Hsmall|Hbase].
- split; [cbn [length]; lia|]. split; [cbn [sum_sizes]; lia|constructor].
- split; [cbn [length]; lia|]. split.
  + cbn [sum_sizes fst snd].
    rewrite !u64_lit by
      (unfold vdso_len, vdso_vvar_pages, page_size, mmap_base_max, sp_window_hi in *; lia).
    unfold vdso_len, vdso_vvar_pages, page_size in *; lia.
  + repeat constructor; cbn [fst];
      rewrite !u64_lit by
        (unfold vdso_len, vdso_vvar_pages, page_size, mmap_base_max, sp_window_hi in *; lia);
      unfold KHI, vdso_len, vdso_vvar_pages, page_size,
        mmap_base_min, mmap_base_max, sp_window_hi in *; lia.
Qed.
Lemma hid0_eq : forall a : word, hid0 a = (argH0 E0 a || negb (APSG.in_hull A (bv_unsigned a) || (TOP <=? bv_unsigned a)))%bool.
Proof.
intros a. unfold hid0, hid, vis. destruct model0_facts as (_&_&_&_&Hm&Hn&Hl&_). rewrite Hm. cbn [in_ivs existsb andb].
rewrite orb_false_r. reflexivity.
Qed.
Lemma Mr0_visible : forall a : word, TOP <= bv_unsigned a -> argH0 E0 a = false -> Mr0 a = FULL0 a.
Proof.
intros a Hc Ha. unfold Mr0, Mr, mrestrict. fold hid0. rewrite hid0_eq, Ha.
replace (TOP <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; exact Hc). rewrite orb_true_r. reflexivity.
Qed.
(* STATEMENT CHANGED, old beside new:
     OLD  usp - 8388608 <= bv_unsigned a < usp -> FULL0 a = Some 0
     NEW  usp - stack_window_depth <= bv_unsigned a < usp -> FULL0 a = Some 0
   The old one is FALSE, not stale, at EVERY launch.  [YK11.wrap_mem] now zero-fills
   down to [Run.stack_window_lo (in_kernel inp) mbase rdraw], which is
   [max (top - stack_max_size) (mbase + guard_gap)], and [top > sp] always
   ([pad_eq] with [lstr_lo]), so [stack_window_lo > usp - 8388608] on every run --
   no hypothesis recovers the old window.  [stack_window_depth] is
   [stack_max_size - stack_window_reach] (YK1b.v:117-122, 6144513), which is what
   [stack_window_lo_valid] bounds the fill by.  Consumers re-checked: [Mr0_below]
   and [stack_window_ok] below (both restated), and [atrandom_ok] /
   [rdn_Mr0_stack], which only ever apply it at or above sp. *)
Lemma FULL0_below : forall a : word, usp - stack_window_depth <= bv_unsigned a < usp -> FULL0 a = Some (Z_to_bv 8 0).
Proof.
intros a Ha. unfold FULL0, wrap_mem.
assert (HW : stack_window_lo (in_kernel inp) mbase rdraw
             <= bv_unsigned sp + stack_window_reach - stack_max_size)
  by exact (stack_window_lo_valid inp sp brk0 mbase rdraw Hvl Hlau).
assert (Hs : stack_to_mem sp SIMG a = None).
{ unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
fold SIMG. rewrite Hs. unfold stack_window_depth, stack_window_reach, stack_max_size, usp in *.
replace (Z.leb (stack_window_lo (in_kernel inp) mbase rdraw) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
(* STATEMENT UNCHANGED at 8388608: [stack_window_lo_ge_sp] (YK1b.v:187) gives
   [sp - stack_max_size <= stack_window_lo], so nothing BELOW the old window is
   filled either.  Only the filled side shrank. *)
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
apply rdn_ext; [exact Hn|]. intros x Hx. apply Mr0_visible; [unfold usp, TOP, CEIL in *; lia | apply Hvis; exact Hx].
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
(* STATEMENT CHANGED, following [argH0]'s own restatement: the string disjunct is
   [STR0 .. utop], not [usp + 8*argc + 8*envc + 184 .. + 8*W]. *)
Lemma argH0_range : forall a : word, argH0 E0 a = true ->
usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 8 * envc + 24
\/ STR0 <= bv_unsigned a < utop.
Proof.
intros a H. unfold argH0 in H.
apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2];
  apply Z.leb_le in H1; apply Z.ltb_lt in H2; [left|right]; lia.
Qed.
(* The complement, in the same two ranges: below the envp pointers, between them
   and argv[0] (the auxv, the gap and the random bytes all live here now), and
   above the stack VMA's end.  [STR0], [utop], [CHEAD], [W] and [LSTR] stay ATOMS:
   every relation the contradiction needs is among the posed facts, and a
   [fold CHEAD in *] would fold inside CHEAD's own body. *)
Lemma not_argH0 : forall a : word,
(bv_unsigned a < usp + 8 * argc + 16
 \/ (usp + 8 * argc + 8 * envc + 24 <= bv_unsigned a < STR0)
 \/ utop <= bv_unsigned a) -> argH0 E0 a = false.
Proof.
intros a H. destruct (argH0 E0 a) eqn:Ha; [|reflexivity]. apply argH0_range in Ha.
pose proof len_av. pose proof len_ev. pose proof chead_eq. pose proof pad_range.
pose proof gap_range. pose proof str0_hi. pose proof pad_eq. pose proof lstr_lo.
pose proof RZ_range. lia.
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
(* the auxv words the launch wrote, named once *)
Let AUXW := auxv_words (launch_auxv inp sp mbase) ph entryw uid gid hw
              (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn).
(* STATEMENT CHANGED, old beside new:
     OLD  (j < 20)%nat -> nth j (auxv_words ph (at_random_ptr sp argv envp) uid hw) .. -> ..
     NEW  (j < 2 * auxv_count rseq)%nat -> nth j AUXW .. -> ..
   The old one is FALSE, not stale, twice over: [StackLayout.auxv_words] now takes
   eight arguments ([la ph entry uid gid hw ar ae]) where it took four, so the old
   application does not even type; and the vector is 58 words (29 pairs) with
   CONFIG_RSEQ and 54 (27) without, where 20 was the old 160-byte auxv's count.
   [auxv_count rseq] is symbolic in the free field, so the new bound holds at BOTH
   builds ([auxv_count_RZ] is the only case split).  The read-back is
   [YK12.read_auxv_word], whose own bound is the same. *)
Lemma auxv_word_ok : forall (j : nat) v,
(j < 2 * auxv_count rseq)%nat ->
nth j AUXW (Z_to_bv 64 0) = edenot E0 v ->
kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 v).
Proof.
intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
pose proof chead_eq. pose proof chead_range. pose proof pad_range. pose proof gap_range.
pose proof length_bsb_sum. pose proof lstr_lo. pose proof bsb_ge as Gb. pose proof RZ_range.
pose proof auxv_count_RZ. pose proof str0_hi. pose proof pad_eq.
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
rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul in Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. lia.
- rewrite <- Hv.
exact (read_auxv_word segs Sv48 inp mbase ph entryw sp brk0 rdraw Hva Hve Hvl Hlau Hlo' Hhi' j Hj).
Qed.
(* STATEMENT CHANGED, old beside new:
     OLD  (0 <= i <= 9) -> ..
     NEW  (0 <= i <= 26 + 2 * RZ) -> ..
   Same two reasons as [auxv_word_ok]; the plan claims pair [26 + 2 * r]
   (YK09.v:2742), which 9 excludes at either build. *)
Lemma auxw_ok : forall i ty v,
(0 <= i <= 26 + 2 * RZ) ->
nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
nth (Z.to_nat (2 * i + 1)) AUXW (Z_to_bv 64 0) = edenot E0 v ->
know_ok segs E0 Mr0 (auxw i ty v).
Proof.
intros i ty v Hi H1 H2. pose proof auxv_count_RZ. pose proof RZ_range. unfold auxw.
constructor; [|constructor; [|constructor]].
- replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia. apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
- replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia. apply auxv_word_ok; [lia|]. exact H2.
Qed.
Lemma kr_ok : forall e lo hi, lo <= uE E0 e <= hi -> kentry_ok segs E0 Mr0 (KRange e lo hi).
Proof. intros e lo hi H. cbn [kentry_ok]. unfold uE in H. exact H. Qed.
(* STATEMENT CHANGED for [FULL0_below]'s reason, and stated through
   [YK1b.stack_window_depth] rather than its numeral so that a model change to
   [stack_window_reach] moves this in one place:
     OLD  usp - 8388608 <= bv_unsigned a < usp -> Mr0 a = Some 0
     NEW  usp - stack_window_depth <= bv_unsigned a < usp -> Mr0 a = Some 0 *)
Lemma Mr0_below : forall a : word, usp - stack_window_depth <= bv_unsigned a < usp -> Mr0 a = Some (Z_to_bv 8 0).
Proof.
intros a Ha. pose proof usp_lo. pose proof len_av. pose proof stack_window_depth_val.
rewrite Mr0_visible; [apply FULL0_below; lia | unfold TOP, CEIL; lia | apply not_argH0; lia].
Qed.
(* The initial KWr/KZero facts use the launch-independent zero-fill depth
   guaranteed by [stack_window_lo_valid]. *)
Lemma stack_window_ok :
kentry_ok segs E0 Mr0 (KWr (SA e_sp0 (-stack_window_depth)) (ELit stack_window_depth))
/\ kentry_ok segs E0 Mr0 (KZero (SA e_sp0 (-stack_window_depth)) (ELit stack_window_depth)).
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof stack_window_depth_val as HD.
assert (Hst : estart E0 (SA e_sp0 (-stack_window_depth)) = usp - stack_window_depth).
{ unfold estart. cbn [a_base a_off]. pose proof u_e_sp0 as U. unfold uE in U. rewrite U. lia. }
assert (Hl : elenZ E0 (ELit stack_window_depth) = stack_window_depth) by (apply elenZ_lit; lia).
assert (Hfl : flat E0 (SA e_sp0 (-stack_window_depth)) (elenZ E0 (ELit stack_window_depth))).
{ unfold flat. rewrite Hst, Hl. lia. }
split; cbn [kentry_ok]; (split; [exact Hfl|]); rewrite Hst, ?Hl.
- intros d m Hd Hdm. apply store_ok_of_all; rewrite u_small by lia; [lia|].
intros x Hx. unfold wview. rewrite (Mr0_below x) by lia. discriminate.
- intros i Hi. apply Mr0_below. rewrite u_small by lia. lia.
Qed.
Lemma argc_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 0) 8 (EVar V_ARGC)).
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as Gb.
apply (kword_stack e_sp0 0 (EVar V_ARGC) sp).
- pose proof u_e_sp0 as U. unfold uE in U. rewrite U. unfold usp. lia.
- unfold usp. lia.
- unfold usp in *. lia.
- intros x Hx. apply not_argH0. unfold usp in *. lia.
- pose proof (read_argc inp mbase ph entryw segs sp rdraw) as RW.
assert (Hv : len_word argv = edenot E0 (EVar V_ARGC)).
{ apply bv_eq. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. rewrite U3. unfold argc. exact (u_argcN inp Hva). }
rewrite inp_argv in RW. rewrite <- Hv. apply RW. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
Qed.
(* argv[0] is at the BOTTOM OF THE STRING AREA, [cat_string_off] bytes above sp --
   no longer [cat_struct_size] bytes above sp, and [STR0] is this Section's name
   for that address. *)
Lemma argv0_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 8) 8 (e_str0 RZ)).
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as Gb.
apply (kword_stack e_sp0 8 (e_str0 RZ) (sp + nat_to_word (8 + 8 * 0))%bv).
- pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
- rewrite word_add_nat, u64_lit; unfold usp in *; lia.
- rewrite word_add_nat, u64_lit; unfold usp in *; lia.
- intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
- pose proof (read_argv_ptr_k segs inp mbase ph entryw sp rdraw 0) as RW.
assert (Hv : cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0 = edenot E0 (e_str0 RZ)).
{ apply bv_eq.
rewrite (u_cat_argv_ptr segs Sv48 inp mbase ph entryw sp brk0 rdraw Hva Hve Hvl Hlau Hlo' Hhi' 0 Hav0).
pose proof u_e_str0 as U. unfold uE in U. rewrite U.
change (total_arg_bytes_nat (firstn 0 (in_argv inp))) with 0%nat.
unfold STR0, usp, rseq, top. rewrite inp_argv, inp_envp, inp_execfn. rewrite Nat.add_0_r. reflexivity. }
rewrite <- Hv. apply RW; [rewrite inp_argv; exact Hav0|]. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
Qed.
Lemma argv1_word_ok : kentry_ok segs E0 Mr0 (kw_argv1 (e_argv1w RZ)).
Proof.
unfold kw_argv1.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as Gb.
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
assert (Hv : cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1 = edenot E0 (e_str1 RZ)).
{ apply bv_eq.
rewrite (u_cat_argv_ptr segs Sv48 inp mbase ph entryw sp brk0 rdraw Hva Hve Hvl Hlau Hlo' Hhi' 1 ltac:(rewrite inp_argv; exact Hav1)).
pose proof u_e_str1 as U. unfold uE in U. rewrite U.
assert (TF : forall l : list (list byte), (0 < length l)%nat ->
Z.of_nat (total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1)
by (intros [|x t] Hl; [cbn in Hl; lia|]; change (firstn 1 (x :: t)) with [x]; cbn -[Z.of_nat Z.add]; lia).
rewrite inp_argv, inp_envp, inp_execfn.
rewrite Nat2Z.inj_add, (TF argv Hav0). unfold STR0, L0, usp, rseq, top. lia. }
rewrite <- Hv. apply RW; [rewrite inp_argv; exact Hav1|]. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
+ apply Z.ltb_ge in Hc. assert (Hav1 : length argv = 1%nat) by (unfold argc in Hc; pose proof Hav0; lia).
pose proof (read_argv_null segs Sv48 inp mbase ph entryw sp brk0 rdraw Hva Hve Hvl Hlau Hlo' Hhi') as RW.
rewrite inp_argv, Hav1 in RW.
exact RW.
Qed.
(* STATEMENT UNCHANGED.  Three steps inside it were FALSE, not stale, and all three
   are the same move: the AT_RANDOM bytes are no longer at the TOP of the image.
     OLD  Hak : ak = 184          NEW  Hak : ak = 24 + AUXSZ RZ
     OLD  Hst : .. = usp + |bsb| - 16   NEW  .. = usp + CHEAD - 16
     OLD  Hu  : .. = usp + off          NEW  .. = usp + CHEAD - 16
   [snd (e_atrb RZ)] is [24 + AUXSZ RZ] because [e_atrandom] now adds the auxv's
   own size (YK09.v:2295); no literal can be right at both builds, and the tie to
   the model's [auxv_size] is the hypothesis-free [AUXSZ_of]. *)
Lemma atrandom_ok : kentry_ok segs E0 Mr0 (KBlob (SA (fst (e_atrb RZ)) (snd (e_atrb RZ))) (ELit 16) K_RND).
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as Gb.
pose proof chead_eq. pose proof chead_range. pose proof pad_range. pose proof gap_range.
pose proof length_bsb_sum. pose proof lstr_lo. pose proof RZ_range.
pose proof str0_hi. pose proof pad_eq.
assert (Hab : split_lit (e_atrandom RZ) = (fst (e_atrb RZ), snd (e_atrb RZ))) by (unfold e_atrb; destruct (split_lit (e_atrandom RZ)); reflexivity).
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
destruct (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw Hva Hve Hvl Hlau Hlo' Hhi') as [off (Hp & Hoff & Hmod & Hrd)].
rewrite inp_argv, inp_envp, inp_rseq in Hp, Hoff, Hrd.
assert (Hu : bv_unsigned (at_random_ptr sp rseq argv envp) = usp + CHEAD - 16).
{ rewrite Hp, word_add_nat, u64_lit by (unfold CHEAD, usp in *; lia). unfold CHEAD. lia. }
specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold SIMG in Hrd.
rewrite (YK06.firstn1_skipn_nth _ _ (Z_to_bv 8 0)) in Hrd by (rewrite length_at_random_bytes; lia).
assert (Ha : (at_random_ptr sp rseq argv envp + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + CHEAD - 16 + i)).
{ apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
rewrite Ha in Hrd.
rewrite Mr0_visible; [| rewrite u64_lit; unfold usp, TOP, CEIL in *; lia | apply not_argH0; rewrite u64_lit; unfold usp in *; lia].
unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw _) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
cbn [rdn] in Hrd.
destruct (stack_to_mem sp SIMG (Z_to_bv 64 (usp + CHEAD - 16 + i))) as [b|] eqn:Hstk.
- cbn in Hrd. injection Hrd as ->. reflexivity.
- exfalso. unfold stack_to_mem in Hstk. fold usp in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
replace (usp <=? usp + CHEAD - 16 + i) with true in Hstk by (symmetry; apply Z.leb_le; lia).
cbv zeta in Hstk.
(* [bsb] and [SIMG] are the same list at this revision; it WAS [length_app] on
   [build_stack_bytes ++ entry_slack]. *)
assert (HL : (length bsb <= length SIMG)%nat) by (unfold SIMG, bsb; lia).
replace (usp + CHEAD - 16 + i - usp <? Z.of_nat (length SIMG)) with true in Hstk by (symmetry; apply Z.ltb_lt; lia).
apply nth_error_None in Hstk. lia.
Qed.
Lemma kimg_ok : kentry_ok segs E0 Mr0 (KImg (img_lo A) (img_hi A)).
Proof.
pose proof usp_lo. pose proof (if_hull _ _ _ IMG) as (H1 & H2 & H3 & H4). cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
unfold Mr0, Mr, mrestrict. destruct (hid A TOP argH0 E0 cs0 model0 (Z_to_bv 64 i)); [reflexivity|].
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
Lemma atr_ptr_eq : at_random_ptr sp rseq argv envp = edenot E0 (e_atrandom RZ).
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof chead_eq. pose proof chead_range. pose proof gap_range.
pose proof len_av. pose proof len_ev. pose proof bsb_ge as Gb. pose proof RZ_range.
destruct (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw Hva Hve Hvl Hlau Hlo' Hhi') as [off (Hp & Hoff & _ & _)].
rewrite inp_argv, inp_envp, inp_rseq in Hp, Hoff.
apply bv_eq. rewrite Hp, word_add_nat, u64_lit by (unfold CHEAD, usp in *; lia).
pose proof u_e_atrandom as U. unfold uE in U. rewrite U. unfold CHEAD, usp. lia.
Qed.
(* AT_NULL, the one claimed pair whose index moves with the flag: pair [26 + 2*RZ]
   (YK09.v:2742, [auxv_words_null] above).  A symbolic [nth] no [cbn] can reduce,
   so this is the one case split. *)
Lemma auxv_null_ok : know_ok segs E0 Mr0 (auxw (26 + 2 * RZ) 0 (ELit 0)).
Proof.
pose proof auxv_count_RZ. pose proof RZ_range.
destruct (auxv_words_null (launch_auxv inp sp mbase) ph entryw uid gid hw
            (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn)) as [N1 N2].
apply auxw_ok; [lia | exact N1 | rewrite edenot_lit; exact N2].
Qed.
(* A type word alone (the pairs whose value stays unknown).  As cgif/cgif_file_fuzzer's
   YA02.v [auxt_ok] in this working copy (from bzip2's [K/AS/AsanInit.v]). *)
Lemma auxt_ok : forall i ty,
(0 <= i < Z.of_nat (auxv_count rseq)) ->
nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
kentry_ok segs E0 Mr0 (auxt i ty).
Proof.
intros i ty Hi H1. unfold auxt.
replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia.
apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
Qed.
(* The whole vector is readable ([KUnk]): it is visible block memory between the envp
   pointers and argv[0]. *)
Lemma auxv_unk_ok : kentry_ok segs E0 Mr0 (KUnk (SA (fst e_auxb) (snd e_auxb)) (ELit (AUXSZ RZ))).
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
pose proof chead_eq. pose proof chead_range. pose proof pad_range. pose proof gap_range.
pose proof length_bsb_sum. pose proof lstr_lo. pose proof bsb_ge as Gb. pose proof RZ_range.
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
rewrite Mr0_visible; [| rewrite u64_lit; unfold usp, TOP, CEIL in *; lia | apply not_argH0; rewrite u64_lit; unfold usp in *; lia].
unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw _) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
unfold stack_to_mem. fold usp. rewrite u64_lit by (unfold usp in *; lia).
replace (usp <=? usp + 8 * argc + 8 * envc + 24 + i) with true by (symmetry; apply Z.leb_le; lia).
cbv zeta.
assert (HL : (length bsb <= length SIMG)%nat) by (unfold SIMG, bsb; lia).
replace (usp + 8 * argc + 8 * envc + 24 + i - usp <? Z.of_nat (length SIMG)) with true by (symmetry; apply Z.ltb_lt; lia).
intros Hn. apply nth_error_None in Hn. lia.
Qed.
(* [YK09.auxt_all]: the readable vector, the launch-fixed values of pairs 12, 16, 17, 18 (and
   of the CONFIG_RSEQ pair when the flag is on), and the type words of the pairs whose value
   stays unknown.  Pairs 0..25 sit before the conditional pair, so their [nth] reduces
   without the flag; the conditional pair is read through [auxv_words_rseq]. *)
Lemma auxt_all_ok : know_ok segs E0 Mr0 (auxt_all RZ A).
Proof.
pose proof auxv_count_RZ. pose proof RZ_range.
unfold auxt_all. apply Forall_cons; [exact auxv_unk_ok|].
do 4 (apply Forall_app; split;
[ apply auxw_ok;
  [ lia
  | unfold AUXW; cbn [auxv_words auxv_entries flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
    reflexivity
  | unfold AUXW; cbn [auxv_words auxv_entries flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
    first [ reflexivity | (rewrite edenot_lit; reflexivity)
          | (rewrite edenot_lit; unfold entryw; rewrite Hapc; reflexivity) ] ]
| ]).
apply Forall_app; split.
- destruct (Z.eqb RZ 1) eqn:E1; [|apply Forall_nil].
  pose proof (rseq_z_1 _ E1) as Hrs. apply Z.eqb_eq in E1.
  destruct (auxv_words_rseq (launch_auxv inp sp mbase) ph entryw uid gid hw
              (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn) Hrs) as (R1 & R2 & R3 & R4).
  apply Forall_app; split; apply auxw_ok;
  [ lia | exact R1 | rewrite edenot_lit; exact R2 | lia | exact R3 | rewrite edenot_lit; exact R4 ].
- apply Forall_forall. intros K HK. apply in_map_iff in HK as (p & <- & Hp).
  unfold AUXT_UNCLAIMED in Hp.
  repeat (destruct Hp as [<-|Hp];
    [ cbv beta; apply auxt_ok;
      [ cbn [fst]; lia
      | unfold AUXW; cbn [auxv_words auxv_entries flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
        reflexivity ] |]).
  destruct Hp.
Qed.
Lemma init_kn_with_ok : forall atr, kentry_ok segs E0 Mr0 atr -> know_ok segs E0 Mr0 (init_kn_with RZ atr A).
Proof.
intros atr Hatr.
pose proof usp_lo. pose proof usp_hi. pose proof usp_al. pose proof usp_fit.
pose proof len_av. pose proof len_ev. pose proof pad_range. pose proof gap_range. pose proof chead_range.
(* [usp_fit] bounds [usp + |bsb|], so every upper bound below that is stated in
   [CHEAD] -- the AT_RANDOM range's [<= 2^47] first -- needs [length_bsb_sum] to
   connect the two, and [chead_eq] with [RZ_range] for [CHEAD]'s own shape.  The
   OLD proof had neither, because the OLD [e_atrandom] sat at the top of the image
   and read [|bsb|] directly. *)
pose proof chead_eq. pose proof length_bsb_sum. pose proof lstr_lo. pose proof RZ_range. pose proof auxv_count_RZ.
pose proof brk_range as [B1 B2]. pose proof bsb_ge as Gb. pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
pose proof (if_ph _ _ _ IMG) as (P1 & P2 & P3).
destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7).
assert (HL0 : 0 <= L0 <= 131071).
{ unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
unfold init_kn_with.
destruct stack_window_ok as [SW1 SW2].
apply Forall_app; split.
{ apply Forall_cons; [apply kr_ok; rewrite U1; lia|].
apply Forall_cons; [apply kr_ok; rewrite U2; lia|].
apply Forall_cons; [apply kr_ok; unfold eaddz, uE; rewrite mkAlu_denot, edenot_lit, u_add64, u64_lit by lia;
pose proof u_e_atrandom as U; unfold uE in U; rewrite U; rewrite Z.mod_small by lia; lia|].
(* [KRange e_atr8 .. (0xFFFFFFFFFC5 - 4*r)]: [8 * e_atr8 = e_atrandom - 456 - 32*r]
   (YA01.v:720), so the bound IS [usp + CHEAD <= 2^47].  [AUXSZ] unfolded only so
   [lia] sees a linear term in [RZ]. *)
apply Forall_cons; [apply kr_ok; rewrite u_e_atr8; unfold AUXSZ in *; lia|].
apply Forall_cons; [apply kr_ok; rewrite u_e_sp0; lia|].
apply Forall_cons; [apply kr_ok; rewrite u_sp8; lia|].
apply Forall_cons; [apply kr_ok; rewrite U3; lia|].
apply Forall_cons; [apply kr_ok; rewrite U4; lia|].
apply Forall_cons; [apply kr_ok; rewrite U5; lia|].
apply Forall_cons; [apply kr_ok; rewrite uE0_L1; pose proof L1_range; lia|].
apply Forall_cons; [apply kr_ok; rewrite uE0_uid; unfold valid_id in Huid; pose proof (u64_range uid); lia|].
apply Forall_cons; [apply kr_ok; rewrite U6; lia|].
(* [KRange (EVar V_G) 0 1], the plan's new variable at index 9: [uE0] does not
   carry it, so this bullet reads [uE0_G]. *)
apply Forall_cons; [apply kr_ok; rewrite uE0_G; lia|].
apply Forall_cons; [apply kr_ok; rewrite U7; unfold BRK_ASLR in *; lia|].
apply Forall_cons; [exact SW1|].
apply Forall_cons; [exact SW2|].
apply Forall_cons; [exact argc_word_ok|].
apply Forall_cons; [exact argv0_word_ok|].
apply Forall_cons; [exact argv1_word_ok|].
apply Forall_nil. }
repeat (apply Forall_app; split).
(* AT_NULL (pair [26 + 2*RZ]): symbolic in the free field, so no [cbn] closes it. *)
9: exact auxv_null_ok.
(* AT_RANDOM (pair 24): its value is the plan's [e_atrandom RZ]; the two sides are
   equal only by [atr_ptr_eq]. *)
8: apply auxw_ok;
   [ lia
   | unfold AUXW; cbn [auxv_words auxv_entries flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
     reflexivity
   | unfold AUXW; cbn [auxv_words auxv_entries flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
     exact atr_ptr_eq ].
(* pairs 13, 14, 15, 11, 19, 20, 23: all below the CONFIG_RSEQ pair, so the same
   words under both layouts and the reduction never enters the branch. *)
1-7: apply auxw_ok;
   [ lia
   | unfold AUXW; cbn [auxv_words auxv_entries flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
     try reflexivity .. ].
all: try (rewrite edenot_lit; reflexivity).
1: rewrite edenot_lit, P1; reflexivity.
1: rewrite edenot_lit, P2; reflexivity.
1: rewrite edenot_lit, P3; reflexivity.
apply Forall_cons; [exact Hatr|].
apply Forall_cons; [exact kimg_ok|].
apply Forall_cons; [exact rw_window_ok|].
apply Forall_nil.
exact auxt_all_ok.
Qed.
Lemma init_kn_ok : know_ok segs E0 Mr0 (init_kn RZ A).
Proof. exact (init_kn_with_ok _ atrandom_ok). Qed.
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
Lemma stack_len_g : uE E0 (esub (ELit (STACK_END - STACK_LO)) e_sp0) = STACK_END - TOP.
Proof.
pose proof usp_lo as U1. pose proof usp_hi as U2.
unfold esub, uE. rewrite mkAlu_denot. cbn [alu64 alu]. rewrite bv_sub_unsigned, edenot_e_sp0, edenot_lit.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z. unfold STACK_END, STACK_LO, TOP, usp in *.
rewrite u64_lit by lia. rewrite Z.mod_small; lia.
Qed.
Lemma allowA_init_g : allowA A E0 (init_acs_of_g RZ A) =
[(pagedown (img_lo A), pageup (img_lo A + (img_hi A - img_lo A)));
(pagedown (shadow_off A + img_lo A / 8), pageup (shadow_off A + (img_lo A + (img_hi A - img_lo A)) / 8));
(pagedown TOP, pageup (TOP + (STACK_END - TOP)));
(pagedown (shadow_off A + TOP / 8), pageup (shadow_off A + (TOP + (STACK_END - TOP)) / 8))].
Proof.
pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof usp_lo as U1. pose proof usp_hi as U2.
unfold allowA, init_acs_of_g, init_vis_g, stack_side. cbn [a_vis a_ghost app flat_map allow1 fst snd].
unfold sh_lo, sh_hi. cbn [fst snd].
assert (US : uE E0 (eadd e_sp0 (ELit STACK_LO)) = TOP).
{ unfold eadd, uE. rewrite mkAlu_denot. cbn [alu64 alu]. rewrite bv_add_unsigned, edenot_e_sp0, edenot_lit.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z. unfold STACK_LO, TOP, usp in *.
rewrite (Z_to_bv_unsigned 64 (-8388608)). unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
unfold sp_window_hi in U2. lia.
}
rewrite US, stack_len_g. unfold uE. rewrite !edenot_lit, !u64_lit by lia. reflexivity.
Qed.
Lemma abytes_init_g : A_bytes (allowA A E0 (init_acs_of_g RZ A)) <= vis_cost (img_hi A - img_lo A) + vis_cost STACK_VIS
/\ vis_cost (img_hi A - img_lo A) + vis_cost STACK_VIS <= LIMIT.
Proof.
pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof (if_shadow _ _ _ IMG) as S1. pose proof top_ok0 as HT; unfold top_ok, CEIL in HT.
rewrite allowA_init_g. cbn [A_bytes fst snd]. unfold vis_cost, STACK_VIS, STACK_END, LIMIT, target_alloc_limit.
replace (img_lo A + (img_hi A - img_lo A)) with (img_hi A) by lia.
replace (TOP + (140737488355328 - TOP)) with 140737488355328 by lia.
assert (P1 : forall z, z mod 4096 = 0 -> pagedown z = z) by (intros z Hz; unfold pagedown; lia).
assert (P2 : forall z, z mod 4096 = 0 -> pageup z = z) by (intros z Hz; unfold pageup; lia).
rewrite (P1 (img_lo A) I3), (P2 (img_hi A) I4).
pose proof (pageup_minus_pagedown (shadow_off A + img_lo A / 8) (shadow_off A + img_hi A / 8) ltac:(lia)).
pose proof (pageup_minus_pagedown TOP 140737488355328 ltac:(lia)).
pose proof (pageup_minus_pagedown (shadow_off A + TOP / 8) (shadow_off A + 140737488355328 / 8) ltac:(lia)).
split; lia.
Qed.
(* AT_HWCAP is pair 10 at 75d69e00 (StackLayout.v:229-266), not pair 3, and its
   value word is [EVar V_HW] at index 10 of [vals0]. *)
Lemma hw_facts_ok : know_ok segs E0 Mr0 (KRange (EVar V_HW) 0x112D 0x20112D :: auxw 10 16 (EVar V_HW)).
Proof.
pose proof auxv_count_RZ. pose proof RZ_range.
assert (Ehw : edenot E0 (EVar V_HW) = hw) by reflexivity.
apply Forall_cons.
- apply kr_ok. unfold uE. rewrite Ehw. destruct Hhw as [Hhw_gc | Hhw_gcv]; [rewrite Hhw_gc | rewrite Hhw_gcv]; unfold hwcap_rv64gc, hwcap_rv64gcv; rewrite u64_lit by lia; lia.
- apply auxw_ok;
  [ lia
  | unfold AUXW; cbn [auxv_words auxv_entries flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
    reflexivity
  | unfold AUXW; cbn [auxv_words auxv_entries flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
    rewrite Ehw; reflexivity ].
Qed.
(* AT_GID and AT_EGID (pairs 21, 22) are both [gid], the launch variable [V_GID]. *)
Lemma gid_facts_ok : know_ok segs E0 Mr0 (auxw 21 13 (EVar V_GID) ++ auxw 22 14 (EVar V_GID)).
Proof.
pose proof auxv_count_RZ. pose proof RZ_range.
assert (Egid : edenot E0 (EVar V_GID) = gid) by reflexivity.
apply Forall_app; split; (apply auxw_ok;
  [ lia
  | unfold AUXW; cbn [auxv_words auxv_entries flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
    reflexivity
  | unfold AUXW; cbn [auxv_words auxv_entries flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
    rewrite Egid; reflexivity ]).
Qed.
Lemma init_kn_g_ok : know_ok segs E0 Mr0 (init_kn_g RZ A).
Proof.
unfold init_kn_g.
pose proof usp_lo. pose proof usp_al. pose proof usp_fit. pose proof len_av. pose proof len_ev.
pose proof gap_range. pose proof RZ_range. pose proof chead_eq. pose proof chead_range.
pose proof length_bsb_sum. pose proof lstr_lo. pose proof pad_range. pose proof bsb_ge as Gb.
apply Forall_cons; [apply kr_ok; rewrite u_e_atr8; unfold AUXSZ in *; lia|].
apply Forall_app. split; [exact init_kn_ok|].
apply Forall_app. split; [exact hw_facts_ok | exact gid_facts_ok].
Qed.
(* The launch's channel reader, for [cs_ok]'s [co_rdr] field: this Section's [inp] spells
   [in_channel_reader] as the literal [true] (the [inp] above), and [init_model] copies it
   into the model's process state, so the field is proved here and never assumed. *)
Lemma model0_channel_reader : m_channel_reader model0 = true.
Proof. reflexivity. Qed.
Theorem init_cs_ok_g : cs_ok segs A LIMIT TOP SINV0 argH0 (fs_seed_tmp fs tmp) E0 (init_acs_of_g RZ A) R0 FULL0 model0.
Proof.
destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
destruct abytes_init_g as [AB1 AB2].
constructor; cbn [init_acs_of_g a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
- exact init_regs_ok.
- reflexivity.
- exact init_kn_g_ok.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- exists (vdso_reserved (m_kernel model0) (vdso_top (m_vmmaps model0))).
  split; [reflexivity | exact model0_res_bounds].
- reflexivity.
-   unfold model0, TOP. rewrite m_vmmaps_with_vdso, alloc_top_init. unfold stack_max_size. lia.
- reflexivity.
- constructor.
- apply seps_nil.
- unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
unfold model0. apply init_sp_ok_init_model. exact Hsp.
- constructor.
- constructor.
- intros z Hz. exact Hz.
- constructor.
- constructor.
- rewrite app_nil_r, (if_sizes _ _ _ IMG). lia.
- constructor.
- unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
destruct uE0 as (_ & _ & _ & _ & _ & _ & U7). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
rewrite Z.mod_small by lia. lia.
- lia.
- lia.
- exact AB1.
- constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
- intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
- split; [intros; reflexivity | split; [intros; reflexivity | reflexivity]].
- constructor.
- apply incl_appr, incl_refl.
- exact model0_channel_reader.
Qed.
(* STATEMENT CHANGED, old beside new, because [apc] became this Section's Variable
   (the auxv, hence the stack image, reads the entry):
     OLD  forall apc : N, Z.of_N apc = a_entry A -> init_config .. = ..
     NEW  the same equation over the Section's [apc] and [Hapc]
   It is not a weakening: [Z.of_N] is injective, so the old statement follows from
   this one for any [apc'] satisfying [Hapc]'s equation, and consumers pass the
   entry once instead of twice. *)
Theorem init_cfg_eq :
init_config segs apc ph sp brk0 mbase rdraw LIMIT inp = cfg_of segs R0 (a_entry A) FULL0 model0.
Proof.
unfold init_config, cfg_of, model0. cbn [in_argv in_envp in_uid in_hwcap inp].
(* [FULL0] hides one occurrence of [entryw = Z_to_bv 64 (Z.of_N apc)], which
   [rewrite Hapc] cannot see; unfold both so the entry rewrites on BOTH sides. *)
rewrite init_mkst. unfold FULL0, entryw. rewrite Hapc. reflexivity.
Qed.
End c.
