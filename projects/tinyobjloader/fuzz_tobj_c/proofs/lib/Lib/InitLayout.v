(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the entry-stack layout of the new model over the launch's ProcInput: the random bytes at the head's end, then the pad, the strings and execfn; the offsets, the auxv per CONFIG_RSEQ and the image restated, with str_base_eq added and pad_len_lt8 and str_off_mod8 deleted; valid_entry48 gains the launch conjunct; the va_size lemmas re-proved for the input's new conjunct order; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint tab (l : list (list byte)) : nat :=
  match l with
  | [] => 0%nat
  | s :: r => (length s + 1 + tab r)%nat
  end.

Lemma tab_app : forall l1 l2, tab (l1 ++ l2) = (tab l1 + tab l2)%nat.
Proof. induction l1 as [|s l1 IH]; intros l2; cbn; [reflexivity|]. rewrite IH. lia. Qed.

Lemma total_arg_bytes_tab : forall l, total_arg_bytes l = Z.of_nat (tab l).
Proof.
  induction l as [|s l IH]; [reflexivity|].
  unfold total_arg_bytes in *. cbn [fold_right tab]. rewrite IH. lia.
Qed.

Lemma flatten_strings_cons : forall s l, flatten_strings (s :: l) = (s ++ [Z_to_bv 8 0]) ++ flatten_strings l.
Proof. reflexivity. Qed.

Lemma length_flatten_strings : forall l, length (flatten_strings l) = tab l.
Proof.
  induction l as [|s l IH]; [reflexivity|]. rewrite flatten_strings_cons, !length_app, IH. cbn. lia.
Qed.

Lemma length_word_le8 : forall w, length (word_le8 w) = 8%nat.
Proof. reflexivity. Qed.

Lemma length_flat_map_le8 : forall l, length (flat_map word_le8 l) = (8 * length l)%nat.
Proof. induction l as [|w l IH]; [reflexivity|]. cbn [flat_map]. rewrite length_app, IH, length_word_le8. cbn [length]. lia. Qed.

Lemma string_addrs_fst_length : forall base l, length (fst (string_addrs base l)) = length l.
Proof.
  intros base l. revert base. induction l as [|s l IH]; intros base; [reflexivity|].
  cbn. specialize (IH (base + len_word s + 1)%bv).
  destruct (string_addrs (base + len_word s + 1)%bv l) as [ptrs final]. cbn in *. now rewrite IH.
Qed.

Lemma length_build_auxv : forall l, length (build_auxv l) = (16 * length l)%nat.
Proof.
  induction l as [|[t v] l IH]; [reflexivity|]. cbn [build_auxv flat_map fst snd].
  rewrite !length_app, !length_word_le8. cbn [length]. fold (build_auxv l). rewrite IH. lia.
Qed.

Section Layout.
(* THE SECTION BINDS [inp] AND RE-EXPOSES THE OLD NAMES AS NOTATIONS OVER IT.
   Donor, STATEMENT:
     the openssl/ct statement:
       projects/openssl/ct/proofs/lib/P/InitMem.v:335-339
   which is what makes this island portable at all.

   WHY IT IS A CORRECTNESS FIX AND NOT AN ERGONOMIC ONE.  Before this restatement [argv], [envp],
   [uid] and [hwcap] were FREE SECTION VARIABLES while [bsb] was built from [entry_stack_image
   inp ..], which reads [in_argv inp], [in_envp inp], [in_uid inp] and [in_hwcap inp].  Nothing
   tied the two: the offsets below described one argv and the image described another, so the
   decomposition lemmas could not have been proved however their statements were written.  As
   notations the names now ARE the projections, so [bsb] and every offset speak about the same
   list, and every line below that says [argv] keeps working unchanged -- the name resolves, now
   to a field of [inp] rather than to a section variable.

   It is also what keeps the 41 files that depend on this section from needing new arguments:
   a notation adds no section parameter, where a [Variable] or a [Let] would.

   [build_stack_bytes] takes TWELVE parameters
   (rocq-linux-process-semantics@75d69e00:theories/LinuxProcessSem/StackLayout.v:483-485), and
   none of them has to be sourced here, because Common/PropExec.v:2495-2500 packages them (at
   b84e73ef, whose [launch_auxv] takes the entry's stack pointer):
   [entry_stack_image inp mbase ph entry sp draw = build_stack_bytes (launch_auxv inp sp mbase) ph
   entry sp (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) (in_uid inp) (in_gid inp)
   (in_hwcap inp) draw] by [reflexivity].

   [rseq] reaches the kernel field by conversion too: :2506-2508 gives
   [la_rseq (launch_auxv inp sp mbase) = kb_rseq (in_kernel inp)] by [reflexivity], so every offset
   below is parametric in [kb_rseq] and pins nothing. *)
Variable inp : ProcInput.
Variable mbase : word.
Variable ph : PhdrInfo.
Variable entry : word.
Variable sp : word.
Variable draw : EntryDraw.
Local Notation argv := (in_argv inp).
Local Notation envp := (in_envp inp).
Local Notation execfn := (in_execfn inp).
Local Notation uid := (in_uid inp).
Local Notation hwcap := (in_hwcap inp).
Local Notation top := (ed_top draw).
Local Notation rseq := (kb_rseq (in_kernel inp)).

(* THE PREMISE [bsb_decomp]'s STRING-BASE BRIDGE RESTS ON, and the one this copy of
   [valid_entry48] was short until this file's fifth conjunct was added.

   rocq-linux-process-semantics@75d69e00:theories/LinuxProcessSem/Run.v:3641-3646:
     launch_sp_hi top inp
       = align_down16 (bv_unsigned top - 8 - launch_string_bytes argv envp execfn)
         - block_head_size (kb_rseq (in_kernel inp)) argv envp
   so [sp <= launch_sp_hi top inp] gives
     sp + block_head_size <= align_down16 (top - 8 - lsb) <= top - 8 - lsb
   i.e. exactly the non-negativity of
     block_pad_len rseq sp top argv envp execfn
       = Z.to_nat (top - 8 - lsb - sp - block_head_size)      (ibid.:439-444)
   which is what turns the definitional identity
     sp + cat_string_off = top - 8 - launch_string_bytes
   into an equation about [nat] offsets rather than about [Z].

   HOW EVERY CONSUMER DISCHARGES IT, with no new text at any call site: this is the second half
   of the second conjunct of [valid_launch_sp (ed_top draw) inp sp] (ibid.:3656-3658), which is
   the second conjunct of [entry_launch_ok_va Sv48 _ inp] (ibid.:3723-3729), which is the FIFTH
   conjunct of [valid_entry48] below -- and the ~14 consumers already state [valid_entry48] as a
   [Hypothesis] (A/TopClosed.v:288 and its B/, P/, U/ twins), deriving it from
   [valid_input_either] through [valid_entry48_of_input_either]. *)
Hypothesis Hsp_hi : (bv_unsigned sp <= launch_sp_hi top inp)%Z.

Definition argc : nat := length argv.
Definition envc : nat := length envp.

(* THE OFFSETS KEEP THEIR NAMES AND CHANGE ONLY THEIR BODIES, which the keep-the-names experiment
   (measured) shows to be safe for the eleven tbs__
   files that carry these names: 233 compiled, 10 of 43 PGSZ-naming blob files clean under a
   changed body, zero encoded proof terms failing.

   [aux_off] is UNCHANGED IN VALUE: [block_items argv envp] is [length argv + length envp + 3]
   (StackLayout.v:385-386), so the old [24 + 8 * argc + 8 * envc] is exactly [8 * block_items],
   the 24 being 8 * 3 -- argc, the argv NULL and the envp NULL.  Re-pointed to the model's name so
   it moves with the model rather than restating it.

   [str_off] is the distance from [sp] to the STRING block, and that is the model's
   [cat_string_off] (CatExec.v:430-432) = [block_head_size rseq argv envp + block_pad_len rseq sp
   top argv envp execfn].  [block_head_size] (StackLayout.v:399-401) is
   [8 * items + auxv_size rseq + 8 * (items mod 2) + 16], which supplies all three things the old
   body lacked: the rseq-dependent vector size in place of the literal 160 (which was 10 pairs x
   16, the old fixed count, against [auxv_size] = 16 * (29 or 27) = 464 or 432), the
   [8 * (items mod 2)] zero gap between the vector and the random block, and the trailing 16. *)
Definition aux_off : nat := (8 * block_items argv envp)%nat.
(* [cat_string_off rseq sp top argv envp execfn] spelled out as its own body.  The name itself is
   NOT reachable here: it is defined in the shared proof library's [Common/CatExec.v:430-432],
   which this tree does not vendor (measured: naming it gives
   "The reference cat_string_off was not found in the current environment" at this line).  Its body
   is the sum of two functions that ARE reachable, both from [StackLayout], which this file already
   requires at the top: [block_head_size] (StackLayout.v:399-401) and [block_pad_len]
   (StackLayout.v:439-444).  So the sum is written out rather than the definition vendored -- no
   new Require, and in particular no Require placed after the scope block at :12-13, which would
   reopen [bv_scope] over every numeral in this file. *)
Definition str_off : nat :=
  (block_head_size rseq argv envp + block_pad_len rseq sp top argv envp execfn)%nat.
Definition env_str_off : nat := (str_off + tab argv)%nat.
Definition raw_len : nat := (env_str_off + tab envp)%nat.
Definition pad_len : nat := block_pad_len rseq sp top argv envp execfn.
(* THE IMAGE ORDER CHANGED, so these two no longer denote what the old bodies computed.
   [build_stack_bytes] lays [head ++ repeat 0 pad ++ strs ++ repeat 0 8] with [at_random_bytes]
   INSIDE the head, above the vector and BELOW the pad and the strings -- not last, as the old
   [raw_len + pad_len] assumed.  The random block therefore begins at the end of the head:
   the donor:
     projects/cgif/cgif_file_fuzzer/proofs/lib/YK12.v:311-314 (STATEMENT) states exactly that --
     [bsb_random_split : exists pre post, bsb = pre ++ at_random_bytes (ed_random rdraw) ++ post
      /\ length pre = (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp) - 16)].
   [img_len] is the whole image, which [length_build_stack_bytes] gives as
   [cat_string_off + launch_string_bytes + 8] (the trailing 8 is the final zero word). *)
Definition rand_off : nat := (block_head_size rseq argv envp - 16)%nat.
Definition img_len : nat := (str_off + launch_string_bytes argv envp execfn + 8)%nat.


(* [comment removed for export] *)
Definition str_base : word := (sp + nat_to_word str_off)%bv.
(* THE BRIDGE. [build_stack_bytes] lays the strings from [string_base_addr top argv envp execfn]
   = [top - nat_to_word (8 + launch_string_bytes argv envp execfn)]
   (rocq-linux-process-semantics@75d69e00:theories/LinuxProcessSem/StackLayout.v:414-416), while
   this file measures them as [sp + nat_to_word str_off].  THE TWO ARE THE SAME ADDRESS, and
   definitionally so: with [str_off = block_head_size + block_pad_len] and [block_pad_len] defined
   (ibid.:439-444) as [Z.to_nat (top - 8 - lsb - sp - block_head_size)], the [block_head_size]
   cancels and
     sp + str_off = top - 8 - launch_string_bytes argv envp execfn
   for every rseq, sp and top -- the pad IS the slack that makes the two meet.
   (Derived here, and it is also why
   openssl/ct's [ed_top - 8 - str_len] and cgif's [sp + cat_string_off] are one address written
   from opposite ends.)
   The cancellation is in Z and the [Z.to_nat] is not, so it needs the pad to be non-negative --
   which is exactly [Hsp_hi]. *)
Lemma str_base_eq : string_base_addr top argv envp execfn = str_base.
Proof using Hsp_hi.
  (* ORDER MATTERS AND IS THE DONOR'S.  [rewrite Nat2Z.inj_add] while the sum is still
     under [nat_to_word] fails at this line (measured) with
       Found no subterm matching "Z.of_nat (?M + ?M)" in the current goal.
     cgif proves the same identification as a named lemma and peels the [bv] layer FIRST,
     in the donor's proof:
         projects/cgif/cgif_file_fuzzer/proofs/lib/YK0h.v:328-343  (PROOF only)
         [cat_string_base_offset] -- apply bv_eq, then the bv rewrites, and only then
         [Nat2Z.inj_add] / [Z2Nat.id].
     Warrant (rule 15): YK0h.v was green in cgif's 2026-11-04T16:11 run with the control (YZ00)
     firing; YA0a.v and YA02.v were NOT, which is why the citation is YK0h and not YA0a.  That
     log carries no extractable ossv-source, so this is "green in that run", not "green at the
     text ported here": the warrant is the donor's text in that run, not this file's text
     in any run. *)
  assert (Hnn : (0 <= bv_unsigned top - 8
                      - Z.of_nat (launch_string_bytes argv envp execfn)
                      - bv_unsigned sp
                      - Z.of_nat (block_head_size rseq argv envp))%Z).
  { (* [align_down16_le] is the donor's name and lives in the model's
       [Checks/Cases/EntryLaunch.v], which this file does not import.  Unfolding and using the
       stdlib bound instead keeps the whole assertion inside names this cone certainly has. *)
    unfold launch_sp_hi, align_down16 in Hsp_hi.
    pose proof (Z.mod_pos_bound (bv_unsigned top - 8
                   - Z.of_nat (launch_string_bytes argv envp execfn)) 16 ltac:(lia)).
    lia. }
  (* THREE BORROWED NAMES, ONE CAUSE -- recorded because the pattern is the point.
     [u64_range] lives in the shared library's [Common/PropExec.v:461], which
     this tree does not vendor; [bv_unsigned_sub] does not exist anywhere -- the
     tree's name is [bv_sub_unsigned], the OTHER WORD ORDER, 22 files; and
     [bv_unsigned_nat_to_word] likewise does not exist -- this tree handles [nat_to_word] by
     [unfold], 4 uses, not by a lemma.
     Verified present in THIS cone, excluding this file: bv_sub_unsigned 22, bv_add_unsigned 91,
     Z_to_bv_unsigned 299, bv_unsigned_in_range 103.
     THE TEST IS NOT "DOES THIS LEMMA EXIST" BUT "DOES IT EXIST IN THE TARGET'S CONE, SPELLED
     THIS WAY" -- and a hit count of 1 is not a pass when the 1 is the file you are editing. *)
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 top) as Rtop.
  apply bv_eq.
  (* THE NAT LAYER IS RESOLVED BEFORE THE BV LAYER, not after.  In the other order the
     proof stops here (measured) with
       Found no subterm matching "Z.of_nat (Z.to_nat ?M)" in the current goal
     because [unfold str_off, pad_len, block_pad_len] run AFTER [Z_to_bv_unsigned] exposes the
     [Z.to_nat] only under the [bv_wrap] those rewrites introduce, and
     [Z2Nat.id] cannot see it there.  Unfolding [nat_to_word] already puts [Z.of_nat str_off] in the
     goal, so [str_off], [pad_len] and [block_pad_len] can come out in the same breath and the
     whole nat-level simplification finishes before any bv rewrite touches the term.
     THIS IS THE SECOND ORDERING CONSTRAINT IN THIS ONE PROOF -- :204 is the same one in the
     opposite direction, [Nat2Z.inj_add] only after the bv layer is peeled.  Both are tactic
     ORDER and not content, so where either fails the fix is the order, not another lemma
     name. *)
  unfold string_base_addr, str_base, nat_to_word, str_off, pad_len, block_pad_len.
  (* [!] MATTERS HERE.  The goal is
       top - nat_to_word (8 + launch_string_bytes ..) = sp + nat_to_word str_off
     and BOTH sides carry a [Z.of_nat] of a sum once [nat_to_word] is unfolded: the left is
     [Z.of_nat (8 + lsb)], the right is [Z.of_nat (block_head_size + block_pad_len)].
     A bare [rewrite Nat2Z.inj_add] fires ONCE, on the LEFT, and leaves the right side's sum
     intact -- so [Z2Nat.id] finds no [Z.of_nat (Z.to_nat _)] and reports
     "Found no subterm matching", which reads like a missing lemma and is a missing [!].
     Ruled out by READING THE SOURCE, not by another build:
     [nat_to_word] IS [Z_to_bv 64 (Z.of_nat n)] (BvBase.v:36), and [block_pad_len] IS a plain
     [Definition] ending in [Z.to_nat] (StackLayout.v:439-444), so neither "it does not unfold"
     nor "the Z.of_nat came from elsewhere" is the cause. *)
  rewrite !Nat2Z.inj_add, Z2Nat.id by exact Hnn.
  rewrite bv_sub_unsigned, bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64%N) with (2 ^ 64)%Z.
  change (bv_modulus 64%N) with (2 ^ 64)%Z in Rsp, Rtop.
  (* THE [lia] AT THE END OF THIS PROOF NEEDS THE TWO INNER [mod]s GONE; NO FACT IS
     MISSING.  With them the [lia] alone fails with "No applicable tactic.": in this tree [lia]
     is REDEFINED as [first [ lia_noeuclid | lia_euclid ]] (Lib/LiaFast.v:23), so that message is
     that [first] running out, not a tactic that does not exist.

     What [f_equal] hands it without the two rewrites below is
       bv_unsigned top - (8 + Z.of_nat lsb) mod 2^64
         = bv_unsigned sp + (Z.of_nat bhs + (top - 8 - lsb - sp - bhs)) mod 2^64
     -- still two [mod]s.  To drop them [lia] must show each operand is already in [0, 2^64),
     and [launch_string_bytes] has NO upper bound of its own: the only one available is
     [bv_unsigned top < bv_modulus 64], and the goal says [2 ^ 64] while that hypothesis says
     [bv_modulus 64], two atoms [lia] cannot relate.  So the euclidean arm has an unbounded
     quantity and both arms fail.

     [Zminus_mod_idemp_r] and [Zplus_mod_idemp_r] (ZArith, no side condition -- they hold for
     [n = 0] too) delete both inner [mod]s outright, after which [f_equal] leaves a PURELY LINEAR
     equation in which [Z.of_nat bhs] cancels against itself and no bound is needed at all.

     Measured, not assumed: the rseq flag is NOT what breaks this [lia].  [block_head_size] is
     never unfolded in this proof -- the [unfold] at :243 names [string_base_addr], [str_base],
     [nat_to_word], [str_off], [pad_len], [block_pad_len] and not it -- so [auxv_size rseq] is
     never exposed and [lia] sees [Z.of_nat (block_head_size rseq argv envp)] as one non-negative
     atom that cancels.  Control for that zero: the four proofs in this file that DO unfold it
     are :297, :413, :487 and :501.  No [rseq_z]/[rz_range] range lemma is
     added here, because there is no rseq-dependent integer in this goal to bound.

     [Z.sub_mod_idemp_r] is NOT the name to reach for: 0 files on this branch, against
     [Zminus_mod_idemp_r] 1499, [Zplus_mod_idemp_r] 3517, [Zminus_mod_idemp_l] 3410 and
     [Zplus_mod_idemp_l] 7724 -- the four siblings are the firing control for that zero.

     The class is ONE site in this file.  The only other two proofs that reach [f_equal. lia.]
     under an unfolded [bv_wrap] are :551 and :566, and both already clear their [mod]s first
     with [mod_add_outer]/[mod_add_inner] (:526-536); they are not in this class.  [Rsp]/[Rtop]
     are named and restated at [2 ^ 64] anyway: a true hypothesis in a [lia] context is
     monotone, so it cannot cost anything, and it removes the atom mismatch for good. *)
  rewrite !Zminus_mod_idemp_r, !Zplus_mod_idemp_r.
  f_equal. lia.
Qed.
Definition argv_ptrs : list word := fst (string_addrs str_base argv).
Definition env_str_base : word := snd (string_addrs str_base argv).
Definition envp_ptrs : list word := fst (string_addrs env_str_base envp).

(* Stated over the model's PACKAGED form, which is the shape three files in cgif already use and
   carry their lemmas against:
   the donor:
     projects/cgif/cgif_file_fuzzer/proofs/lib/YA0a.v:87  (also YA02.v:85, YK12.v:107)
   This is CONVERTIBLE to the twelve-argument call -- [entry_stack_image_block] at
   rocq-linux-process-semantics@75d69e00:theories/Common/PropExec.v:2495-2500 proves the two equal
   by [reflexivity] -- so a proof that must see inside the block writes
   [rewrite entry_stack_image_block].  Kept as a [Definition] rather than cgif's [Let], because 41
   files in this tree name [bsb] and a section-local [Let] would withdraw it. *)
Definition bsb : list byte := entry_stack_image inp mbase ph entry sp draw.

(* [pad_len_lt8] IS GONE: IT IS FALSE AT THIS REVISION, not merely unproven.
   Its old proof applied [Z.mod_pos_bound] to the OLD body [(8 - raw_len mod 8) mod 8], which was
   bounded by 8 by construction.  [pad_len] is now [block_pad_len], and the model bounds that
   BETWEEN 0 AND 4095 (rocq-linux-process-semantics@75d69e00:theories/LinuxProcessSem/
   StackLayout.v:429-438): it is whatever [arch_align_stack] leaves, and :470-480 says it is
   "the draw plus the alignment remainder".  No premise available here makes it less than 8 --
   [valid_launch_sp] constrains [sp], not the draw.  A lemma the revision makes false does not
   survive in any form, so it is deleted rather than weakened to fit its consumer. *)

(* [rand_off] is a multiple of 8 and this SURVIVES: [block_head_size] is
   [8 * items + auxv_size rseq + 8 * (items mod 2) + 16] (StackLayout.v:399-401), every term of
   which is a multiple of 8 because [auxv_size rseq] is [16 * (29 or 27)], and subtracting 16
   keeps it so.  Proof ported from
   the donor:
     projects/cgif/cgif_file_fuzzer/proofs/lib/YK12.v:343-364   (PROOF only)
   THE LITERALS BELOW ARE CORRECT AND DELIBERATE: [16 * 29] and [16 * 27] appear INSIDE a
   [destruct] on [kb_rseq], with both branches discharged.  That is the two-closed-instantiations
   form, which is what a layout parametric in [kb_rseq] requires in a proof -- it is NOT the
   forbidden literal, which is one that pins the extent in a STATEMENT.  Anyone "fixing" this
   case split away breaks a correct proof. *)
Lemma rand_off_mod8 : Z.of_nat rand_off mod 8 = 0.
Proof using .
  unfold rand_off, block_head_size, auxv_size, auxv_count.
  destruct (kb_rseq (in_kernel inp)).
  - change (16 * 29)%nat with 464%nat. rewrite !Nat2Z.inj_sub by lia.
    rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. lia.
  - change (16 * 27)%nat with 432%nat. rewrite !Nat2Z.inj_sub by lia.
    rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. lia.
Qed.

(* [str_off_mod8] IS GONE: FALSE AT THIS REVISION, same cause as [pad_len_lt8].
   [str_off] is now [block_head_size + block_pad_len].  The head is a multiple of 8; THE PAD IS
   NOT, being the draw in [0,4095] plus an alignment remainder.  Its old proof rewrote the literal
   [24 + 8*argc + 8*envc + 160] into [8 * (23 + argc + envc)], which only ever worked because the
   vector was a fixed 160 bytes and there was no pad below the strings.
   CONSUMER: Lib/InitState.v:479-480 poses this and [pad_lt8] into one [repeat split; try lia]
   inside [nums], whose own statement is a [tb__] blob.  Whether that [lia] needs 8-alignment of
   [str_off] cannot be read from the script and needs [Print nums.] under -vok.  Deleting first is
   deliberate: the ruling is that a false lemma does not survive in any form, so the consumer is
   repaired against whatever it actually needs rather than the lemma being kept to satisfy it. *)

(* [comment removed for export] *)
(* [at_random_ptr] GAINED THE [rseq] ARGUMENT -- a fifth arity fault in this file, and the one
   that makes this lemma collapse to [reflexivity].
   rocq-linux-process-semantics@75d69e00:theories/LinuxProcessSem/StackLayout.v:425-427:
     at_random_ptr (sp : word) (rseq : bool) (argv envp : list (list byte)) : word :=
       sp + nat_to_word (block_head_size rseq argv envp - 16)
   and [rand_off] is DEFINED above as [block_head_size rseq argv envp - 16], so the two sides are
   the same term.  The old proof computed the old [raw_len + pad_len] offset by hand against a
   literal [auxv_size]; there is nothing left to compute. *)
Lemma at_random_ptr_eq : at_random_ptr sp rseq argv envp = (sp + nat_to_word rand_off)%bv.
Proof using . unfold at_random_ptr, rand_off. reflexivity. Qed.

(* [comment removed for export] *)
Definition hdr_bytes : list byte :=
  word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0).
Definition env_bytes : list byte := flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0).
(* [auxv_bytes] takes EIGHT parameters at 75d69e00
   (rocq-linux-process-semantics@75d69e00:theories/LinuxProcessSem/StackLayout.v:268-271):
   [la ph entry uid gid hwcap at_random at_execfn].  The old call passed four.  The two pointer
   arguments are the ones [build_stack_bytes] itself passes (StackLayout.v:490-493):
   [at_random_ptr sp (la_rseq la) argv envp] -- which gained the [rseq] argument -- and
   [at_execfn_ptr top execfn]. *)
Definition auxv : list byte :=
  auxv_bytes (launch_auxv inp sp mbase) ph entry uid (in_gid inp) hwcap
    (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn).
Definition rand_bytes : list byte := at_random_bytes (ed_random draw).

(* [bsb_decomp] states the random block as the FOLDED name [rand_bytes], so after
   [rewrite bsb_decomp, !length_app] the goal holds [length rand_bytes] and NOT
   [length (at_random_bytes _)] -- which is why [rewrite length_at_random_bytes] reported
   "Found no subterm matching length (at_random_bytes ?M)" at :448.  That is a FOLD/UNFOLD
   mismatch and NOT the image reorder: [at_random_bytes] is unchanged at the revision
   (rocq-linux-process-semantics@75d69e00:theories/LinuxProcessSem/StackLayout.v:365, with
   [length_at_random_bytes] at :375 still giving 16), and [bsb_decomp] does place the block
   inside the head exactly as the comment above says.  Naming the composed fact once fixes
   both consumers and removes the unfold-ordering hazard.  The class is exactly two sites,
   [length_bsb] and [region_strs]; [region_rand]'s witness prefix stops before the block, so
   it never forms [length rand_bytes] and is not in the class. *)
Lemma length_rand_bytes : length rand_bytes = 16%nat.
Proof using . unfold rand_bytes. apply length_at_random_bytes. Qed.

(* THE NEW IMAGE ORDER, read off [build_stack_bytes]'s own body
   (rocq-linux-process-semantics@75d69e00:theories/LinuxProcessSem/StackLayout.v:486-505), not
   inferred:
     head ++ repeat 0 pad ++ strs ++ repeat 0 8
   with
     head = argc word ++ argv ptrs ++ NUL ++ envp ptrs ++ NUL
            ++ auxv ++ repeat 0 (8 * (items mod 2)) ++ at_random_bytes (ed_random draw)
     strs = flatten_strings argv ++ flatten_strings envp ++ execfn ++ [0]
   So AT_RANDOM sits INSIDE the head -- above the vector, BELOW the pad and the strings -- where
   the old statement had it LAST, after the strings, with the pad between.  Those were two
   different images, which is why this is a rewrite and not a re-point.
   Corroborated three ways: this reading of [build_stack_bytes]; G4's glaze plan cores derived
   separately from the model (projects/glaze/binary_reflection/proofs/lib/
   AzPlanCore.v:3615-3626, ascending e_auxv -> auxv -> 8-byte gap -> AT_RANDOM -> pad -> strings);
   and the random block's offset in
   the donor:
     projects/cgif/cgif_file_fuzzer/proofs/lib/YK12.v:311-314 (STATEMENT), which puts it at
     [block_head_size .. - 16], i.e. at the head's end. *)
Lemma bsb_decomp :
  bsb = hdr_bytes ++ env_bytes ++ auxv
        ++ repeat (Z_to_bv 8 0) (8 * (block_items argv envp mod 2))
        ++ rand_bytes
        ++ repeat (Z_to_bv 8 0) pad_len
        ++ flatten_strings argv ++ flatten_strings envp ++ execfn ++ [Z_to_bv 8 0]
        ++ repeat (Z_to_bv 8 0) 8.
Proof using Hsp_hi.
  (* A REASSOCIATION OF [build_stack_bytes]'s OWN BODY, once the two string bases are identified.
     [str_base_eq] does that identification and is the only step needing [Hsp_hi]; everything
     after it is the definition's own append chain read in the new order.
     Shape taken from the donor:
       projects/cgif/cgif_file_fuzzer/proofs/lib/YK12.v:315-325 (PROOF only) -- which unfolds
       [bsb, entry_stack_image] and destructures the [string_addrs] pairs the same way.
     Warrant on that donor (rule 15): YK12.v was green in cgif's 2026-11-04T16:11 run with the
     control firing, and that log carries no extractable ossv-source, so it is "green in that run"
     rather than "green at the text ported here". *)
  unfold bsb, entry_stack_image, build_stack_bytes, hdr_bytes, env_bytes, auxv, rand_bytes,
    argv_ptrs, envp_ptrs, env_str_base, pad_len.
  cbv zeta.
  rewrite str_base_eq.
  cbn [launch_auxv la_rseq].
  destruct (string_addrs str_base argv) as [aptrs esb] eqn:Ea. cbn [fst snd].
  destruct (string_addrs esb envp) as [eptrs fin] eqn:Ee. cbn [fst snd].
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma length_hdr_bytes : length hdr_bytes = (16 + 8 * argc)%nat.
Proof using .
  unfold hdr_bytes, argv_ptrs, argc. rewrite !length_app, length_flat_map_le8, !length_word_le8, string_addrs_fst_length. lia.
Qed.

Lemma length_env_bytes : length env_bytes = (8 * envc + 8)%nat.
Proof using .
  unfold env_bytes, envp_ptrs, envc. rewrite length_app, length_flat_map_le8, length_word_le8, string_addrs_fst_length. lia.
Qed.

(* The vector's length is [auxv_size rseq], never a literal: 16 * 29 = 464 or 16 * 27 = 432
   (rocq-linux-process-semantics@75d69e00:theories/LinuxProcessSem/StackLayout.v:276-277).
   The old [160] was ten pairs x 16, the pre-retarget fixed count.  The model's own
   [length_auxv_bytes] (ibid.:279-284) closes it, and [cbn [launch_auxv la_rseq]] reconciles its
   [la_rseq (launch_auxv inp sp mbase)] with this section's [rseq] notation -- equal by
   [reflexivity] (Common/PropExec.v:2506-2508 at b84e73ef) but not syntactically. *)
Lemma length_auxv : length auxv = auxv_size rseq.
Proof using . unfold auxv. rewrite length_auxv_bytes. cbn [launch_auxv la_rseq]. reflexivity. Qed.

(* [img_len] = [str_off + launch_string_bytes + 8]: the head and pad are [str_off] by definition,
   the strings are [launch_string_bytes argv envp execfn], and the trailing zero word is the 8. *)
Lemma length_bsb : length bsb = img_len.
Proof using Hsp_hi.
  rewrite bsb_decomp, !length_app, length_hdr_bytes, length_env_bytes, length_auxv,
    !length_flatten_strings, !repeat_length, length_rand_bytes.
  (* [pad_len] MUST COME OUT WITH [str_off], and leaving it in is why the [lia] at this line
     failed once the rewrite above started firing.  [!repeat_length] turns [bsb_decomp]'s
     [repeat 0 pad_len] into the FOLDED atom [pad_len], while [unfold str_off] turns the
     right-hand side into [block_head_size + block_pad_len rseq sp top argv envp execfn].
     Those are the same quantity under two names ([pad_len] IS [block_pad_len ..], :162), and
     [lia] sees two unrelated atoms that will not cancel.  Same fold/unfold family as the
     [rand_bytes] fix above, one line later in the same proof.
     [block_pad_len] itself is deliberately NOT unfolded: both sides then carry the identical
     atom and cancel, whereas unfolding it exposes a [Z.to_nat] that [lia] handles worse.
     [str_base_eq] at :243 is the in-file donor for the pairing, and the comment at :236-237
     says it outright -- "[str_off], [pad_len] and [block_pad_len] can come out in the same
     breath". *)
  (* AND THE FOLD FAMILY IS LARGER THAN THE PARAGRAPH ABOVE SAYS.  MEASURED by printing the
     goal (a goal probe; the probe text and its output are in the pull request's probe
     commits):
       16 + 8*argc + (8*envc + 8 + (auxv_size rseq + (8*((length argv + length envp + 3) mod 2)
         + (16 + (block_pad_len .. + (tab argv + (tab envp + (length execfn + (1 + 8))))))))) =
       8*(length argv + length envp + 3) + auxv_size rseq
         + 8*((length argv + length envp + 3) mod 2) + 16 + block_pad_len ..
         + (length (flatten_strings argv) + length (flatten_strings envp) + length execfn + 1) + 8
     [block_pad_len ..] is ALREADY the same atom on both sides, so leaving it folded was right
     and [pad_len] belonged in the list -- but neither was the obstacle.  The unmatched pairs
     are [tab argv]/[tab envp] against [length (flatten_strings ..)], and [argc]/[envc]
     (:128-129) against [length argv]/[length envp]. *)
  (* AND [tab] MUST NOT BE UNFOLDED -- MEASURED on the farm.  Unfolding it leaves the raw
     [fix tab ..] on the left while the right still reads [length (flatten_strings ..)],
     which is two atoms again (measured with a goal probe, whose
     ZZPROBE-A goal prints the [fix] verbatim).  The right-hand side's
     [length (flatten_strings ..)] is EXPOSED BY [unfold launch_string_bytes], which happens
     AFTER the [!length_flatten_strings] at :463, so that rewrite never saw it.  Running the
     rewrite again, after the unfold, folds both sides to [tab]. *)
  unfold img_len, str_off, pad_len, block_head_size, launch_string_bytes, block_items,
    argc, envc.
  rewrite !length_flatten_strings.
  cbn [length]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nth_error_app_off : forall {A} (l1 l2 : list A) j,
  nth_error (l1 ++ l2) (length l1 + j) = nth_error l2 j.
Proof using . intros A l1 l2 j. rewrite nth_error_app2 by lia. f_equal. lia. Qed.

(* [comment removed for export] *)
Definition region (o : nat) (seg : list byte) : Prop :=
  exists pre post, bsb = pre ++ seg ++ post /\ length pre = o.

Lemma region_nth : forall o seg j, region o seg -> (j < length seg)%nat ->
  nth_error bsb (o + j) = nth_error seg j.
Proof using .
  intros o seg j (pre & post & E & L) Hj. rewrite E, <- L, nth_error_app_off.
  apply nth_error_app1. exact Hj.
Qed.

Lemma region_app_l : forall o l1 l2, region o (l1 ++ l2) -> region o l1.
Proof using Hsp_hi.
  intros o l1 l2 (pre & post & E & L). exists pre, (l2 ++ post). rewrite E, <- !app_assoc. auto.
Qed.

Lemma region_app_r : forall o l1 l2, region o (l1 ++ l2) -> region (o + length l1) l2.
Proof using Hsp_hi.
  intros o l1 l2 (pre & post & E & L). exists (pre ++ l1), post.
  rewrite E, <- !app_assoc, length_app, L. auto.
Qed.

Lemma region_at : forall pre seg post o,
  bsb = pre ++ seg ++ post -> length pre = o -> region o seg.
Proof using . intros pre seg post o E L. exists pre, post. auto. Qed.

Lemma region_hdr : region 0 hdr_bytes.
(* LPS 75d69e00: [bsb_decomp] rests on [Hsp_hi], so this proof does too.  It is NOT a new
   dependency -- it comes with [bsb_decomp]: this [Qed] is checked only once every proof above
   it compiles, so an error count without it says nothing about it; an error count counts
   what the build reaches. *)
Proof using Hsp_hi.
  eapply (region_at []); [|reflexivity]. rewrite bsb_decomp. reflexivity.
Qed.

Lemma region_env : region (16 + 8 * argc) env_bytes.
Proof using Hsp_hi.
  eapply (region_at hdr_bytes); [rewrite bsb_decomp; reflexivity|]. apply length_hdr_bytes.
Qed.

Lemma region_auxv : region aux_off auxv.
Proof using Hsp_hi.
  eapply (region_at (hdr_bytes ++ env_bytes)).
  - rewrite bsb_decomp, <- !app_assoc. reflexivity.
  (* Same fold family as [length_bsb]:490.  [length_hdr_bytes] and [length_env_bytes] deliver
     [16 + 8 * argc] and [8 * envc + 8] while [aux_off] unfolds to [8 * block_items argv envp],
     and [lia] sees THREE unrelated atoms.  [argc]/[envc] (:128-129) and [block_items] have to
     come out together, exactly as at :495-496.  NOT the [Hsp_hi] family: :550 already
     declares it and that fix held. *)
  - rewrite length_app, length_hdr_bytes, length_env_bytes.
    unfold aux_off, block_items, argc, envc. lia.
Qed.

(* THE OFFSETS ARE UNCHANGED AND ONLY THE PREFIXES MOVE -- the payoff of keeping every offset's
   name and changing only its body.  New order (bsb_decomp above):
     hdr ++ env ++ auxv ++ gap ++ rand ++ pad ++ strs ++ execfn ++ [0] ++ trailing8
   and the prefix lengths still land exactly on the old names:
     hdr ++ env                     = 8 * block_items                  = aux_off
     ... ++ auxv ++ gap             = block_head_size - 16             = rand_off
     ... ++ rand ++ pad             = block_head_size + block_pad_len  = str_off
   so these two statements survive the reorder verbatim and only their [region_at] witnesses
   change.  [region_auxv] above needs no change at all, its prefix being [hdr ++ env]. *)
Lemma region_strs : region str_off (flatten_strings argv ++ flatten_strings envp).
Proof using Hsp_hi.
  eapply (region_at
            (hdr_bytes ++ env_bytes ++ auxv
             ++ repeat (Z_to_bv 8 0) (8 * (block_items argv envp mod 2))
             ++ rand_bytes ++ repeat (Z_to_bv 8 0) pad_len)
            _
            (execfn ++ [Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) 8)).
  - rewrite bsb_decomp, <- !app_assoc. reflexivity.
  - rewrite !length_app, length_hdr_bytes, length_env_bytes, length_auxv, !repeat_length,
      length_rand_bytes.
    (* Second and last site of the [pad_len] class: [!repeat_length] exposes the folded
       [pad_len] and [unfold str_off] unfolds the other copy.  [region_rand] below is NOT in
       the class -- its witness prefix stops before the pad, so its [repeat_length] is the
       [8 * (items mod 2)] gap, and it unfolds [rand_off], which carries no [block_pad_len]. *)
    unfold str_off, pad_len, block_head_size, block_items, argc, envc. lia.
Qed.

Lemma region_rand : region rand_off rand_bytes.
Proof using Hsp_hi.
  eapply (region_at
            (hdr_bytes ++ env_bytes ++ auxv
             ++ repeat (Z_to_bv 8 0) (8 * (block_items argv envp mod 2)))
            _
            (repeat (Z_to_bv 8 0) pad_len
             ++ flatten_strings argv ++ flatten_strings envp
             ++ execfn ++ [Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) 8)).
  - rewrite bsb_decomp, <- !app_assoc. reflexivity.
  - rewrite !length_app, length_hdr_bytes, length_env_bytes, length_auxv, repeat_length.
    unfold rand_off, block_head_size, block_items, argc, envc. lia.
Qed.

(* [comment removed for export] *)
Lemma flatten_strings_split : forall l k, (k < length l)%nat ->
  exists post, flatten_strings l = flatten_strings (firstn k l) ++ (nth k l [] ++ [Z_to_bv 8 0]) ++ post.
Proof using .
  induction l as [|s l IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k].
  - exists (flatten_strings l). reflexivity.
  - destruct (IH k ltac:(cbn in Hk; lia)) as (post & E).
    exists post. cbn [firstn nth]. rewrite !flatten_strings_cons, E, <- !app_assoc. reflexivity.
Qed.

Lemma region_argv_str : forall k, (k < argc)%nat ->
  region (str_off + tab (firstn k argv)) (nth k argv [] ++ [Z_to_bv 8 0]).
Proof using Hsp_hi.
  intros k Hk. destruct (flatten_strings_split argv k Hk) as (post & E).
  destruct region_strs as (pre & post' & E' & L').
  eapply (region_at (pre ++ flatten_strings (firstn k argv)) _ (post ++ flatten_strings envp ++ post')).
  - rewrite E', E, <- !app_assoc. reflexivity.
  - rewrite length_app, L', length_flatten_strings. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mod_add_inner : forall a b c M, M <> 0 -> ((a + b mod M) + c) mod M = (a + b + c) mod M.
Proof using .
  intros a b c M HM. replace (a + b mod M + c) with (b mod M + (a + c)) by lia.
  rewrite Z.add_mod_idemp_l by exact HM. f_equal. lia.
Qed.

Lemma M64_ne : 2 ^ 64 <> 0.
Proof using . cbv. discriminate. Qed.

Lemma mod_add_outer : forall a c M, M <> 0 -> (a mod M + c) mod M = (a + c) mod M.
Proof using . intros. apply Z.add_mod_idemp_l. assumption. Qed.
Lemma string_addrs_nth : forall base l k, (k < length l)%nat ->
  nth k (fst (string_addrs base l)) (Z_to_bv 64 0)
  = Z_to_bv 64 (bv_unsigned base + Z.of_nat (tab (firstn k l))).
Proof using .
  intros base l. revert base. induction l as [|s l IH]; intros base k Hk; [cbn in Hk; lia|].
  cbn [string_addrs]. specialize (IH (base + len_word s + 1)%bv).
  destruct (string_addrs (base + len_word s + 1)%bv l) as [ptrs fin] eqn:E. cbn [fst].
  destruct k as [|k].
  - cbn. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - cbn [nth firstn tab]. rewrite IH by (cbn in Hk; lia). cbn [fst].
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_add_unsigned. unfold len_word. rewrite Z_to_bv_unsigned.
    change (bv_unsigned 1%bv) with 1.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    repeat ((rewrite mod_add_outer by apply M64_ne) || (rewrite mod_add_inner by apply M64_ne) || rewrite <- Z.add_assoc).
    f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma string_addrs_snd : forall base l,
  snd (string_addrs base l) = Z_to_bv 64 (bv_unsigned base + Z.of_nat (tab l)).
Proof using .
  intros base l. revert base. induction l as [|s l IH]; intros base.
  - cbn. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - cbn [string_addrs tab]. specialize (IH (base + len_word s + 1)%bv).
    destruct (string_addrs (base + len_word s + 1)%bv l) as [ptrs fin]. cbn [snd] in *. rewrite IH.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_add_unsigned. unfold len_word. rewrite Z_to_bv_unsigned.
    change (bv_unsigned 1%bv) with 1.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    repeat ((rewrite mod_add_outer by apply M64_ne) || (rewrite mod_add_inner by apply M64_ne) || rewrite <- Z.add_assoc).
    f_equal. lia.
Qed.

End Layout.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* FIFTH CONJUNCT ADDED to match the model, which this tree-local copy was short.
   rocq-linux-process-semantics@75d69e00:theories/LinuxProcessSem/Run.v:3748-3757 states
   [valid_entry_sv48] with FIVE conjuncts, the fifth being [entry_launch_ok_va Sv48 en inp], and
   its own comment at :3744-3747 says so: "conjunct for conjunct, with the launch conjunct last".
   This copy stopped at [entry_stack_fits], leaving a tree-local definition WEAKER than the
   model's under the same name.

   [entry_stack_fits] is [sp + entry_stack_span argv envp <= sp_window_hi] (ibid.:3479-3480) and
   never mentions [top], so it cannot bound the gap between [sp] and [ed_top draw].
   [entry_launch_ok_va]'s second conjunct [valid_launch_sp (ed_top draw) inp sp] (ibid.:3723-3729)
   is exactly that bound, which is what [block_pad_len]'s [Z.to_nat] needs to be non-negative and
   therefore what [bsb_decomp]'s string-base bridge rests on.

   The draw is now bound in the pattern ([rnd], previously [_]) because the fifth conjunct takes
   the whole [ExecEntry]. *)
Definition valid_entry48 (img : Image) (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs _ _, mkEntry sp brk0 mbase rnd =>
      valid_sp sp /\ valid_brk segs brk0 /\ valid_mmap_base mbase
      /\ entry_stack_fits sp (in_argv inp) (in_envp inp)
      /\ entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rnd) inp
  end.

Lemma valid_entry48_of : forall img en inp,
  in_va_size inp = Sv48 -> valid_entry img en inp -> valid_entry48 img en inp.
Proof.
  intros img en inp Hv H. pose proof (proj1 (valid_entry_sv48 img en inp Hv) H) as H'.
  destruct img, en. exact H'.
Qed.

Lemma valid_entry48_to : forall img en inp,
  in_va_size inp = Sv48 -> valid_entry48 img en inp -> valid_entry img en inp.
Proof.
  intros img en inp Hv H. apply (proj2 (valid_entry_sv48 img en inp Hv)).
  destruct img, en. exact H.
Qed.

Lemma valid_entry48_of_input : forall img en inp,
  valid_input inp -> valid_entry img en inp -> valid_entry48 img en inp.
Proof. intros img en inp Hi. apply valid_entry48_of. exact (valid_input_va_size _ Hi). Qed.

(* LPS 75d69e00: the conjunct order of [valid_input_abort] and of
   [valid_input_either] moved, so the positional patterns these two proofs used
   picked up [in_abort_terminal inp = true].  Taken by the model's own named
   accessor where one exists, and otherwise count-free, in the model's own
   idiom (Run.v:5282-5289), so a further inserted conjunct does not break them. *)
Lemma valid_input_abort_va_size' : forall inp, valid_input_abort inp -> in_va_size inp = Sv48.
Proof. exact valid_input_abort_va_size. Qed.

Lemma valid_input_either_va_size' : forall inp, valid_input_either inp -> in_va_size inp = Sv48.
Proof.
  intros inp Hv. red in Hv.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

Lemma valid_entry48_of_input_abort : forall img en inp,
  valid_input_abort inp -> valid_entry img en inp -> valid_entry48 img en inp.
Proof. intros img en inp Hi. apply valid_entry48_of. exact (valid_input_abort_va_size' _ Hi). Qed.

Lemma valid_entry48_of_input_either : forall img en inp,
  valid_input_either inp -> valid_entry img en inp -> valid_entry48 img en inp.
Proof. intros img en inp Hi. apply valid_entry48_of. exact (valid_input_either_va_size' _ Hi). Qed.
