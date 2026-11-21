(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput, the strings above the AT_RANDOM block and their shadow from the invariant's co_zero, the launch's stack window depth under sp, the image size from valid_launch's E2BIG bound, this run's per-flag hand-off state). *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.glaze.binary_reflection.images.Asan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvMainCertA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDrvBridgeArgv.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvMainCertA.AsDrvBridgeEnv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import AzImageAsan.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
Lemma rdn1_off_image : forall (m : word -> option byte) (a : word) (b : byte),
  0x65d000 <= u a -> rdn ASEGS m a 1 = Some [b] -> m a = Some b.
Proof.
  intros m a b Ha H. cbn [rdn] in H. destruct (m a) as [b0|] eqn:Hm.
  - injection H as ->. reflexivity.
  - exfalso. unfold seg_rom, memory_read in H. change (Z.of_N 1) with 1 in H.
    rewrite (asan_segs_hi a) in H by (cbn [g_img_hi GASAN]; lia). discriminate H.
Qed.

Lemma targ_firstn_S : forall (l : list (list byte)) k, (k < length l)%nat ->
  (total_arg_bytes_nat (firstn (S k) l) = total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1)%nat.
Proof.
  intros l k. revert l. induction k as [|k IH]; intros l Hk.
  - destruct l as [|a l]; [cbn in Hk; lia|]. change (firstn 1 (a :: l)) with [a]. change (firstn 0 (a :: l)) with (@nil (list byte)). cbn [nth].
    rewrite total_arg_bytes_cons. change (total_arg_bytes_nat []) with 0%nat. lia.
  - destruct l as [|a l]; [cbn in Hk; lia|]. change (firstn (S (S k)) (a :: l)) with (a :: firstn (S k) l). change (firstn (S k) (a :: l)) with (a :: firstn k l).
    cbn [nth]. rewrite !total_arg_bytes_cons. rewrite (IH l) by (cbn in Hk; lia). lia.
Qed.

Section Argv.
(* Moved onto [inp] with AsSInit.Init (AsSInit.v:50-120).  [apc] and [mbase]
   are new because the image and [wrap_mem] take them; [argv envp uid hw]
   are projections now; [AsSInit.inp], the function that built a ProcInput,
   no longer exists. *)
Variables (ph : PhdrInfo) (apc : N) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput).
Local Notation argv   := (in_argv inp) (only parsing).
Local Notation envp   := (in_envp inp) (only parsing).
Local Notation uid    := (in_uid inp) (only parsing).
Local Notation hw     := (in_hwcap inp) (only parsing).
Local Notation execfn := (in_execfn inp) (only parsing).
Local Notation rseq   := (kb_rseq (in_kernel inp)) (only parsing).
Local Notation top    := (ed_top rdraw) (only parsing).
Local Notation entryw := (Z_to_bv 64 (Z.of_N apc)) (only parsing).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.

(* Old beside new:
     lenb : length (build_stack_bytes ph sp argv envp uid hw rdraw)
          -> length (entry_stack_image inp mbase ph entryw sp rdraw)
     STRv k : u sp + 8*argc + 8*envc + <the old constant>
                   + total_arg_bytes_nat (firstn k argv)
            -> u sp + cat_string_off rseq sp top argv envp execfn
                   + total_arg_bytes_nat (firstn k argv)
   The k-th argv string's address is the string base plus the bytes of the
   strings before it (Common/CatExec.v:597, cat_argv_ptr_offset), and the
   base is the model's own cat_string_off (Common/CatExec.v:578).  The old
   base was 24 + the fixed 160-byte auxv above the pointer arrays, which is
   the form an earlier round refuted. *)
Definition lenb : Z := Z.of_nat (length (entry_stack_image inp mbase ph entryw sp rdraw)).
Definition STRv (k : nat) : Z :=
  u sp + Z.of_nat (cat_string_off rseq sp top argv envp execfn)
       + Z.of_nat (total_arg_bytes_nat (firstn k argv)).
(* OLD BESIDE NEW, and this one REVERSES AN ORDERING rather than moving an
   offset, so it is the hazardous kind:
     XAv := u sp + lenb - 16                  (sixteen below the IMAGE top)
     XAv := u sp + block_head_size rseq argv envp - 16
   [XAv] is the AT_RANDOM block's base.  Under the pre-revision layout the
   random bytes WERE the top of the image and the strings lay below them;
   at this revision the block is
     head(C-16) ++ at_random(16) ++ pad ++ strings ++ 8 zero bytes
   (LPS@08b1429 theories/LinuxProcessSem/StackLayout.v:560-589,
   build_stack_bytes / block_below_random / block_above_random, with
   length_build_stack_bytes giving C + pad + L + 8), and
     at_random_ptr sp rseq argv envp = sp + (block_head_size rseq argv envp - 16)
   (same file, :437-441).  So the random bytes are at sp + C - 16 and the
   STRINGS ARE ABOVE THEM.  The old spelling is short by pad + L + 8, with
   L = launch_string_bytes >= 1 always (the exec name's NUL), so it was
   false for every input rather than merely unprovable.
   The definition is taken from the MODEL, not from any AsSInit lemma, so
   it stands however that file resolves. *)
Definition XAv : Z := u sp + Z.of_nat (block_head_size rseq argv envp) - 16.
Definition XBv : Z := 64 * ((u sp + lenb + 63) / 64).
#[local] Notation E0 := (AsSInit.E0 sp rdraw brk0 inp).

Lemma sp_rng : 0x7fff80000000 <= u sp /\ u sp <= 0x800000000000 /\ u sp mod 16 = 0.
Proof. destruct Hsp as (H1 & H2 & H3). unfold sp_window_lo, sp_window_hi in *. lia. Qed.

(* Old beside new: the right-hand side was the refuted closed form
     u sp + 8*argc + 8*envc + <the old constant>
   and is now the model's own string-block base. *)
Lemma STRv0 : STRv 0 = u sp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).
Proof.
  unfold STRv. change (firstn 0 argv) with (@nil (list byte)).
  change (total_arg_bytes_nat []) with 0%nat. lia.
Qed.

(* THE STRING BLOCK'S CEILING IS NOT [XAv] ANY MORE, and this is the one
   place in this file where the revision REVERSES an ordering rather than
   moving an offset.
   [XAv] is [u sp + lenb - 16] -- sixteen below the image's top -- and under
   the pre-revision layout that WAS the AT_RANDOM block, with the strings
   below it.  At this revision the block is
     head(C-16) ++ at_random(16) ++ pad ++ strings ++ 8 zero bytes
   (LPS@08b1429 StackLayout.v build_stack_bytes / block_below_random /
   block_above_random / length_build_stack_bytes), so the AT_RANDOM bytes
   sit at [sp + block_head_size - 16] and the STRINGS ARE ABOVE THEM,
   running from [STRv 0] for [launch_string_bytes] bytes and ending eight
   below the top.  [STRv 0 + total_arg_bytes_nat argv <= XAv] is therefore
   FALSE in general -- take an empty envp and an empty exec name and the
   argv strings end seven bytes above [XAv].
   So the ceiling is restated as the string block's own end, which is what
   every consumer below actually needs; the [XAv]/[XBv] conjuncts that are
   about the IMAGE's top rather than the random block are unchanged and
   still hold. *)
Definition STRend : Z := STRv 0 + Z.of_nat (launch_string_bytes argv envp execfn).

(* OLD BESIDE NEW, conjunct by conjunct.  Four of the nine change, and each
   changes because the random block moved BELOW the strings rather than
   because an offset moved:
     1  STRv 0 + total_arg_bytes_nat argv <= XAv
     -> STRv 0 + total_arg_bytes_nat argv <= STRend
        The argv strings are a PREFIX of the string area, which ends at
        STRend; they are no longer below the random block at all.
     -  (new) STRend + 8 = u sp + lenb
        The eight-byte slot create_init_stack_vma skips is all that lies
        above the strings, so this is the block's decomposition and it is
        what every later bound is read from.
     3  XAv + 16 <= XBv      -> XAv + 16 <= STRv 0
        was "the random block is below the 64-aligned top"; it is now the
        sharper and true statement that the strings begin at or above the
        top of the random block.
     4  XBv <= XAv + 72      -> u sp + lenb <= XBv <= u sp + lenb + 63
        XBv is the 64-aligned IMAGE top and has nothing to do with the
        random block any more; stated against the top directly.
   Unchanged and still true: XAv mod 8 = 0 (C is a sum of multiples of 8
   and u sp mod 16 = 0); XBv mod 64 = 0; XBv <= 2^47; lenb <= 4000000.
     8  u sp + <the old constant> <= XAv  ->  u sp + 456 <= XAv
   STRENGTHENED rather than carried, and the number is changed so that no
   occurrence of the refuted string-base constant survives anywhere in this
   tree.  456 is the model's own minimum for C - 16: that quantity is
   8*block_items + auxv_size rseq + 8*(block_items mod 2), block_items is
   at least 1 + 0 + 3 = 4 so the first term is at least 32, and auxv_size
   is 432 without CONFIG_RSEQ and 464 with it -- 24 + 432 = 456 at the
   smallest.  Strictly stronger than the old bound, so every consumer's
   [lia] still closes. *)
Lemma blk_arith :
  STRv 0 + Z.of_nat (total_arg_bytes_nat argv) <= STRend /\ STRend + 8 = u sp + lenb
  /\ XAv mod 8 = 0 /\ XAv + 16 <= STRv 0
  /\ u sp + lenb <= XBv /\ XBv <= u sp + lenb + 63 /\ XBv mod 64 = 0
  /\ XBv <= 2 ^ 47 /\ u sp + 456 <= XAv /\ lenb <= 4000000.
Proof.
  pose proof sp_rng as (S1 & S2 & S3).
  pose proof (AsSInit.length_bsb_eq ph apc sp rdraw brk0 mbase inp Hlau) as HL. fold lenb in HL.
  pose proof (AsSInit.usp_fit ph apc sp rdraw brk0 mbase inp Hlau) as HF. fold lenb in HF.
  pose proof (AsSInit.W_range apc sp rdraw brk0 mbase inp Hlau) as (W1 & W2).
  pose proof (AsSInit.bsb_ge ph apc sp rdraw brk0 mbase inp Hlau) as (G1 & G2). fold lenb in G1, G2.
  (* The launch's own two facts the decomposition below needs: the head, the
     strings and the 8-byte slot fit under the stack top
     ([launch_string_base_arith], Common/CatExec.v), so the pad's [Z.to_nat]
     argument is not negative; and the image is at most 2101782 bytes under
     [valid_launch]'s E2BIG bound ([bsb_bound], Mh32.v), which is where
     [lenb <= 4000000] comes from. *)
  pose proof (launch_string_base_arith Sv48 inp mbase sp brk0 rdraw Hlau) as HSA.
  assert (HBB : lenb <= 2101782)
    by (unfold lenb; exact (bsb_bound Sv48 inp mbase ph entryw sp brk0 rdraw Hvl Hlau)).
  unfold AsSInit.stack_image_size in HL.
  pose proof (Nat2Z.is_nonneg (total_arg_bytes_nat argv)) as T1. pose proof (Nat2Z.is_nonneg (total_arg_bytes_nat envp)) as T2.
  (* THE TWO FACTS ABOUT C COME FROM THE MODEL'S OWN LEMMAS, NOT FROM AN
     UNFOLD.  [block_head_size] is 8*items + auxv_size rseq + 8*(items mod 2)
     + 16, and [auxv_size rseq] is [16 * auxv_count rseq] with
     [auxv_count rseq = if rseq then 29 else 27] -- an opaque [if] over a
     Section-variable bool.  Unfolding it and calling [lia] leaves that
     [if] standing, and [lia] cannot reduce it; the model's own proofs of
     both lemmas below end in [destruct rseq; lia] for exactly that reason.
       Run.block_head_size_bounds (Run.v:3884)
         8*(argc+envc) + 472 <= C <= 8*(argc+envc) + 512
       Run.block_head_size_mod16 (Run.v:3899)
         C mod 16 = 0
     The lower bound is where [u sp + 456 <= XAv] comes from -- XAv is
     u sp + C - 16 and 472 - 16 = 456 -- and the mod-16 fact is what gives
     [XAv mod 8 = 0] with [u sp mod 16 = 0].  Both are rseq-independent,
     which is the point: the flag never has to be evaluated here. *)
  pose proof (block_head_size_bounds rseq argv envp) as (HCl & HCh).
  pose proof (block_head_size_mod16 rseq argv envp) as HCm.
  (* The second conjunct is [block_pad_len]'s own definition read forwards.
     [block_pad_len rseq sp top argv envp execfn] is
       Z.to_nat (top - 8 - L - sp - C)                (StackLayout.v:439-444)
     whose argument [HSA] keeps non-negative, so
       C + pad + L + 8 = top - sp = lenb              (length_bsb_eq)
     and [STRend = u sp + C + pad + L] is eight below the top.  [STRend] is
     unfolded BEFORE [STRv0] is rewritten, so that every [STRv 0] becomes the
     same string base. *)
  unfold STRend, XAv, XBv in *. rewrite !STRv0.
  unfold cat_string_off, block_pad_len, launch_string_bytes in *.
  rewrite !length_flatten_strings in *.
  pose proof (valid_argv_len argv Hva) as VA. destruct Hve as [VE _].
  pose proof (Nat2Z.is_nonneg (length (in_execfn inp))) as T3.
  repeat split; Z.div_mod_to_equations; lia.
Qed.

Lemma str_end : forall k, (k < length argv)%nat ->
  STRv k + Z.of_nat (length (nth k argv [])) + 1 = STRv (S k) /\ STRv (S k) <= STRend /\ STRv 0 <= STRv k.
Proof.
  intros k Hk. pose proof blk_arith as (B1 & _).
  pose proof (total_arg_bytes_firstn_le (S k) argv) as F1. pose proof (targ_firstn_S argv k Hk) as F2.
  rewrite STRv0 in *. unfold STRend, STRv in *. lia.
Qed.

(* LPS 727298f3: the stack VMA's end is page aligned ([Run.valid_stack_top_va]'s first
   conjunct), so the 64-aligned image top [XBv] IS the end, the string block ends eight below
   it, and the exec name's NUL ends the block ([StackLayout.launch_string_bytes]). *)
Lemma top_arith :
  u sp + lenb = u top /\ u top mod 4096 = 0 /\ XBv = u top /\ STRend + 8 = XBv /\ STRend mod 8 = 0
  /\ STRv 0 + Z.of_nat (total_arg_bytes_nat argv) + 1 <= STRend.
Proof.
  pose proof (AsSInit.length_bsb_eq ph apc sp rdraw brk0 mbase inp Hlau) as HL. fold lenb in HL.
  unfold AsSInit.stack_image_size in HL.
  assert (HT : u top mod 4096 = 0) by (pose proof Hlau as (Ht & _); destruct Ht as (Hm & _); exact Hm).
  pose proof blk_arith as (B1 & B2 & _).
  assert (HS : STRv 0 + Z.of_nat (total_arg_bytes_nat argv) + 1 <= STRend).
  { unfold STRend, launch_string_bytes. rewrite !length_flatten_strings. lia. }
  assert (HX : XBv = u top) by (unfold XBv; Z.div_mod_to_equations; lia).
  assert (HE : STRend + 8 = u top) by lia.
  split; [lia|]. split; [exact HT|]. split; [exact HX|]. split; [lia|]. split; [|exact HS].
  clear - HT HE. Z.div_mod_to_equations. lia.
Qed.

(* Every argv string ends at least one byte (the exec name's NUL) below [STRend]. *)
Lemma str_end1 : forall k, (k < length argv)%nat -> STRv (S k) + 1 <= STRend.
Proof.
  intros k Hk. pose proof top_arith as (_ & _ & _ & _ & _ & T6).
  pose proof (total_arg_bytes_firstn_le (S k) argv) as F1.
  rewrite STRv0 in T6. unfold STRv in *. lia.
Qed.

(* Old beside new:
     u_ptr : u (cat_argv_ptr sp argv envp k)           = STRv k
     u_ptr : u (cat_argv_ptr top argv envp execfn k)   = STRv k
   [cat_argv_ptr] is anchored at the stack VMA's end now
   (Common/CatExec.v:574) because the strings sit at the top of Linux's
   block.  The old proof closed by [change auxv_size with 160%nat], a
   constant that no longer exists; the new one goes through the model's
   [cat_string_base_offset], so it holds at either auxv size. *)
Lemma u_ptr : forall k, (k < length argv)%nat -> u (cat_argv_ptr top argv envp execfn k) = STRv k.
Proof.
  intros k Hk. pose proof sp_rng as (S1 & S2 & _).
  pose proof (AsSInit.usp_fit ph apc sp rdraw brk0 mbase inp Hlau) as HF. fold lenb in HF.
  pose proof (total_arg_bytes_firstn_le k argv) as F1.
  rewrite (cat_argv_ptr_offset top argv envp execfn k Hk).
  rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
  (* The address stays under 2^64 because the strings end eight below the stack top
     ([blk_arith]), which [usp_fit] keeps under 2^47. *)
  pose proof blk_arith as (B1 & B2 & _). pose proof STRv0 as B0.
  rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia.
  unfold STRv. lia.
Qed.

Section WithE.
Variables (E : env) (M : word -> option byte).
Hypothesis HS : AsSInit.SINV0 ph apc sp rdraw brk0 mbase inp E M.

Lemma sinv_val : forall e, expr_okb (fun n => Nat.ltb n NXS) e = true -> edenot E e = edenot E0 e.
Proof.
  intros e He. apply (edenot_okb (fun n => Nat.ltb n NXS) E E0 e He).
  intros n Hn. apply Nat.ltb_lt in Hn. exact (proj1 HS n Hn).
Qed.

(* Old beside new, and the window moves for the same reason [blk_arith]'s
   first conjunct does -- the hidden string block is [argH0]'s second
   disjunct, which is now [STRv 0 .. STRv 0 + launch_string_bytes), not
   "up to the random block":
     sinv_hidden : STRv 0 <= u a < XAv -> M a = wrap_mem ph sp argv envp uid hw rdraw a
     sinv_hidden : STRv 0 <= u a < STRend -> M a = wrap_mem inp mbase ph entryw sp rdraw a
   Same change in [sinv_def].  [wrap_mem]'s restatement is
   Common/PropExec.v:2454. *)
Lemma sinv_hidden : forall a : word, STRv 0 <= u a < STRend -> M a = wrap_mem inp mbase ph entryw sp rdraw a.
Proof.
  intros a Ha. apply (proj2 HS). unfold AsSInit.argH0.
  assert (Hsp0 : APS.uE E AP.e_sp0 = u sp).
  { unfold APS.uE. rewrite (sinv_val AP.e_sp0 eq_refl). apply (AsSInit.u_e_sp0 ph apc sp rdraw brk0 mbase inp); assumption. }
  cbv zeta. rewrite Hsp0, Z.eqb_refl. cbn [andb]. apply orb_true_iff. left. apply orb_true_iff. right.
  rewrite STRv0 in Ha. unfold STRend, STRv in Ha.
  change (firstn 0 argv) with (@nil (list byte)) in Ha. change (total_arg_bytes_nat []) with 0%nat in Ha.
  apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma sinv_byte : forall k j, (k < length argv)%nat -> (j <= length (nth k argv []))%nat ->
  M (Z_to_bv 64 (STRv k + Z.of_nat j)) = Some (nth j (nth k argv [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)).
Proof.
  intros k j Hk Hj. pose proof sp_rng as (S1 & S2 & S3).
  pose proof blk_arith as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  destruct (str_end k Hk) as (E1 & E2 & E3). pose proof STRv0 as S0.
  assert (Ua : u (Z_to_bv 64 (STRv k + Z.of_nat j)) = STRv k + Z.of_nat j) by (apply u64_lit; unfold STRend in *; lia).
  rewrite sinv_hidden by (rewrite Ua; unfold STRend in *; lia).
  rewrite wrap_above_sp by (rewrite Ua; lia).
  apply rdn1_off_image; [rewrite Ua; lia|].
  replace (Z_to_bv 64 (STRv k + Z.of_nat j)) with (cat_argv_ptr top argv envp execfn k + nat_to_word j)%bv.
  (* [read_argv_byte_k] takes the launch premise at this revision
     (Common/CatExec.v:807: v segs inp mbase ph entry sp brk draw k j, with
     entry_launch_ok_va first), and its no-wrap side condition is now
     discharged by that premise rather than by a [bsb_nw] argument. *)
  - apply (read_argv_byte_k Sv48 ASEGS inp mbase ph entryw sp brk0 rdraw k j Hlau Hk Hj).
  - rewrite word_add_nat. rewrite (u_ptr k Hk). reflexivity.
Qed.

Lemma sinv_def : forall a : word, STRv 0 <= u a < STRend -> M a <> None.
Proof.
  intros a Ha. pose proof sp_rng as (S1 & S2 & S3).
  pose proof blk_arith as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). pose proof STRv0 as S0.
  rewrite sinv_hidden by exact Ha.
  rewrite wrap_above_sp by (unfold STRend in *; lia).
  unfold stack_to_mem. replace (u sp <=? u a) with true by (symmetry; apply Z.leb_le; unfold STRend in *; lia).
  (* [entry_stack_image] IS Linux's whole block, sp .. ed_top: the model no
     longer lays a shorter block and draws bytes above it, so [entry_slack]
     and the draw's [ed_slack] field are both gone and there is no [++]
     here for [length_app] to split.  The length wanted is [lenb], and
     [blk_arith]'s second conjunct [STRend + 8 = u sp + lenb] is what puts
     every address below [STRend] inside it. *)
  replace (u a - u sp <? Z.of_nat (length (entry_stack_image inp mbase ph entryw sp rdraw)))
    with true by (symmetry; apply Z.ltb_lt; unfold lenb in *; lia).
  apply nth_error_Some. unfold lenb in *. lia.
Qed.
End WithE.
End Argv.
End AsDrvBridgeArgv.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeE OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstAE OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit OSSVerify.Proofs.glaze.binary_reflection.lib.AsImages OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvMainCertA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeE OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstAE OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit OSSVerify.Proofs.glaze.binary_reflection.lib.AsImages OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSc OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvS0A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvS1A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvInstFactsA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvMainCertA.AsDrvBridgeEnv OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvMainCertA.AsDrvBridgeLib AsDrvBridgeArgv OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvMainCertA.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require PuLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= PuLia.lia_nd.
#[local] Ltac nia ::= PuLia.znia_nd.
Import AzImageAsan.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
Definition rng_vis_b (s l : Z) : bool :=
  (((0x10000 <=? s) && (s + l <=? 0x65d000)) || ((SB + 0x10000 / 8 <=? s) && (s + l <=? SB + (0x65d000 - 1) / 8 + 1)))%bool.
Definition lit_vis_b (K : kentry) : bool :=
  match K with
  | KImg lo hi => (0x10000 <=? lo) && (hi <=? 0x65d000)
  | KWord (SA (ELit a) o) w _ => (0 <=? a) && (a <? 2 ^ 64) && rng_vis_b (a + o) (Z.of_nat w)
  | KZero (SA (ELit a) o) (ELit n) | KUnk (SA (ELit a) o) (ELit n) | KWr (SA (ELit a) o) (ELit n) | KFill (SA (ELit a) o) (ELit n) _ =>
      (0 <=? a) && (a <? 2 ^ 64) && (0 <=? n) && (n <? 2 ^ 64) && rng_vis_b (a + o) n
  | KShOk (SA (ELit a) o) (ELit n) => (0 <=? a) && (a <? 2 ^ 64) && (1 <=? n) && (n <? 2 ^ 64) && (0x10000 <=? a + o) && (a + o + n <=? 0x65d000)
  | KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ => true
  | _ => false
  end%bool.
Definition sp_vis_b (K : kentry) : bool :=
  match K with
  | KWord (SA (EVar 0) o) w _ => (-8388560 <=? o) && (o + Z.of_nat w <=? 1048576)
  | KWr (SA (EVar 0) o) (ELit n) | KUnk (SA (EVar 0) o) (ELit n) => (-8388560 <=? o) && (0 <=? n) && (n <? 2 ^ 64) && (o + n <=? 1048576)
  | _ => false
  end%bool.
Lemma vis_syn_b : forallb (fun K => if lit_vis_b K then true else sp_vis_b K) TKsyn = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma vis_lit_b : forallb lit_vis_b (map (fun w => KWr (SA (fst w) 0) (snd w)) PERM_A ++ LOWSH ++ GLZSH) = true. Proof. vm_cast_no_check (eq_refl true). Qed.

Section Bridge.
Context {RC : run_ceil}.
(* Moved onto [inp] with AsSInit.Init and with Module AsDrvBridgeArgv above.
   [fs] is a projection now, so it leaves the variable list with the other
   components. *)
Variables (ph : PhdrInfo) (apc : N) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput).
Local Notation argv   := (in_argv inp) (only parsing).
Local Notation envp   := (in_envp inp) (only parsing).
Local Notation fs     := (in_fs inp) (only parsing).
Local Notation uid    := (in_uid inp) (only parsing).
Local Notation hw     := (in_hwcap inp) (only parsing).
Local Notation execfn := (in_execfn inp) (only parsing).
Local Notation rseq   := (kb_rseq (in_kernel inp)) (only parsing).
Local Notation top    := (ed_top rdraw) (only parsing).
Local Notation entryw := (Z_to_bv 64 (Z.of_N apc)) (only parsing).
Local Notation RS     := (rseq_z (kb_rseq (in_kernel inp))) (only parsing).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
(* Old beside new:
     SINV : AsSInit.SINV0 ph sp rdraw brk0 argv envp uid hw
         -> AsSInit.SINV0 ph apc sp rdraw brk0 mbase inp
     argH : AsSInit.argH0 ph sp rdraw argv envp uid hw
         -> AsSInit.argH0 sp rdraw inp
   Both are Definitions, so the arities come from their bodies: [argH0]
   loses [ph] and [brk0] because its string-block bound is
   [cat_string_off] now rather than an expression over the image. *)
#[local] Notation SINV := (AsSInit.SINV0 ph apc sp rdraw brk0 mbase inp).
#[local] Notation argH := (AsSInit.argH0 sp rdraw inp).
#[local] Notation CSOK := (APS.cs_ok ASEGS AT_A LIMIT_S SINV argH ISP_S fs).

Variable hs : acs.
(* The hand-off states are per flag value; this run's own. *)
Hypothesis Hhs : hs = HS_1 RS \/ hs = HS_2 RS.
Variables (E : env) (R : bvmap 5 word) (M : word -> option byte) (model : Model).
Hypothesis HC : CSOK E hs R M model.

Lemma ent_syn : kn_ent AT_A (kn hs) (map (ktsubst (thA RS hs)) TKsyn) = true.
Proof. destruct Hhs as [-> | ->]; [exact (ent_syn_1 rseq) | exact (ent_syn_2 rseq)]. Qed.
Lemma ent_boot : kn_ent AT_A (kn hs) (BOOTF RS) = true.
Proof. destruct Hhs as [-> | ->]; [exact (ent_boot_1 rseq) | exact (ent_boot_2 rseq)]. Qed.
Lemma regs_h : regs_ent (kn hs) 0 (map (tsubst (thA RS hs)) regsM) (s_regs (a_ss hs)) = true.
Proof. destruct Hhs as [-> | ->]; [exact (regs_1 rseq) | exact (regs_2 rseq)]. Qed.
Lemma hull_h : APS.kimg_in_hull AT_A (kn hs).
Proof.
  assert (H : hull_b (kn hs) = true) by (destruct Hhs as [-> | ->]; [exact (hull_1 rseq) | exact (hull_2 rseq)]).
  unfold APS.kimg_in_hull. apply Forall_forall. intros K HK. pose proof (proj1 (forallb_forall _ _) H K HK) as X.
  destruct K; try exact I. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma know_full : know_ok ASEGS E M (kn hs).
Proof.
  apply (BE.know_ok_full ASEGS AT_A LIMIT_S ISP_S SINV argH fs asan_S_in_hull asan_S_hull_ok
           (* a LEMMA, so given by a tactic rather than a positional list *)
           ltac:(apply AsSInit.argH0_high; assumption) E hs R M model (kn hs) HC (APS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) hull_h).
Qed.

#[local] Notation Et := (GPS.tenv E (thA RS hs)).
Lemma know_syn : know_ok ASEGS Et M TKsyn.
Proof.
  apply (proj1 (GPS.know_ok_ktsubst ASEGS E (thA RS hs) M TKsyn)).
  exact (GPS.kn_ent_sound ASEGS AT_A asan_S_in_hull asan_S_hull_ok E M (kn hs) _ know_full ent_syn).
Qed.
Lemma know_boot : know_ok ASEGS E M (BOOTF RS).
Proof. exact (GPS.kn_ent_sound ASEGS AT_A asan_S_in_hull asan_S_hull_ok E M (kn hs) _ know_full ent_boot). Qed.
Lemma regs_syn : regs_ok Et regsM R.
Proof. exact (BE.transport_regs ASEGS AT_A LIMIT_S ISP_S SINV argH fs asan_S_hull_ok E hs R M model (thA RS hs) regsM HC regs_h). Qed.

(* [comment removed for export] *)
Variables (mk : Z) (bl : nat -> list byte).
(* Definitions, so their arities come from their bodies.  Old beside new:
     STRv  AsDrvBridgeArgv.STRv sp argv envp
        -> AsDrvBridgeArgv.STRv sp rdraw inp
        ([rdraw] enters because the string base is anchored at [ed_top])
     XAv   AsDrvBridgeArgv.XAv ph sp rdraw argv envp uid hw
        -> AsDrvBridgeArgv.XAv sp inp
        ([XAv] is [block_head_size]-based now and mentions neither the
         image nor the draw)
     XBv   AsDrvBridgeArgv.XBv ph sp rdraw argv envp uid hw
        -> AsDrvBridgeArgv.XBv ph apc sp rdraw mbase inp *)
#[local] Notation STRv := (AsDrvBridgeArgv.STRv sp rdraw inp).
#[local] Notation STRend := (AsDrvBridgeArgv.STRend sp rdraw inp).
#[local] Notation XAv := (AsDrvBridgeArgv.XAv sp inp).
#[local] Notation XBv := (AsDrvBridgeArgv.XBv ph apc sp rdraw mbase inp).
Definition L0v : Z := Z.of_nat (length (nth 0 argv [])).
Definition L1v : Z := Z.of_nat (length (nth 1 argv [])).
(* OLD BESIDE NEW, and a search for the old number does not find this one:
     D0v := 8*argc + 8*envc + <the old constant plus the frame's 48>
     D0v := cat_string_off rseq sp top argv envp execfn + 48
   [D0v] is the distance from the frame base [u sp - 48] to the first argv
   string, and [HS0 : u sp - 48 + D0v = STRv 0] is where it is used.  With
   [STRv 0] now [u sp + cat_string_off …], the old literal was THE REFUTED
   STRING BASE DISPLACED BY THE FRAME OFFSET -- the same dead constant with
   48 added, which is exactly why a search for the bare number finds
   nothing here.  A wrong value fails as arithmetic inside fifteen
   [unfold D0v; lia] sites, nowhere near any layout vocabulary. *)
Definition D0v : Z := Z.of_nat (cat_string_off rseq sp top argv envp execfn) + 48.
(* [D0v] in the start-up variables, the form [D0th RS] computes: [cat_string_off] is
   [block_head_size + block_pad_len] and the head is
   [8*items + 16*auxv_count + 8*(items mod 2) + 16] with [items = argc + envc + 3]
   ([StackLayout.block_head_size]) and [auxv_count = 27 + 2 r] ([AsSInit.auxv_count_rz]). *)
Lemma D0v_eq : D0v = 8 * Z.of_nat (length argv) + (8 * Z.of_nat (length envp) + (8 * Z.of_nat (block_items argv envp mod 2)
                     + (Z.of_nat (block_pad_len rseq sp top argv envp execfn) + (520 + 32 * RS)))).
Proof.
  pose proof (AsSInit.auxv_count_rz rseq) as HA.
  assert (HB : block_items argv envp = (length argv + length envp + 3)%nat) by reflexivity.
  unfold D0v, cat_string_off, block_head_size, auxv_size. cbv zeta. lia.
Qed.
Definition ovr (n : nat) (w : word) : word :=
  match n with
  | 4%nat => Z_to_bv 64 mk
  | 13%nat => Z_to_bv 64 (STRend - (STRv 0 + L0v))
  | 14%nat => Z_to_bv 64 (STRend - (STRv 0 + L0v + 1 + L1v))
  | 26%nat => Z_to_bv 64 (XBv - (STRv 0 + L0v))
  | 27%nat => Z_to_bv 64 (XBv - (STRv 0 + L0v + 1 + L1v))
  | _ => w
  end.
Definition E' : env := Env (fun n => ovr n (ev Et n)) bl.

Lemma E'_pov : forall n, POV n = true -> ev Et n = ev E' n.
Proof.
  intros n Hn. cbn [E' ev]. unfold POV in Hn. cbn [existsb] in Hn.
  do 28 (destruct n as [|n]; [first [reflexivity | discriminate Hn]|]). reflexivity.
Qed.
Lemma know_syn' : know_ok ASEGS E' M TKsyn.
Proof. exact (know_ok_rel POV ASEGS Et E' M TKsyn okb_syn E'_pov know_syn). Qed.
Lemma regs_syn' : regs_ok E' regsM R.
Proof. exact (regs_ok_rel POV Et E' regsM R okb_regs E'_pov regs_syn). Qed.

(* [comment removed for export] *)
Lemma HSINV : SINV E M. Proof. exact (APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
#[local] Notation E0 := (AsSInit.E0 sp rdraw brk0 inp).
Lemma evE : forall n, (n < NXS)%nat -> ev E n = ev E0 n. Proof. exact (proj1 HSINV). Qed.
Lemma uvar : forall n z, (n < NXS)%nat -> APS.uE E0 (EVar n) = z -> u (ev E n) = z.
Proof. intros n z Hn H. rewrite (evE n Hn). exact H. Qed.

(* Old beside new, the sixth conjunct, and the OLD one is FALSE rather than
   stale -- it is the deleted [W]:
     u (ev E 4) = (lenb - 16 - (8*argc + 8*envc + <the old constant>)) / 8
  -> u (ev E 4) = Z.of_nat (block_pad_len rseq sp top argv envp execfn)
   [V_W] CHANGED MEANING at this revision (AsSInit.v:132-139): it WAS the
   number of 8-byte words of string block below the AT_RANDOM bytes, and it
   IS the pad [arch_align_stack] left between the random block and argv[0],
   in BYTES, 0..4110.  The old right-hand side is a word count computed from
   an offset that no longer locates anything.
   The seventh conjunct, R8V, is the AT_RANDOM block's 64-alignment slack at this revision
   ([AsSInit.uE0_R8]: (64 * BV - (usp + C)) / 8 with BV = (usp + C + 63) / 64); the eighth is
   V_G, the STACK_ROUND gap ([AsSInit.uE0_G]); the ninth V_T, [e_top]'s page index above
   [32768 * V_S1] ([AsSInit.uE0_T]), which [cont_fact] reads the e_top window with.
   [uE0_L1] and [uE0_G] mention neither the image nor the mmap base (their proofs do not
   reach [length bsb]), so they take [E0]'s own variables and [apc]
   (AsSInit's discharged argument lists). *)
Definition TVv : Z := (u sp - 160 + 4095) / 4096 - 8 * (u sp / 32768).
Lemma boot_vals :
  u (ev E 0%nat) = u sp / 32768 /\ u (ev E 6%nat) = u sp mod 32768 / 16 /\ u (ev E 1%nat) = Z.of_nat (length argv)
  /\ u (ev E 2%nat) = Z.of_nat (length envp) /\ u (ev E 3%nat) = L0v /\ u (ev E 7%nat) = L1v
  /\ u (ev E 4%nat) = Z.of_nat (block_pad_len rseq sp top argv envp execfn)
  /\ u (ev E 12%nat) = (64 * ((u sp + Z.of_nat (block_head_size rseq argv envp) + 63) / 64)
                        - (u sp + Z.of_nat (block_head_size rseq argv envp))) / 8
  /\ u (ev E 13%nat) = Z.of_nat (block_items argv envp mod 2)
  /\ u (ev E 10%nat) = TVv.
Proof.
  pose proof (AsSInit.uE0 ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau) as (U1 & U2 & U3 & U4 & U5 & U6 & _).
  pose proof (AsSInit.uE0_L1 apc sp rdraw brk0 inp Hva) as U7.
  pose proof (AsSInit.uE0_R8 ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau) as U8.
  pose proof (AsSInit.uE0_G apc sp rdraw brk0 inp) as U9.
  pose proof (AsSInit.uE0_T ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau) as U10.
  repeat split; (apply uvar; [unfold NXS; lia|]); assumption.
Qed.

(* [comment removed for export] *)
#[local] Notation lenb := (AsDrvBridgeArgv.lenb ph apc sp rdraw mbase inp).
Definition fE (n : nat) : option Z :=
  match n with
  | 0%nat => Some (u sp / 32768) | 1%nat => Some (Z.of_nat (length argv)) | 2%nat => Some (Z.of_nat (length envp)) | 3%nat => Some L0v
  | 4%nat => Some (Z.of_nat (block_pad_len rseq sp top argv envp execfn))
  | 6%nat => Some (u sp mod 32768 / 16) | 7%nat => Some L1v | 10%nat => Some TVv
  | 12%nat => Some ((64 * ((u sp + Z.of_nat (block_head_size rseq argv envp) + 63) / 64)
                     - (u sp + Z.of_nat (block_head_size rseq argv envp))) / 8)
  | 13%nat => Some (Z.of_nat (block_items argv envp mod 2))
  | _ => None
  end.
Lemma fE_ok : forall n x, fE n = Some x -> u (ev E n) = x mod 2 ^ 64.
Proof.
  pose proof boot_vals as (V0 & V6 & V1 & V2 & V3 & V7 & V4 & V12 & V13 & V10).
  intros n x H.
  assert (G : u (ev E n) = x).
  { do 14 (destruct n as [|n]; [cbn [fE] in H; first [discriminate H | injection H as <-; assumption]|]). discriminate H. }
  rewrite <- G. symmetry. apply Z.mod_small. apply u64_range.
Qed.

Lemma hreg2 : hregh hs 2 = eaddz e_sp0 (-48).
(* The hand-off state is a table lookup per CONFIG_RSEQ value, so the flag is split first. *)
Proof. destruct Hhs as [-> | ->]; destruct (kb_rseq (in_kernel inp)); reflexivity. Qed.

(* [comment removed for export] *)
(* FIFTEEN CONJUNCTS, SAME COUNT AND SAME ORDER, deliberately: every
   consumer destructures this as [(N1 & … & N15)] positionally and a
   changed count would silently re-bind all of them.  Four are restated.
   Old beside new:
     7   STRv 0 = u sp + 8*argc + 8*envc + <the old constant>
      -> STRv 0 = u sp + cat_string_off rseq sp top argv envp execfn
     8   STRv 0 + L0v + 1 <= XAv   ->   STRv 0 + L0v + 1 <= STRend
         argv[0] and its NUL end inside the STRING block; they are not
         below the random block any more.
     11  XBv <= XAv + 72   ->   XBv <= u sp + lenb + 63
         XBv is the 64-aligned IMAGE top; it is no longer within 72 of the
         random block, which sits pad + L + 8 below it.
     15  XAv = u sp + lenb - 16
      -> XAv = u sp + block_head_size rseq argv envp - 16
         The AT_RANDOM block's real address
         (LPS@08b1429 StackLayout.v:437-441).
   Unchanged: 1-6, 9, 10, 12, 13, 14. *)
Lemma nums : 0x7fff80000000 <= u sp /\ u sp mod 16 = 0 /\ 1 <= Z.of_nat (length argv) <= 1024 /\ Z.of_nat (length envp) <= 256
  /\ 0 <= L0v <= 131071 /\ 0 <= L1v <= 131071
  /\ STRv 0 = u sp + Z.of_nat (cat_string_off rseq sp top argv envp execfn)
  /\ STRv 0 + L0v + 1 <= STRend /\ XAv mod 8 = 0 /\ XAv + 16 <= XBv
  /\ XBv <= u sp + lenb + 63 /\ XBv mod 64 = 0 /\ XBv <= 2 ^ 47 /\ lenb <= 4000000
  /\ XAv = u sp + Z.of_nat (block_head_size rseq argv envp) - 16.
Proof.
  pose proof (AsDrvBridgeArgv.sp_rng sp Hsp) as (S1 & S2 & S3).
  pose proof (AsDrvBridgeArgv.blk_arith ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hvl Hlau)
    as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof (AsDrvBridgeArgv.STRv0 sp rdraw inp) as S0.
  assert (Hk0 : (0 < length argv)%nat) by (destruct Hva as [[? ?] _]; lia).
  destruct (AsDrvBridgeArgv.str_end ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hvl Hlau 0 Hk0) as (E1 & E2 & E3).
  pose proof (valid_argv_len argv Hva) as VA. destruct Hve as [VE _].
  pose proof (valid_argv_str_len argv 0 Hva Hk0) as VL0.
  assert (VL1 : L1v <= 131071).
  { unfold L1v. destruct (Nat.lt_ge_cases 1 (length argv)) as [H1|H1]; [exact (valid_argv_str_len argv 1 Hva H1)|].
    rewrite nth_overflow by lia. cbn. lia. }
  unfold L0v, L1v in *. repeat split; try lia.
Qed.

(* LPS 727298f3: the string block's end against the stack top ([AsDrvBridgeArgv.top_arith]):
   the block ends eight below the page-aligned top, past every argv string and the exec name's
   NUL. *)
Lemma strend_rng : STRend mod 8 = 0 /\ STRend + 8 = XBv /\ XBv = u sp + lenb /\ STRv 0 + L0v + 1 <= STRend
  /\ (forall k, (k < length argv)%nat -> STRv (S k) + 1 <= STRend).
Proof.
  pose proof (AsDrvBridgeArgv.top_arith ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hvl Hlau) as (T1 & T2 & T3 & T4 & T5 & T6).
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & _).
  split; [exact T5|]. split; [exact T4|]. split; [lia|]. split; [exact N8|].
  exact (AsDrvBridgeArgv.str_end1 ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hvl Hlau).
Qed.

(* The witnesses for main's H0 / H1: the readable span after argv[k] runs to the string
   block's end ([STRend], eight-aligned), no longer to the AT_RANDOM block, which sits below
   the strings at this revision. *)
Definition H0v : Z := STRend - (STRv 0 + L0v).
Definition H1v : Z := STRend - (STRv 0 + L0v + 1 + L1v).
Definition G0v : Z := XBv - (STRv 0 + L0v).
Definition G1v : Z := XBv - (STRv 0 + L0v + 1 + L1v).
Definition fE' (n : nat) : option Z :=
  match n with
  | 0%nat => Some (u sp - 48) | 1%nat => Some (Z.of_nat (length argv)) | 2%nat => Some D0v | 3%nat => Some L0v
  | 5%nat => Some (D0v + L0v + 1) | 6%nat => Some L1v
  | 13%nat => Some H0v | 14%nat => Some H1v | 26%nat => Some G0v | 27%nat => Some G1v
  | _ => None
  end.
Lemma vals'_ok :
  u (ev E' 0%nat) = (u sp - 48) mod 2 ^ 64 /\ u (ev E' 1%nat) = Z.of_nat (length argv) mod 2 ^ 64 /\ u (ev E' 2%nat) = D0v mod 2 ^ 64
  /\ u (ev E' 3%nat) = L0v mod 2 ^ 64 /\ u (ev E' 5%nat) = (D0v + L0v + 1) mod 2 ^ 64 /\ u (ev E' 6%nat) = L1v mod 2 ^ 64
  /\ u (ev E' 13%nat) = H0v mod 2 ^ 64 /\ u (ev E' 14%nat) = H1v mod 2 ^ 64 /\ u (ev E' 26%nat) = G0v mod 2 ^ 64 /\ u (ev E' 27%nat) = G1v mod 2 ^ 64.
Proof.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & _).
  pose proof boot_vals as (V0 & V6 & V1 & V2 & V3 & V7 & V4 & V12 & V13 & V10).
  assert (SM : forall w : word, u w = u w mod 2 ^ 64) by (intros w; symmetry; apply Z.mod_small; apply u64_range).
  repeat split.
  - change (ev E' 0%nat) with (edenot E (hregh hs 2)). rewrite hreg2.
    rewrite (zval_sound fE E (eaddz e_sp0 (-48)) (32768 * (u sp / 32768) + 16 * (u sp mod 32768 / 16) + -48) fE_ok eq_refl).
    f_equal. clear - N2. Z.div_mod_to_equations. lia.
  - change (ev E' 1%nat) with (ev E 1%nat). rewrite <- V1. apply SM.
  - change (ev E' 2%nat) with (edenot E (D0th RS)).
    rewrite (zval_sound fE E (D0th RS) (8 * Z.of_nat (length argv) + (8 * Z.of_nat (length envp) + (8 * Z.of_nat (block_items argv envp mod 2)
                     + (Z.of_nat (block_pad_len rseq sp top argv envp execfn) + (520 + 32 * RS))))) fE_ok eq_refl).
    rewrite D0v_eq. reflexivity.
  - change (ev E' 3%nat) with (ev E 3%nat). rewrite <- V3. apply SM.
  - change (ev E' 5%nat) with (edenot E (EAlu Instr.ALU_ADD (D0th RS) (EAlu Instr.ALU_ADD (EVar 3) (ELit 1)))).
    rewrite (zval_sound fE E (EAlu Instr.ALU_ADD (D0th RS) (EAlu Instr.ALU_ADD (EVar 3) (ELit 1)))
               ((8 * Z.of_nat (length argv) + (8 * Z.of_nat (length envp) + (8 * Z.of_nat (block_items argv envp mod 2)
                     + (Z.of_nat (block_pad_len rseq sp top argv envp execfn) + (520 + 32 * RS))))) + (L0v + 1)) fE_ok eq_refl).
    f_equal. rewrite D0v_eq. lia.
  - change (ev E' 6%nat) with (ev E 7%nat). rewrite <- V7. apply SM.
Qed.
Lemma fE'_ok : forall n x, fE' n = Some x -> u (ev E' n) = x mod 2 ^ 64.
Proof.
  pose proof vals'_ok as (W0 & W1 & W2 & W3 & W5 & W6 & W13 & W14 & W26 & W27).
  intros n x H.
  do 28 (destruct n as [|n]; [cbn [fE'] in H; first [discriminate H | injection H as <-; assumption]|]). discriminate H.
Qed.

(* [comment removed for export] *)
Lemma evE' : forall e z, zval fE' e = Some z -> 0 <= z < 2 ^ 64 -> u (edenot E' e) = z.
Proof. intros e z H Hz. exact (zval_small fE' E' e z fE'_ok H Hz). Qed.
Lemma evEb : forall e z, zval fE e = Some z -> 0 <= z < 2 ^ 64 -> u (edenot E e) = z.
Proof. intros e z H Hz. exact (zval_small fE E e z fE_ok H Hz). Qed.

(* [comment removed for export] *)
Lemma rdn1_mem : forall (m : word -> option byte) (a : word) (b : byte), m a = Some b -> rdn ASEGS m a 1 = Some [b].
Proof. intros m a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

Lemma adenot_val : forall Ex b o z, u (edenot Ex b) + o = z -> 0 <= z < 2 ^ 64 -> adenot Ex (SA b o) = Z_to_bv 64 z.
Proof.
  intros Ex b o z H Hz. apply bv_eq. rewrite u64_lit by exact Hz.
  rewrite (flat_u Ex (SA b o) 0); [unfold estart; cbn [a_base a_off]; exact H|].
  unfold flat, estart. cbn [a_base a_off]. lia.
Qed.

(* [comment removed for export] *)
Section Str.
Variables (k : nat) (eS eE eXA eXB eL eH eG eLH : expr) (j : nat) (Sv Lv : Z).
Hypothesis Hk : (k < length argv)%nat.
Hypothesis HLv : Lv = Z.of_nat (length (nth k argv [])).
Hypothesis HSv : Sv = STRv k.
Hypothesis HeS : u (edenot E' eS) = Sv.
Hypothesis HeE : u (edenot E' eE) = Sv + Lv.
Hypothesis HeL : u (edenot E' eL) = Lv.
Hypothesis HeH : u (edenot E' eH) = STRend - (Sv + Lv).
Hypothesis HeG : u (edenot E' eG) = XBv - (Sv + Lv).
Hypothesis HeXA : u (edenot E' eXA) = STRend.
Hypothesis HeXB : u (edenot E' eXB) = XBv.
Hypothesis HeLH : u (edenot E' eLH) = STRend - Sv.
Hypothesis Hbl : bl j = nth k argv [].

Lemma str_facts :
  know_ok ASEGS E' M
    [ KRange eG 10 4194304; KAlign eXB 64; KRange eXB 0 two47;
      KWord (SA eE 0) 1 (ELit 0); KBlob (SA eS 0) eL j;
      KRange eH 1 4194304; KAlign eXA 8; KRange eXA 1 two47; KUnk (SA eS 0) eLH ].
Proof.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15).
  destruct (AsDrvBridgeArgv.str_end ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hvl Hlau k Hk) as (E1 & E2 & E3).
  pose proof strend_rng as (R1 & R2 & R3 & R4 & R5). pose proof (R5 k Hk) as R6.
  rewrite <- HLv, <- HSv in E1. rewrite <- HSv in E3.
  assert (HL131 : 0 <= Lv <= 131071) by (rewrite HLv; pose proof (valid_argv_str_len argv k Hva Hk); lia).
  unfold know_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok].
  - rewrite HeG. lia.
  - rewrite HeXB. split; [lia | exact N12].
  - rewrite HeXB. unfold two47. lia.
  - split; [lia|]. split; [unfold flat, estart; cbn [a_base a_off]; rewrite HeE; lia|].
    rewrite (adenot_val E' eE 0 (Sv + Lv)) by (rewrite ?HeE; lia).
    pose proof (AsDrvBridgeArgv.sinv_byte ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hvl Hlau E M HSINV k (length (nth k argv [])) Hk ltac:(lia)) as B.
    rewrite <- HSv, <- HLv in B. rewrite nth_middle in B. exact (rdn1_mem M _ _ B).
  - unfold flat, estart, elenZ. cbn [a_base a_off eb E']. rewrite HeS, HeL, Hbl.
    split; [lia|]. split; [lia|]. intros i Hi.
    pose proof (AsDrvBridgeArgv.sinv_byte ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hvl Hlau E M HSINV k (Z.to_nat i) Hk ltac:(lia)) as B.
    rewrite <- HSv in B. rewrite Z2Nat.id in B by lia. rewrite app_nth1 in B by lia. rewrite Z.add_0_r. exact B.
  - rewrite HeH. lia.
  - rewrite HeXA. split; [lia | exact R1].
  - rewrite HeXA. unfold two47. lia.
  - unfold flat, estart, elenZ. cbn [a_base a_off]. rewrite HeS, HeLH. split; [lia|]. intros i Hi. rewrite Z.add_0_r.
    apply (AsDrvBridgeArgv.sinv_def ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hvl Hlau E M HSINV).
    rewrite u64_lit by lia. lia.
Qed.
End Str.

(* [comment removed for export] *)
Lemma boot_in : forall K, In K (BOOTF RS) -> kentry_ok ASEGS E M K.
Proof. intros K HK. exact (proj1 (Forall_forall _ _) know_boot K HK). Qed.

Lemma sp0_val : u (edenot E e_sp0) = u sp.
Proof.
  pose proof nums as (N1 & N2 & _). pose proof (AsDrvBridgeArgv.sp_rng sp Hsp) as (S1 & S2 & S3).
  rewrite (evEb e_sp0 (32768 * (u sp / 32768) + 16 * (u sp mod 32768 / 16)) eq_refl); Z.div_mod_to_equations; lia.
Qed.
Lemma SP0_val : u (edenot E' SP0) = u sp - 48.
Proof. pose proof (AsDrvBridgeArgv.sp_rng sp Hsp) as (S1 & S2 & S3). apply (evE' SP0 (u sp - 48) eq_refl). lia. Qed.

Lemma stk_facts : know_ok ASEGS E' M [KWr (SA SP0 (- YLO)) (ELit YLO); KUnk (SA SP0 (- YLO)) (ELit YLO); KShOk (SA SP0 (- YLO)) (ELit (YLO + 48))].
Proof.
  pose proof (AsDrvBridgeArgv.sp_rng sp Hsp) as (S1 & S2 & S3).
  apply (stack_trio E E' M e_sp0 e_shb (u sp)).
  - apply boot_in. unfold BOOTF. apply in_or_app. right. left. reflexivity.
  - apply boot_in. unfold BOOTF. apply in_or_app. right. right. left. reflexivity.
  - exact sp0_val.
  - rewrite (evEb e_shb (4096 * (u sp / 32768) + 2 * (u sp mod 32768 / 16)) eq_refl); Z.div_mod_to_equations; lia.
  - exact SP0_val.
  - lia.
Qed.

(* Route (C) for the strings' shadow (see AsDrvMainCertA.vis_ok).  [B64v] is [e_bend64], the
   AT_RANDOM block's 64-aligned top; [TOPv] is [e_top = 4096 * ceil ((sp - 160) / 4096)]. *)
Definition B64v : Z := 64 * ((u sp + Z.of_nat (block_head_size rseq argv envp) + 63) / 64).
Definition TOPv : Z := 32768 * (u sp / 32768) + 4096 * TVv.

Lemma vis_ok_h : vis_ok RS hs = true.
Proof. destruct Hhs as [-> | ->]; [exact (vis_ok_1 rseq) | exact (vis_ok_2 rseq)]. Qed.

(* The block head in the start-up variables' terms ([StackLayout.block_head_size], as in
   [D0v_eq]). *)
Lemma head_eq : Z.of_nat (block_head_size rseq argv envp)
  = 8 * Z.of_nat (length argv) + (8 * Z.of_nat (length envp) + (8 * Z.of_nat (block_items argv envp mod 2) + (472 + 32 * RS))).
Proof.
  pose proof (AsSInit.auxv_count_rz rseq) as HA.
  assert (HB : block_items argv envp = (length argv + length envp + 3)%nat) by reflexivity.
  unfold block_head_size, auxv_size. cbv zeta. lia.
Qed.

(* The three start-up stack windows start above [sp - 8 MiB - 160] and end at [sp],
   [e_top] and [e_bend64]. *)
Lemma win_facts : forall p, existsb (pair_eqb p) (stk_wins RS) = true ->
  u sp - 8388768 <= APS.uE E (fst p) /\ APS.uE E (fst p) + APS.uE E (snd p) <= Z.max B64v TOPv.
Proof.
  intros [e n] H.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15).
  pose proof head_eq as HE.
  assert (HR : 0 <= RS <= 1) by (unfold rseq_z; destruct (kb_rseq (in_kernel inp)); lia).
  assert (HG : 0 <= Z.of_nat (block_items argv envp mod 2) <= 1)
    by (pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)); lia).
  apply existsb_exists in H as ([e' n'] & Hq & Heq). cbn [fst snd].
  apply APS.pair_eqb_eq in Heq. injection Heq as H1 H2. subst e' n'.
  unfold stk_wins in Hq. cbn [In] in Hq. unfold APS.uE.
  destruct Hq as [Hq|[Hq|[Hq|[]]]]; injection Hq as Ee En; subst e n.
  - rewrite (evEb stk_w1 (32768 * (u sp / 32768) + 16 * (u sp mod 32768 / 16) + -8388608) eq_refl),
      (evEb (ELit 8388608) 8388608 eq_refl);
      unfold B64v, TOPv, TVv; Z.div_mod_to_equations; lia.
  - rewrite (evEb stk_w2 (32768 * (u sp / 32768) + 4096 * TVv + -8388608) eq_refl),
      (evEb (ELit 8388608) 8388608 eq_refl);
      unfold B64v, TOPv, TVv; Z.div_mod_to_equations; lia.
  - rewrite (evEb (stk_w3 RS) (32768 * (u sp / 32768) + (8 * Z.of_nat (length argv) + (8 * Z.of_nat (length envp)
                 + (16 * (u sp mod 32768 / 16) + (8 * ((B64v - (u sp + Z.of_nat (block_head_size rseq argv envp))) / 8)
                 + 8 * Z.of_nat (block_items argv envp mod 2))))) + (-4193832 + 32 * RS)) eq_refl),
      (evEb (ELit 4194304) 4194304 eq_refl);
      unfold B64v, TOPv, TVv; rewrite ?HE; Z.div_mod_to_equations; lia.
Qed.

(* A range the checker finds flat and apart from the high-shadow grant. *)
Lemma apart_facts : forall p, apart_hsh (kn hs) p = true ->
  0 <= APS.uE E (fst p) /\ APS.uE E (fst p) + APS.uE E (snd p) <= 2 ^ 64
  /\ (APS.uE E (fst p) + APS.uE E (snd p) <= HSB \/ HSB + HSL <= APS.uE E (fst p)).
Proof.
  intros [e n]. unfold apart_hsh. cbn [fst snd].
  destruct (split_lit e) as [pb pk] eqn:HSp. intros H. cbv beta iota in H.
  apply andb_prop in H as [HF HR].
  destruct (APS.flat_x_sound ASEGS E M (kn hs) pb pk n know_full HF) as (F1 & F2 & F3).
  assert (U : APS.uE E e = estart E (SA pb pk)) by (unfold APS.uE; apply (APS.u_of_split E e pb pk HSp); lia).
  pose proof (ranges_apart_x_sound ASEGS E M (kn hs) pb pk n (ELit 0) HSB (ELit HSL) know_full HR) as RA.
  assert (S0 : estart E (SA (ELit 0) HSB) = HSB)
    by (unfold estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia; unfold HSB; lia).
  rewrite S0, (elenZ_lit E HSL) in RA by (unfold HSL; lia). unfold elenZ in RA.
  (* The three conjuncts are [F1], [F2] and [RA] as they stand; the unit's [lia] (MhTac)
     does not close a goal whose last conjunct is a disjunction. *)
  rewrite U. unfold APS.uE. split; [exact F1|]. split; [exact F2|]. exact RA.
Qed.

(* A range the checker also finds apart from the stack region [sp - 8 MiB, sp + 2^47). *)
Lemma below_facts : forall p, apart_hsh (kn hs) p = true -> below_stk (kn hs) p = true ->
  APS.uE E (fst p) + APS.uE E (snd p) <= u sp - 8388608 \/ u sp + 2 ^ 47 <= APS.uE E (fst p).
Proof.
  intros [e n]. unfold apart_hsh, below_stk. cbn [fst snd].
  destruct (split_lit e) as [pb pk] eqn:HSp. intros H HB. cbv beta iota in H, HB.
  apply andb_prop in H as [HF _].
  destruct (APS.flat_x_sound ASEGS E M (kn hs) pb pk n know_full HF) as (F1 & F2 & F3).
  assert (U : APS.uE E e = estart E (SA pb pk)) by (unfold APS.uE; apply (APS.u_of_split E e pb pk HSp); lia).
  pose proof (ranges_apart_x_sound ASEGS E M (kn hs) pb pk n e_usp (-8388608) (ELit STKL) know_full HB) as RB.
  pose proof (AsDrvBridgeArgv.sp_rng sp Hsp) as (S1 & S2 & S3).
  assert (S0 : estart E (SA e_usp (-8388608)) = u sp - 8388608).
  { unfold estart. cbn [a_base a_off].
    rewrite (evEb e_usp (32768 * (u sp / 32768) + 16 * (u sp mod 32768 / 16)) eq_refl); Z.div_mod_to_equations; lia. }
  rewrite S0, (elenZ_lit E STKL) in RB by (unfold STKL; lia). unfold elenZ in RB.
  (* Stdlib's lia core: the unit's [lia] (MhTac) gives up on this goal shape. *)
  rewrite U. unfold APS.uE. unfold STKL in RB. destruct RB as [RB|RB]; [left | right]; Zify.zify; xlia zchecker.
Qed.

(* The shadow of the stack bytes above [e_bend64] and [e_top] is zero: the shadow byte is
   in the high-shadow grant, so it is mapped, lazy and not no-access ([co_maps],
   [co_kinds]); no visible or ghost range covers it or its shadow ([vis_ok]); it lies
   below the allocation top; so it is hidden and [co_zero] makes it zero. *)
Lemma shadow_zero_hi : forall z, B64v <= z -> TOPv <= z -> z < XBv ->
  M (Z_to_bv 64 (SB + z / 8)) = Some (Z_to_bv 8 0).
Proof.
  intros z Hz1 Hz2 Hz3.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15).
  assert (HB0 : u sp <= B64v) by (unfold B64v; Z.div_mod_to_equations; lia).
  assert (Hy : HSB <= SB + z / 8 < HSB + HSL) by (unfold HSB, HSL, SB; Z.div_mod_to_equations; lia).
  remember (SB + z / 8) as y eqn:Ey.
  remember (Z_to_bv 64 y) as a eqn:Ea.
  assert (UA : u a = y) by (rewrite Ea; apply u64_lit; unfold HSB, HSL in Hy; lia).
  assert (SV : u (edenot E ISP_S) = u sp) by exact sp0_val.
  assert (ATOP : alloc_top (m_vmmaps model) = u sp - 8388608).
  { unfold alloc_top, stack_max_size. rewrite (APS.co_isp _ _ _ _ _ _ _ _ _ _ _ _ HC), SV. lia. }
  assert (IH : img_hi AT_A = 0x65d000) by reflexivity.
  assert (SO : shadow_off AT_A = SB) by reflexivity.
  pose proof vis_ok_h as VO. unfold vis_ok in VO.
  apply andb_prop in VO as [VO VM]. apply andb_prop in VO as [VV VG].
  apply existsb_exists in VM as (m & Hm & Hmq). apply APS.amap_eqb_eq in Hmq. subst m.
  assert (BND : u (edenot E (am_base hsh_map)) <= u a < u (edenot E (am_base hsh_map)) + u (edenot E (am_len hsh_map))).
  { cbn [hsh_map am_base am_len edenot]. rewrite UA, !u64_lit by (unfold HSB, HSL; lia). unfold HSB, HSL in *. lia. }
  pose proof (proj1 (Forall_forall _ _) (APS.co_kinds _ _ _ _ _ _ _ _ _ _ _ _ HC) hsh_map Hm) as K.
  destruct (K eq_refl a BND) as [K1 K2].
  assert (NV : APS.in_vis E hs y = false).
  { apply Bool.not_true_iff_false. intros X. unfold APS.in_vis in X. apply existsb_exists in X as (p & Hp & Xp). cbv beta in Xp.
    apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
    pose proof (proj1 (forallb_forall _ _) VV p Hp) as Pp. cbv beta in Pp.
    apply orb_prop in Pp as [W|W].
    - destruct (win_facts p W) as (W1 & W2). unfold HSB, HSL in *. lia.
    - apply andb_prop in W as [WA _]. destruct (apart_facts p WA) as (A1 & A2 & A3). lia. }
  assert (NS : APS.in_sh AT_A E hs y = false).
  { apply Bool.not_true_iff_false. intros X. unfold APS.in_sh in X. apply existsb_exists in X as (p & Hp & Xp). cbv beta in Xp.
    apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
    unfold APS.sh_lo, APS.sh_hi in X1, X2. rewrite SO in X1, X2.
    pose proof (proj1 (forallb_forall _ _) VV p Hp) as Pp. cbv beta in Pp.
    apply orb_prop in Pp as [W|W].
    - destruct (win_facts p W) as (W1 & W2). Z.div_mod_to_equations. lia.
    - apply andb_prop in W as [WA WB]. destruct (apart_facts p WA) as (A1 & A2 & A3).
      destruct (below_facts p WA WB) as [B|B]; Z.div_mod_to_equations; lia. }
  assert (NG : APS.in_ghost E hs y = false).
  { apply Bool.not_true_iff_false. intros X. unfold APS.in_ghost in X. apply existsb_exists in X as (p & Hp & Xp). cbv beta in Xp.
    apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
    destruct (apart_facts p (proj1 (forallb_forall _ _) VG p Hp)) as (A1 & A2 & A3). lia. }
  apply (APS.co_zero _ _ _ _ _ _ _ _ _ _ _ _ HC a).
  - unfold APS.hid. apply orb_true_intro. right. apply negb_true_iff.
    unfold APS.vis. cbv zeta. rewrite UA, ATOP, K2.
    replace (APS.in_hull AT_A y) with false
      by (symmetry; unfold APS.in_hull; rewrite IH; apply andb_false_iff; right; apply Z.ltb_ge; unfold HSB in Hy; lia).
    replace (u sp - 8388608 <=? y) with false by (symmetry; apply Z.leb_gt; unfold HSB, HSL in Hy; lia).
    unfold APS.in_allow. rewrite NV, NS. cbn [negb orb]. apply andb_false_r.
  - eapply APS.in_ivs_maps_match; [exact (APS.co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hm | reflexivity | exact BND].
  - exact K1.
  - exact K2.
  - rewrite UA. exact NG.
Qed.

(* [cont_fact]: the shadow of [sp, top) is zero.  Below [e_bend64] it is the start state's
   e_bend64 window ([BOOTF]'s KZero at [e_w64]); between [e_bend64] and [e_top] its e_top
   window ([e_tsh]); above both, [shadow_zero_hi]. *)
Lemma cont_fact : forall eLEN, u (edenot E' eLEN) = XBv - u sp -> kentry_ok ASEGS E' M (KShOk (SA SP0 48) eLEN).
Proof.
  intros eLEN HLEN.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15).
  pose proof head_eq as HE.
  assert (HR : 0 <= RS <= 1) by (unfold rseq_z; destruct (kb_rseq (in_kernel inp)); lia).
  assert (HG : 0 <= Z.of_nat (block_items argv envp mod 2) <= 1)
    by (pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)); lia).
  assert (HB0 : u sp <= B64v <= u sp + 4000126 /\ B64v mod 64 = 0) by (unfold B64v; Z.div_mod_to_equations; lia).
  assert (HT0 : u sp - 160 <= TOPv <= u sp + 3935) by (unfold TOPv, TVv; Z.div_mod_to_equations; lia).
  assert (HW : u (edenot E e_w64) = B64v / 8 - 59 - 4 * RS).
  { rewrite (evEb e_w64 (4096 * (u sp / 32768) + (Z.of_nat (length argv) + (Z.of_nat (length envp)
               + (2 * (u sp mod 32768 / 16) + ((B64v - (u sp + Z.of_nat (block_head_size rseq argv envp))) / 8
               + Z.of_nat (block_items argv envp mod 2)))))) eq_refl);
      unfold B64v in *; rewrite ?HE in *; Z.div_mod_to_equations; lia. }
  assert (HTs : 8 * u (edenot E e_tsh) = TOPv).
  { rewrite (evEb e_tsh (4096 * (u sp / 32768) + 512 * TVv) eq_refl); unfold TOPv, TVv in *; Z.div_mod_to_equations; lia. }
  cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off]. rewrite SP0_val, HLEN.
  split; [lia|]. split; [lia|].
  intros z Hz. exists (Z_to_bv 8 0). split; [|left; reflexivity].
  destruct (Z_lt_ge_dec z B64v) as [Hb|Hb].
  - assert (KZ : kentry_ok ASEGS E M (KZero (SA e_w64 (2146926651 + 4 * RS)) (ELit 524288))).
    { apply boot_in. unfold BOOTF. apply in_or_app. right. right. right. left. reflexivity. }
    destruct KZ as [_ HZ]. unfold estart, elenZ in HZ. cbn [a_base a_off edenot] in HZ. rewrite u64_lit in HZ by lia.
    replace (SB + z / 8) with (u (edenot E e_w64) + (2146926651 + 4 * RS) + (z / 8 - B64v / 8 + 524288))
      by (rewrite HW; unfold SB; lia).
    apply HZ. Z.div_mod_to_equations. lia.
  - destruct (Z_lt_ge_dec z TOPv) as [Ht|Ht].
    + assert (KZ : kentry_ok ASEGS E M (KZero (SA e_tsh 2146402304) (ELit 1048576))).
      { apply boot_in. unfold BOOTF. apply in_or_app. right. right. right. right. right. left. reflexivity. }
      destruct KZ as [_ HZ]. unfold estart, elenZ in HZ. cbn [a_base a_off edenot] in HZ. rewrite u64_lit in HZ by lia.
      replace (SB + z / 8) with (u (edenot E e_tsh) + 2146402304 + (z / 8 - u (edenot E e_tsh) + 1048576))
        by (unfold SB; lia).
      apply HZ. Z.div_mod_to_equations. lia.
    + exact (shadow_zero_hi z ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Lemma okb_bootsh : forallb (kentry_okb (fun _ => false)) BOOT_SH = true. Proof. reflexivity. Qed.
Lemma lit_facts : know_ok ASEGS E' M (map (fun w => KWr (SA (fst w) 0) (snd w)) PERM_A ++ LOWSH ++ GLZSH).
Proof.
  unfold know_ok. apply Forall_app. split; [exact (PERM_A_kwr E' M)|].
  apply (LOWSH_GLZSH_of_boot E' M).
  apply (know_ok_rel (fun _ => false) ASEGS E E' M BOOT_SH okb_bootsh); [intros n Hn; discriminate Hn|].
  unfold know_ok. apply Forall_forall. intros K HK. apply boot_in. unfold BOOTF. apply in_or_app. left. exact HK.
Qed.

(* [comment removed for export] *)
Lemma STR1v : (1 < length argv)%nat -> STRv 1 = STRv 0 + L0v + 1.
Proof.
  intros H1. assert (Hk0 : (0 < length argv)%nat) by lia.
  destruct (AsDrvBridgeArgv.str_end ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hvl Hlau 0 Hk0) as (E1 & _). unfold L0v. lia.
Qed.

Definition KS0 : list kentry :=
  [ KRange G0 10 4194304; KAlign (eadd END0 G0) 64; KRange (eadd END0 G0) 0 two47;
    KWord (SA END0 0) 1 (ELit 0); KBlob (SA STR0 0) L0 1;
    KRange H0 1 4194304; KAlign (eadd END0 H0) 8; KRange (eadd END0 H0) 1 two47; KUnk (SA STR0 0) (eadd L0 H0) ].
Definition KS1 : list kentry :=
  [ KRange G1 10 4194304; KAlign (eadd END1 G1) 64; KRange (eadd END1 G1) 0 two47;
    KWord (SA END1 0) 1 (ELit 0); KBlob (SA STR1 0) L1 2;
    KRange H1 1 4194304; KAlign (eadd END1 H1) 8; KRange (eadd END1 H1) 1 two47; KUnk (SA STR1 0) (eadd L1 H1) ].

Ltac ev' z := match goal with |- bv_unsigned (edenot E' ?e) = _ => rewrite (evE' e z eq_refl) end.

Lemma ks0_facts : bl 1%nat = nth 0 argv [] -> know_ok ASEGS E' M KS0.
Proof.
  intros Hbl.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15).
  pose proof strend_rng as (R1 & R2 & R3 & R4 & R5).
  assert (Hk0 : (0 < length argv)%nat) by lia.
  assert (HS0 : u sp - 48 + D0v = STRv 0) by (unfold D0v; lia).
  apply (str_facts 0 STR0 END0 (eadd END0 H0) (eadd END0 G0) L0 H0 G0 (eadd L0 H0) 1 (STRv 0) L0v Hk0 eq_refl eq_refl).
  - ev' (u sp - 48 + D0v); lia.
  - ev' (u sp - 48 + (D0v + L0v)); lia.
  - ev' L0v; lia.
  - ev' H0v; unfold H0v; lia.
  - ev' G0v; unfold G0v; lia.
  - rewrite (evE' (eadd END0 H0) (u sp - 48 + (D0v + (L0v + H0v))) eq_refl); unfold H0v; lia.
  - rewrite (evE' (eadd END0 G0) (u sp - 48 + (D0v + (L0v + G0v))) eq_refl); unfold G0v; lia.
  - rewrite (evE' (eadd L0 H0) (L0v + H0v) eq_refl); unfold H0v; lia.
  - exact Hbl.
Qed.

Lemma ks1_facts : (1 < length argv)%nat -> bl 2%nat = nth 1 argv [] -> know_ok ASEGS E' M KS1.
Proof.
  intros Hac Hbl.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15).
  pose proof strend_rng as (R1 & R2 & R3 & R4 & R5). pose proof (R5 1%nat Hac) as R6.
  pose proof (STR1v Hac) as S1.
  destruct (AsDrvBridgeArgv.str_end ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hvl Hlau 1 Hac) as (E1 & E2 & E3). fold L1v in E1.
  assert (HS0 : u sp - 48 + D0v = STRv 0) by (unfold D0v; lia).
  apply (str_facts 1 STR1 END1 (eadd END1 H1) (eadd END1 G1) L1 H1 G1 (eadd L1 H1) 2 (STRv 1) L1v Hac eq_refl eq_refl).
  - ev' (u sp - 48 + (D0v + L0v + 1)); lia.
  - ev' (u sp - 48 + ((D0v + L0v + 1) + L1v)); lia.
  - ev' L1v; lia.
  - ev' H1v; unfold H1v; lia.
  - ev' G1v; unfold G1v; lia.
  - rewrite (evE' (eadd END1 H1) (u sp - 48 + ((D0v + L0v + 1) + (L1v + H1v))) eq_refl); unfold H1v; lia.
  - rewrite (evE' (eadd END1 G1) (u sp - 48 + ((D0v + L0v + 1) + (L1v + G1v))) eq_refl); unfold G1v; lia.
  - rewrite (evE' (eadd L1 H1) (L1v + H1v) eq_refl); unfold H1v; lia.
  - exact Hbl.
Qed.

Lemma cont0_fact : kentry_ok ASEGS E' M (KShOk (SA SP0 48) (eaddz (eadd (eadd D0 L0) G0) (-48))).
Proof.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15).
  apply cont_fact. rewrite (evE' (eaddz (eadd (eadd D0 L0) G0) (-48)) (D0v + (L0v + G0v) + -48) eq_refl); unfold G0v, D0v in *; lia.
Qed.
Lemma cont1_fact : kentry_ok ASEGS E' M (KShOk (SA SP0 48) (eaddz (eadd (eadd D1 L1) G1) (-48))).
Proof.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15).
  apply cont_fact. rewrite (evE' (eaddz (eadd (eadd D1 L1) G1) (-48)) ((D0v + L0v + 1) + (L1v + G1v) + -48) eq_refl); unfold G1v, D0v in *; lia.
Qed.

(* [comment removed for export] *)
Lemma argv1_word : (1 < length argv)%nat -> kentry_ok ASEGS E' M (KWord (SA SP0 64) 8 STR1).
Proof.
  intros Hac.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15).
  pose proof (AsDrvBridgeArgv.sp_rng sp Hsp) as (S1 & S2 & S3).
  assert (KW : kentry_ok ASEGS E M (kw_argv1 (e_argv1w RS))).
  { apply boot_in. unfold BOOTF. apply in_or_app. right. right. right. right. left. reflexivity. }
  unfold kw_argv1 in KW. destruct KW as (_ & _ & KW).
  rewrite (adenot_val E e_sp0 16 (u sp + 16)) in KW by (rewrite ?sp0_val; lia).
  assert (Hs1 : u (edenot E (e_str1 RS)) = STRv 0 + L0v + 1).
  { (* [e_str1 RS]'s variable check is decided per flag value (its literal is symbolic in RS). *)
    rewrite (AsDrvBridgeArgv.sinv_val ph apc sp rdraw brk0 mbase inp E M HSINV (e_str1 RS)
               ltac:(destruct (kb_rseq (in_kernel inp)); reflexivity)).
    pose proof (AsSInit.u_e_str1 ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau) as U. unfold APS.uE in U. rewrite U.
    unfold AsDrvBridgeArgv.STRv, L0v. change (firstn 0 argv) with (@nil (list byte)).
    change (total_arg_bytes_nat []) with 0%nat. lia. }
  assert (Hw : edenot E (e_argv1w RS) = edenot E' STR1).
  { (* The range side condition: [D0v] is now [cat_string_off + 48], so its bound comes from
       [Hs1]'s word, read back through [STRv 0]; Stdlib's lia core, as at [below_facts]. *)
    apply bv_eq. rewrite (evE' STR1 (u sp - 48 + (D0v + L0v + 1)) eq_refl)
      by (pose proof (u64_range (edenot E (e_str1 RS))) as UR; rewrite Hs1 in UR;
          unfold AsDrvBridgeArgv.STRv in UR; change (firstn 0 argv) with (@nil (list byte)) in UR;
          change (total_arg_bytes_nat []) with 0%nat in UR; unfold D0v; Zify.zify; xlia zchecker).
    unfold e_argv1w. cbn [edenot Sem.mul_div Sem.alu64 Sem.alu]. unfold bv_ltu.
    pose proof boot_vals as (_ & _ & V1 & _). change V_ARGC with 1%nat. rewrite V1.
    replace (u (Z_to_bv 64 1) <? Z.of_nat (length argv)) with true by (symmetry; apply Z.ltb_lt; rewrite u64_lit by lia; lia).
    rewrite bv_mul_unsigned, bv_wrap64_mod, u64_lit by lia. rewrite Hs1.
    (* [Z.mod_small]'s range is [Hs1]'s word's own range; the last step reads [STRv 0]
       off [nums] (N7).  Stdlib's lia core, as above. *)
    rewrite Z.mod_small
      by (pose proof (u64_range (edenot E (e_str1 RS))) as UR; rewrite Hs1 in UR; Zify.zify; xlia zchecker).
    unfold D0v. Zify.zify; xlia zchecker. }
  cbn [kentry_ok]. split; [lia|]. split; [unfold flat, estart; cbn [a_base a_off]; rewrite SP0_val; lia|].
  rewrite (adenot_val E' SP0 64 (u sp + 16)) by (rewrite ?SP0_val; lia). rewrite <- Hw. exact KW.
Qed.

(* [comment removed for export] *)
Definition BIG0 : list kentry :=
  TKsyn ++ KS0 ++ [KWr (SA SP0 (- YLO)) (ELit YLO); KUnk (SA SP0 (- YLO)) (ELit YLO); KShOk (SA SP0 (- YLO)) (ELit (YLO + 48))]
  ++ [KShOk (SA SP0 48) (eaddz (eadd (eadd D0 L0) G0) (-48))] ++ (map (fun w => KWr (SA (fst w) 0) (snd w)) PERM_A ++ LOWSH ++ GLZSH).
Definition BIG1 : list kentry := KS1 ++ [KShOk (SA SP0 48) (eaddz (eadd (eadd D1 L1) G1) (-48)); KWord (SA SP0 64) 8 STR1].
Definition incl_b (k big : list kentry) : bool := forallb (fun K => existsb (kentry_eqb K) big) k.
Lemma incl_b_sound : forall Ex Mx k big, incl_b k big = true -> know_ok ASEGS Ex Mx big -> know_ok ASEGS Ex Mx k.
Proof.
  intros Ex Mx k big H HB. unfold know_ok in *. apply Forall_forall. intros K HK.
  pose proof (proj1 (forallb_forall _ _) H K HK) as X. apply existsb_exists in X as (K' & HK' & Heq).
  apply APS.kentry_eqb_eq in Heq. subst K'. exact (proj1 (Forall_forall _ _) HB K HK').
Qed.

Lemma big0_ok : bl 1%nat = nth 0 argv [] -> know_ok ASEGS E' M BIG0.
Proof.
  intros Hbl. unfold BIG0, know_ok.
  apply Forall_app; split; [exact know_syn'|]. apply Forall_app; split; [exact (ks0_facts Hbl)|].
  apply Forall_app; split; [exact stk_facts|]. apply Forall_app; split; [|exact lit_facts].
  apply Forall_cons; [exact cont0_fact | apply Forall_nil].
Qed.
Lemma big1_ok : (1 < length argv)%nat -> bl 2%nat = nth 1 argv [] -> know_ok ASEGS E' M BIG1.
Proof.
  intros Hac Hbl. unfold BIG1, know_ok. apply Forall_app. split; [exact (ks1_facts Hac Hbl)|].
  apply Forall_cons; [exact cont1_fact|]. apply Forall_cons; [exact (argv1_word Hac) | apply Forall_nil].
Qed.

(* [comment removed for export] *)
Variable bt : AsAinvDefs3.as_boot.
Hypothesis BT : AsAinvDefs3.bt_ia bt = AsVocab.AsCells.asan_addrs.
Hypothesis HCT : BE.ceil_top model.
Hypothesis HCS : GlzConst.RunCeil.CEIL <= u sp - 8388608.
#[local] Notation SHCb := (AzBridgeH.SHC_bt bt).

Definition VIS (z : Z) : Prop :=
  (0x10000 <= z < 0x65d000) \/ (GlzConst.RunCeil.CEIL <= z < 2 ^ 64) \/ (SB + 0x10000 / 8 <= z <= SB + (0x65d000 - 1) / 8) \/ (SB + GlzConst.RunCeil.CEIL / 8 <= z <= SB + (2 ^ 47 - 1) / 8).

Lemma IMG_le_A : img_lo AT_A <= img_hi AT_A. Proof. vm_compute. discriminate. Qed.
Lemma vis_hid : forall Ex csD (x : word), VIS (u x) -> GPS.hid SHCb [] Ex csD model x = false.
Proof.
  intros Ex csD x [H|[H|[H|H]]]; unfold GPS.hid.
  - rewrite (BE.lz_false_img ASEGS AT_A LIMIT_S ISP_S SINV argH fs asan_S_hull_ok E hs R M model x HC H). reflexivity.
  - rewrite (BE.lz_false_stack ASEGS AT_A LIMIT_S ISP_S SINV argH fs asan_S_hull_ok IMG_le_A E hs R M model x HC HCT (proj1 H)). reflexivity.
  - unfold GPS.vlz. rewrite (SHC_bt_img_asan bt BT AT_A eq_refl eq_refl (u x) (proj1 H) (proj2 H)). cbn [orb negb]. apply andb_false_r.
  - unfold GPS.vlz. rewrite (SHC_bt_stack bt (u x) (proj1 H) (proj2 H)). cbn [orb negb]. apply andb_false_r.
Qed.

Lemma vis_fact : forall Ex csD K, kentry_ok ASEGS Ex M K -> (forall z, AzKnowLib.in_kfoot Ex K z -> VIS z) ->
  kentry_ok ASEGS Ex (GPS.Mr SHCb [] Ex csD model M) K.
Proof.
  intros Ex csD K HK Hv. apply (AzKnowLib.kentry_ok_footprint ASEGS Ex M _ K HK).
  intros x Hx. unfold GPS.Mr, AsVocab.AsanAcct.mrestrict. rewrite (vis_hid Ex csD x (Hv _ Hx)). reflexivity.
Qed.
Lemma vis_list : forall Ex csD k, know_ok ASEGS Ex M k -> Forall (fun K => forall z, AzKnowLib.in_kfoot Ex K z -> VIS z) k ->
  know_ok ASEGS Ex (GPS.Mr SHCb [] Ex csD model M) k.
Proof.
  intros Ex csD k HK HV. unfold know_ok in *. apply Forall_forall. intros K Hin.
  exact (vis_fact Ex csD K (proj1 (Forall_forall _ _) HK K Hin) (proj1 (Forall_forall _ _) HV K Hin)).
Qed.

Lemma rng_vis_sound : forall s l z, rng_vis_b s l = true -> s <= z < s + l -> VIS z.
Proof.
  intros s l z H Hz. unfold rng_vis_b in H. apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2.
  - left. lia.
  - right. right. left. lia.
Qed.
Lemma lit_vis_sound : forall K Ex z, lit_vis_b K = true -> AzKnowLib.in_kfoot Ex K z -> VIS z.
Proof.
  intros K Ex z H Hz. unfold AzKnowLib.in_kfoot in Hz.
  destruct K as [[b o] w v|[b o] n|a n k|lo hi|e m|e lo hi|[b o] n|a1 n1 a2 n2|[b o] n c|[b o] n|[b o] n|v lo d]; cbn [lit_vis_b APS.kfoot] in H, Hz;
    try discriminate H; try (destruct Hz; fail).
  - destruct b as [a| | | | | | |]; try discriminate H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold estart in Hz. cbn [a_base a_off edenot] in Hz. rewrite u64_lit in Hz by lia.
    exact (rng_vis_sound _ _ z H3 Hz).
  - destruct b as [a| | | | | | |]; try discriminate H. destruct n as [n| | | | | | |]; try discriminate H.
    apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
    unfold estart, elenZ in Hz. cbn [a_base a_off edenot] in Hz. rewrite !u64_lit in Hz by lia. exact (rng_vis_sound _ _ z H5 Hz).
  - apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. left. lia.
  - destruct b as [a| | | | | | |]; try discriminate H. destruct n as [n| | | | | | |]; try discriminate H.
    apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
    unfold estart, elenZ in Hz. cbn [a_base a_off edenot] in Hz. rewrite !u64_lit in Hz by lia. exact (rng_vis_sound _ _ z H5 Hz).
  - destruct b as [a| | | | | | |]; try discriminate H. destruct n as [n| | | | | | |]; try discriminate H.
    apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
    unfold estart, elenZ in Hz. cbn [a_base a_off edenot] in Hz. rewrite !u64_lit in Hz by lia. exact (rng_vis_sound _ _ z H5 Hz).
  - destruct b as [a| | | | | | |]; try discriminate H. destruct n as [n| | | | | | |]; try discriminate H.
    apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
    unfold estart, elenZ in Hz. cbn [a_base a_off edenot] in Hz. rewrite !u64_lit in Hz by lia. exact (rng_vis_sound _ _ z H5 Hz).
  - destruct b as [a| | | | | | |]; try discriminate H. destruct n as [n| | | | | | |]; try discriminate H.
    apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4. apply Z.leb_le in H5. apply Z.leb_le in H6.
    unfold estart, elenZ in Hz. cbn [a_base a_off edenot] in Hz. rewrite !u64_lit in Hz by lia.
    right. right. left. unfold SB in *. Z.div_mod_to_equations. lia.
Qed.

Lemma sp_vis_sound : forall K z, sp_vis_b K = true -> AzKnowLib.in_kfoot E' K z -> VIS z.
Proof.
  intros K z H Hz. unfold AzKnowLib.in_kfoot in Hz. pose proof (AsDrvBridgeArgv.sp_rng sp Hsp) as (S1 & S2 & S3).
  pose proof SP0_val as HSP. unfold SP0 in HSP. cbn [edenot] in HSP.
  destruct K as [[b o] w v| | | | | |[b o] n| | |[b o] n| |]; cbn [sp_vis_b APS.kfoot] in H, Hz; try discriminate H;
    destruct b as [|[|vn]| | | | | |]; try discriminate H.
  - apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    unfold estart in Hz. cbn [a_base a_off edenot] in Hz. rewrite HSP in Hz. right. left. lia.
  - destruct n as [n| | | | | | |]; try discriminate H.
    apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.leb_le in H4.
    unfold estart, elenZ in Hz. cbn [a_base a_off edenot] in Hz. rewrite HSP, u64_lit in Hz by lia. right. left. lia.
  - destruct n as [n| | | | | | |]; try discriminate H.
    apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.leb_le in H4.
    unfold estart, elenZ in Hz. cbn [a_base a_off edenot] in Hz. rewrite HSP, u64_lit in Hz by lia. right. left. lia.
Qed.

(* [comment removed for export] *)
Lemma vis_app : forall K s l z, APS.kfoot E' K = Some (s, l) -> GlzConst.RunCeil.CEIL <= s -> s + l <= 2 ^ 64 -> AzKnowLib.in_kfoot E' K z -> VIS z.
Proof. intros K s l z HF H1 H2 Hz. unfold AzKnowLib.in_kfoot in Hz. rewrite HF in Hz. right. left. lia. Qed.
Lemma vis_shok : forall b o n s l z, u (edenot E' b) + o = s -> u (edenot E' n) = l -> GlzConst.RunCeil.CEIL <= s -> 1 <= l -> s + l <= 2 ^ 47 ->
  AzKnowLib.in_kfoot E' (KShOk (SA b o) n) z -> VIS z.
Proof.
  intros b o n s l z Hs Hl H1 H2 H3 Hz. unfold AzKnowLib.in_kfoot in Hz. cbn [APS.kfoot] in Hz. unfold estart, elenZ in Hz. cbn [a_base a_off] in Hz.
  rewrite Hs, Hl in Hz. right. right. right.
  assert (D1 : GlzConst.RunCeil.CEIL / 8 <= s / 8) by (apply Z.div_le_mono; lia).
  assert (D2 : (s + l - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia).
  lia.
Qed.

#[local] Notation VISF := (fun K => forall z, AzKnowLib.in_kfoot E' K z -> VIS z).
Lemma pure_vis : forall K, APS.kfoot E' K = None -> VISF K.
Proof. intros K H z Hz. unfold AzKnowLib.in_kfoot in Hz. rewrite H in Hz. destruct Hz. Qed.

Lemma str_vis : forall (eS eE eXA eXB eL eH eG eLH : expr) (j : nat) (Sv Lv : Z),
  STRv 0 <= Sv -> 0 <= Lv -> Sv + Lv + 1 <= STRend ->
  u (edenot E' eS) = Sv -> u (edenot E' eE) = Sv + Lv -> u (edenot E' eL) = Lv -> u (edenot E' eLH) = STRend - Sv ->
  Forall VISF [ KRange eG 10 4194304; KAlign eXB 64; KRange eXB 0 two47; KWord (SA eE 0) 1 (ELit 0); KBlob (SA eS 0) eL j;
                KRange eH 1 4194304; KAlign eXA 8; KRange eXA 1 two47; KUnk (SA eS 0) eLH ].
Proof.
  intros eS eE eXA eXB eL eH eG eLH j Sv Lv HS0 HL0 HSL HeS HeE HeL HeLH.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15).
  pose proof strend_rng as (R1 & R2 & R3 & R4 & R5).
  repeat apply Forall_cons; try apply Forall_nil; try (apply pure_vis; reflexivity).
  - intros z. apply (vis_app _ (Sv + Lv) 1); [cbn [APS.kfoot]; unfold estart; cbn [a_base a_off]; rewrite HeE, Z.add_0_r; reflexivity | lia | lia].
  - intros z. apply (vis_app _ Sv Lv); [cbn [APS.kfoot]; unfold estart, elenZ; cbn [a_base a_off]; rewrite HeS, HeL, Z.add_0_r; reflexivity | lia | lia].
  - intros z. apply (vis_app _ Sv (STRend - Sv)); [cbn [APS.kfoot]; unfold estart, elenZ; cbn [a_base a_off]; rewrite HeS, HeLH, Z.add_0_r; reflexivity | lia | lia].
Qed.

Lemma big0_vis : Forall VISF BIG0.
Proof.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15).
  pose proof strend_rng as (R1 & R2 & R3 & R4 & R5).
  assert (HS0 : u sp - 48 + D0v = STRv 0) by (unfold D0v; lia).
  unfold BIG0. apply Forall_app; split.
  { apply Forall_forall. intros K HK z Hz. pose proof (proj1 (forallb_forall _ _) vis_syn_b K HK) as X. cbv beta in X.
    destruct (lit_vis_b K) eqn:HL; [exact (lit_vis_sound K E' z HL Hz) | exact (sp_vis_sound K z X Hz)]. }
  apply Forall_app; split.
  { apply (str_vis STR0 END0 (eadd END0 H0) (eadd END0 G0) L0 H0 G0 (eadd L0 H0) 1 (STRv 0) L0v); try lia.
    - ev' (u sp - 48 + D0v); lia.
    - ev' (u sp - 48 + (D0v + L0v)); lia.
    - ev' L0v; lia.
    - rewrite (evE' (eadd L0 H0) (L0v + H0v) eq_refl); unfold H0v; lia. }
  apply Forall_app; split.
  { repeat apply Forall_cons; try apply Forall_nil.
    - intros z Hz. exact (sp_vis_sound (KWr (SA SP0 (- YLO)) (ELit YLO)) z eq_refl Hz).
    - intros z Hz. exact (sp_vis_sound (KUnk (SA SP0 (- YLO)) (ELit YLO)) z eq_refl Hz).
    - intros z. apply (vis_shok SP0 (- YLO) (ELit (YLO + 48)) (u sp - 6144000) (YLO + 48)); [rewrite SP0_val; unfold YLO; lia | cbn [edenot]; rewrite u64_lit by (unfold YLO; lia); reflexivity | lia | unfold YLO; lia | unfold YLO; lia]. }
  apply Forall_app; split.
  { apply Forall_cons; [|apply Forall_nil]. intros z.
    apply (vis_shok SP0 48 _ (u sp) (XBv - u sp)); [rewrite SP0_val; lia | | lia | lia | lia].
    rewrite (evE' (eaddz (eadd (eadd D0 L0) G0) (-48)) (D0v + (L0v + G0v) + -48) eq_refl); unfold G0v, D0v in *; lia. }
  apply Forall_forall. intros K HK z Hz. exact (lit_vis_sound K E' z (proj1 (forallb_forall _ _) vis_lit_b K HK) Hz).
Qed.

Lemma big1_vis : (1 < length argv)%nat -> Forall VISF BIG1.
Proof.
  intros Hac.
  pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15).
  pose proof strend_rng as (R1 & R2 & R3 & R4 & R5). pose proof (R5 1%nat Hac) as R6.
  pose proof (STR1v Hac) as S1.
  destruct (AsDrvBridgeArgv.str_end ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hvl Hlau 1 Hac) as (E1 & E2 & E3). fold L1v in E1.
  assert (HS0 : u sp - 48 + D0v = STRv 0) by (unfold D0v; lia).
  unfold BIG1. apply Forall_app; split.
  { apply (str_vis STR1 END1 (eadd END1 H1) (eadd END1 G1) L1 H1 G1 (eadd L1 H1) 2 (STRv 1) L1v); try lia.
    - ev' (u sp - 48 + (D0v + L0v + 1)); lia.
    - ev' (u sp - 48 + ((D0v + L0v + 1) + L1v)); lia.
    - ev' L1v; lia.
    - rewrite (evE' (eadd L1 H1) (L1v + H1v) eq_refl); unfold H1v; lia. }
  repeat apply Forall_cons; try apply Forall_nil.
  - intros z. apply (vis_shok SP0 48 _ (u sp) (XBv - u sp)); [rewrite SP0_val; lia | | lia | lia | lia].
    rewrite (evE' (eaddz (eadd (eadd D1 L1) G1) (-48)) ((D0v + L0v + 1) + (L1v + G1v) + -48) eq_refl); unfold G1v, D0v in *; lia.
  - intros z Hz. exact (sp_vis_sound (KWord (SA SP0 64) 8 STR1) z eq_refl Hz).
Qed.

(* [comment removed for export] *)
Theorem gps_big0 : bl 1%nat = nth 0 argv [] -> forall csD, know_ok ASEGS E' (GPS.Mr SHCb [] E' csD model M) BIG0.
Proof. intros Hbl csD. exact (vis_list E' csD BIG0 (big0_ok Hbl) big0_vis). Qed.
Theorem gps_big1 : (1 < length argv)%nat -> bl 2%nat = nth 1 argv [] -> forall csD, know_ok ASEGS E' (GPS.Mr SHCb [] E' csD model M) BIG1.
Proof. intros Hac Hbl csD. exact (vis_list E' csD BIG1 (big1_ok Hac Hbl) (big1_vis Hac)). Qed.

(* [comment removed for export] *)
Context {SFL : GPS.stk_floor}.
Hypothesis HSF : GPS.SFLOOR <= u sp - 8388608.
Variable KCAP : Z.
Hypothesis HKCAP : 0 <= KCAP.
Variable AINVc : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HAINV : AINVc [] [] 0 0 0 M model.
Variable UINV : env -> Prop.
Hypothesis HU : UINV E'.
Variable fx : GPS.FX.
Hypothesis Hfx : AzSymStepR.fx_ok fx.

(* [comment removed for export] *)
Definition main_shape (tX : acs) : Prop :=
  s_regs (a_ss tX) = regsM /\ s_log (a_ss tX) = [] /\ a_vis tX = [] /\ a_fake tX = [] /\ a_ghost tX = PERM_A /\ a_brk tX = eaddz SP0 0
  /\ a_ylo tX = YLO /\ a_fd tX = FdStd /\ a_meter tX = ELit 0 /\ a_fbud tX = ELit FMIN /\ a_maps tX = [].

Theorem cs_ok_main : forall tX, main_shape tX ->
  know_ok ASEGS E' (GPS.Mr SHCb [] E' tX model M) (kn tX) ->
  GPS.cs_ok ASEGS PERM_A_lit (u sp - 48) fs SHCb [] AINVc KCAP FMIN AzSymStepR.fx_ok UINV E' tX fx R M model.
Proof.
  intros tX (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11) HK.
  pose proof (AsDrvBridgeArgv.sp_rng sp Hsp) as (R1 & R2 & R3).
  assert (HT : GPS.uE E' (eaddz SP0 0) = u sp - 48) by (unfold GPS.uE; apply (evE' (eaddz SP0 0) (u sp - 48) eq_refl); lia).
  constructor.
  - rewrite S1. exact regs_syn'.
  - exact S2.
  - exact HK.
  - exact (APS.co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC).
  - exact (APS.co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC).
  - rewrite S8. pose proof (APS.co_fds _ _ _ _ _ _ _ _ _ _ _ _ HC) as FD.
    (* The hand-off state's descriptor table is [FdStd] at both CONFIG_RSEQ values; with the
       flag symbolic the table lookup does not reduce, so it is rewritten first. *)
    assert (AF : forall b, a_fd (HS_1 (rseq_z b)) = FdStd /\ a_fd (HS_2 (rseq_z b)) = FdStd)
      by (intros [|]; split; vm_compute; reflexivity).
    destruct Hhs as [-> | ->];
      [rewrite (proj1 (AF (kb_rseq (in_kernel inp)))) in FD | rewrite (proj2 (AF (kb_rseq (in_kernel inp)))) in FD];
      exact FD.
  - rewrite S3, S4, S9. exact HAINV.
  - exact HU.
  - exact Hfx.
  - rewrite S5. apply PERM_A_den.
  - rewrite S6. unfold GPS.sptop_den. rewrite HT. replace (u sp - 48 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - rewrite S9. unfold GPS.uE. cbn [edenot]. rewrite u64_lit by lia. exact HKCAP.
  - rewrite S4, S10. cbn [length]. unfold GPS.uE. cbn [edenot]. rewrite u64_lit by (unfold FMIN; lia). unfold FMIN. lia.
  - rewrite S11, S6, S7. cbn [acs_floor GPS.floor_sem]. unfold GPS.sptop_den. rewrite HT.
    replace (u sp - 48 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). unfold YLO. lia.
  - (* [co_rdr], the record's field at this revision: the hand-off invariant's own reader. *)
    exact (APS.co_rdr _ _ _ _ _ _ _ _ _ _ _ _ HC).
Qed.

(* [comment removed for export] *)
Lemma knM_in_big0 : incl_b knM BIG0 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma knO_in_big : incl_b (tl knO) (BIG0 ++ BIG1) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
#[local] Notation cs_okM := (GPS.cs_ok ASEGS PERM_A_lit (u sp - 48) fs SHCb [] AINVc KCAP FMIN AzSymStepR.fx_ok UINV E').
#[local] Notation Mg tX := (GPS.Mr SHCb [] E' tX model M).
Hypothesis Hbl1 : bl 1%nat = nth 0 argv [].

Lemma kn_M : forall tX, know_ok ASEGS E' (Mg tX) knM.
Proof. intros tX. exact (incl_b_sound E' _ knM BIG0 knM_in_big0 (gps_big0 Hbl1 tX)). Qed.
Lemma kn_O : (length argv = 2)%nat -> bl 2%nat = nth 1 argv [] -> forall tX, know_ok ASEGS E' (Mg tX) knO.
Proof.
  intros Hac Hbl2 tX. pose proof vals'_ok as (_ & W1 & _).
  change knO with (KRange ARGC 2 2 :: tl knO). apply Forall_cons.
  - cbn [kentry_ok]. unfold ARGC. cbn [edenot]. rewrite W1, Hac. cbn. lia.
  - apply (incl_b_sound E' _ (tl knO) (BIG0 ++ BIG1) knO_in_big). unfold know_ok. apply Forall_app. split.
    + exact (gps_big0 Hbl1 tX).
    + exact (gps_big1 ltac:(lia) Hbl2 tX).
Qed.

(* [comment removed for export] *)
Lemma krange_val : forall Mx e lo hi z, u (edenot E' e) = z -> lo <= z <= hi -> kentry_ok ASEGS E' Mx (KRange e lo hi).
Proof. intros Mx e lo hi z H Hz. cbn [kentry_ok]. rewrite H. exact Hz. Qed.
Lemma ARGC_val : u (edenot E' ARGC) = Z.of_nat (length argv).
Proof. pose proof nums as (_ & _ & N3 & _). apply (evE' ARGC _ eq_refl). lia. Qed.
Lemma L0_val : u (edenot E' L0) = L0v.
Proof. pose proof nums as (_ & _ & _ & _ & N5 & _). apply (evE' L0 _ eq_refl). lia. Qed.
Lemma L1_val : u (edenot E' L1) = L1v.
Proof. pose proof nums as (_ & _ & _ & _ & _ & N6 & _). apply (evE' L1 _ eq_refl). lia. Qed.
Lemma FINFO_val : 0 <= mk < 2 ^ 64 -> u (edenot E' (EVar 4)) = mk.
Proof. intros Hm. change (edenot E' (EVar 4)) with (Z_to_bv 64 mk). apply u64_lit. exact Hm. Qed.

(* [comment removed for export] *)
Lemma cs_ok_inst0 : forall J e inv, s_log (a_ss inv) = [] -> ev E' J = edenot E' e -> cs_okM inv fx R M model -> cs_okM (inst inv J e) fx R M model.
Proof.
  intros J e inv Hlog Hev HCI.
  set (UT := fun _ : env => True).
  assert (H1 : GPS.cs_ok ASEGS PERM_A_lit (u sp - 48) fs SHCb [] AINVc KCAP FMIN AzSymStepR.fx_ok UT E' inv fx R M model)
    by (destruct HCI; constructor; try assumption; exact I).
  assert (HE : APS.upd E' J (edenot E' e) = E').
  { unfold APS.upd, E'. cbn [ev eb]. f_equal. apply FunctionalExtensionality.functional_extensionality. intros n.
    destruct (Nat.eqb_spec n J) as [->|Hne]; [|reflexivity]. symmetry. exact Hev. }
  pose proof (proj2 (GPS.cs_ok_inst ASEGS 0%nat PERM_A_lit (u sp - 48) fs SHCb [] AINVc KCAP FMIN AzSymStepR.fx_ok UT (fun _ _ _ _ => I)
                       E' J e inv fx R M model ltac:(lia) Hlog)) as X.
  rewrite HE in X. specialize (X H1). destruct X; constructor; assumption.
Qed.

Ltac shape := repeat split; reflexivity.
Ltac kr z := apply (krange_val _ _ _ _ z).
Lemma ev_zero : forall J, u (ev E' J) = 0 -> ev E' J = edenot E' (ELit 0).
Proof. intros J H. apply bv_eq. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Theorem cs_tMu1 : length argv = 1%nat -> cs_okM tMu1 fx R M model.
Proof.
  intros Hac. apply cs_ok_main; [shape|]. change (kn tMu1) with ([KRange ARGC 1 1] ++ knM). apply Forall_app. split; [|exact (kn_M tMu1)].
  apply Forall_cons; [|apply Forall_nil]. kr (Z.of_nat (length argv)); [exact ARGC_val | lia].
Qed.
Theorem cs_tMu3 : (3 <= length argv)%nat -> cs_okM tMu3 fx R M model.
Proof.
  intros Hac. pose proof nums as (_ & _ & N3 & _). apply cs_ok_main; [shape|]. change (kn tMu3) with ([KRange ARGC 3 1024] ++ knM).
  apply Forall_app. split; [|exact (kn_M tMu3)]. apply Forall_cons; [|apply Forall_nil]. kr (Z.of_nat (length argv)); [exact ARGC_val | lia].
Qed.
Theorem cs_tMu1n : length argv = 1%nat -> 1 <= L0v -> cs_okM tMu1n fx R M model.
Proof.
  intros Hac HL. pose proof nums as (_ & _ & _ & _ & N5 & _). apply cs_ok_main; [shape|].
  change (kn tMu1n) with ([KRange L0 1 131071] ++ [KRange ARGC 1 1] ++ knM). apply Forall_app. split; [|apply Forall_app; split; [|exact (kn_M tMu1n)]].
  - apply Forall_cons; [|apply Forall_nil]. kr L0v; [exact L0_val | lia].
  - apply Forall_cons; [|apply Forall_nil]. kr (Z.of_nat (length argv)); [exact ARGC_val | lia].
Qed.
Theorem cs_tMu3n : (3 <= length argv)%nat -> 1 <= L0v -> cs_okM tMu3n fx R M model.
Proof.
  intros Hac HL. pose proof nums as (_ & _ & N3 & _ & N5 & _). apply cs_ok_main; [shape|].
  change (kn tMu3n) with ([KRange L0 1 131071] ++ [KRange ARGC 3 1024] ++ knM). apply Forall_app. split; [|apply Forall_app; split; [|exact (kn_M tMu3n)]].
  - apply Forall_cons; [|apply Forall_nil]. kr L0v; [exact L0_val | lia].
  - apply Forall_cons; [|apply Forall_nil]. kr (Z.of_nat (length argv)); [exact ARGC_val | lia].
Qed.
Theorem cs_tMu1z : length argv = 1%nat -> L0v = 0 -> cs_okM tMu1z fx R M model.
Proof.
  intros Hac HL. apply (cs_ok_inst0 3 (ELit 0) tMu1 eq_refl); [|exact (cs_tMu1 Hac)].
  apply ev_zero. pose proof L0_val as X. unfold L0 in X. cbn [edenot] in X. lia.
Qed.
Theorem cs_tMu3z : (3 <= length argv)%nat -> L0v = 0 -> cs_okM tMu3z fx R M model.
Proof.
  intros Hac HL. apply (cs_ok_inst0 3 (ELit 0) tMu3 eq_refl); [|exact (cs_tMu3 Hac)].
  apply ev_zero. pose proof L0_val as X. unfold L0 in X. cbn [edenot] in X. lia.
Qed.

(* [comment removed for export] *)
Hypothesis Hbl2 : bl 2%nat = nth 1 argv [].
Theorem cs_tMo : length argv = 2%nat -> cs_okM tMo fx R M model.
Proof.
  intros Hac. apply cs_ok_main; [shape|]. change (kn tMo) with (knO ++ knM). apply Forall_app. split; [exact (kn_O Hac Hbl2 tMo) | exact (kn_M tMo)].
Qed.
Lemma cs_tMo_cls : forall CLS, length argv = 2%nat -> Forall (kentry_ok ASEGS E' (Mg (add_kn tMo CLS))) CLS -> cs_okM (add_kn tMo CLS) fx R M model.
Proof.
  intros CLS Hac HCLS. apply cs_ok_main; [shape|]. change (kn (add_kn tMo CLS)) with (CLS ++ knO ++ knM).
  apply Forall_app. split; [exact HCLS|]. apply Forall_app. split; [exact (kn_O Hac Hbl2 _) | exact (kn_M _)].
Qed.
Theorem cs_tMoa : length argv = 2%nat -> 1 <= L1v <= 4095 -> mk = DNA.CLS_ABSENT -> cs_okM tMoa fx R M model.
Proof.
  intros Hac HL Hmk. apply (cs_tMo_cls _ Hac). repeat apply Forall_cons; try apply Forall_nil.
  - kr L1v; [exact L1_val | lia].
  - kr mk; [apply FINFO_val; rewrite Hmk; unfold DNA.CLS_ABSENT; lia | lia].
Qed.
Theorem cs_tMod : length argv = 2%nat -> 1 <= L1v <= 4095 -> mk = DNA.CLS_DIR -> cs_okM tMod fx R M model.
Proof.
  intros Hac HL Hmk. apply (cs_tMo_cls _ Hac). repeat apply Forall_cons; try apply Forall_nil.
  - kr L1v; [exact L1_val | lia].
  - kr mk; [apply FINFO_val; rewrite Hmk; unfold DNA.CLS_DIR; lia | lia].
Qed.
Theorem cs_tMot : length argv = 2%nat -> 4096 <= L1v -> cs_okM tMot fx R M model.
Proof.
  intros Hac HL. pose proof nums as (_ & _ & _ & _ & _ & N6 & _). apply (cs_tMo_cls _ Hac). repeat apply Forall_cons; try apply Forall_nil.
  kr L1v; [exact L1_val | lia].
Qed.
Theorem cs_tMf : length argv = 2%nat -> 1 <= L1v <= 4095 -> 0 <= mk <= FLENHI -> cs_okM tMf fx R M model.
Proof.
  intros Hac HL Hmk. apply (cs_tMo_cls _ Hac). repeat apply Forall_cons; try apply Forall_nil.
  - kr L1v; [exact L1_val | lia].
  - kr mk; [apply FINFO_val; unfold FLENHI in Hmk; lia | lia].
Qed.
Theorem cs_tMoz : length argv = 2%nat -> L1v = 0 -> mk = DNA.CLS_ABSENT -> cs_okM tMoz fx R M model.
Proof.
  intros Hac HL Hmk.
  assert (HI : cs_okM (inst tMo 6 (ELit 0)) fx R M model).
  { apply (cs_ok_inst0 6 (ELit 0) tMo eq_refl); [|exact (cs_tMo Hac)].
    apply ev_zero. pose proof L1_val as X. unfold L1 in X. cbn [edenot] in X. lia. }
  unfold tMoz, add_kn. apply GPS.cs_ok_set_kn; [exact HI|].
  apply Forall_app. split; [|exact (GPS.co_know HI)].
  apply Forall_cons; [|apply Forall_nil]. kr mk; [apply FINFO_val; rewrite Hmk; unfold DNA.CLS_ABSENT; lia | lia].
Qed.
End Bridge.
