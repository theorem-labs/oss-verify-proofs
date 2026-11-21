(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput; the launch premises valid_launch and entry_launch_ok_va; the launch's reservations with the vDSO pair; the CONFIG_RSEQ flag of the start-up layer; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec StoreOk CatExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout MemSplit RefMemcpyLib FxLin FxMem.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout OSSVerify.Proofs.fast_float.from_chars.lib.Common.MemSplit OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Image.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface HIfaceInit.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UbStartup UbStartupDefs UDrvData UDrvMain UHeapInit UHeapIGlue.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfKf.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxMalloc MngRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import MngL4 MngL4I.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngRz2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Open Scope Z_scope.

Local Ltac bvlit := vm_compute; try (f_equal; repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]); try reflexivity).

(* LPS 08b1429: the auxv the kernel writes is StackLayout.auxv_entries', not the
   ten-entry table this file used to assume.  Twenty-six types, in the model's own
   order (StackLayout.v:auxv_entries at 75d69e00), and two more when the kernel
   declares rseq; AT_NULL terminates the table, so [MngL4.init_env] finds it at
   AUXV + 16 * length TYPS and the length is NOT a constant any more. *)
Definition TYPS (rseq : bool) : list Z :=
  [33; 40; 41; 42; 43; 44; 45; 46; 47; 51; 16; 6; 17; 3; 4; 5; 7; 8; 9; 11; 12; 13; 14; 23; 25; 31]
  ++ (if rseq then [27; 28] else []).

Lemma TYPS_len : forall r, Z.of_nat (length (TYPS r)) = Z.of_nat (auxv_count r) - 1.
Proof. intros [|]; reflexivity. Qed.

(* MEASURED CURE, 2026-11-07.  The twin of PHeapTyps.v's [TYPS_pos], byte
   for byte, and the reason the P and U builds died at the same 64.00 GiB cap inside two
   differently-named targets (the P build inside the
   PHeapTyps.vo invocation; the U build inside this
   file's).  Named by measuring nine one-sentence twins of PHeapTyps.v:
   the header alone and [bview_none]/[wview_none]/[tot_firstn2] all cheap, [TYPS_rnd] green
   at 2.0 GiB, only this sentence running away.
   THE SHAPE: `repeat (destruct i as [|i]; [cbn [nth app]; lia|])` has NO FIXED POINT.
   Once the destructs pass the end of the list the goal is [1 <= nth i [] 0 <= 2^64-1],
   i.e. [1 <= 0 <= ...], and [Hi : S^k i < 26] is FALSE -- so [lia] closes that branch too
   and the [repeat] never fails.  Every further iteration adds one [S] and calls [lia]
   again, and [lia] here is not Stdlib's: this file Requires two global rebindings of it
   (Common/Lib/LiaTuning.v:188, Common/PropExec.v:49), both context-reading tier batteries.
   Hence the runaway signature -- one core, no error, no frontier, memory climbing to the
   ceiling whatever the ceiling is.
   The list is decided data, so the question is one closed boolean, run ONCE on the VM at
   [Qed] through [vm_cast_no_check] -- this file's own cure for [tables_img_ok] and
   [ctx_img_zero], now applied to the last uncured sentence.
   [TYPS_pos]'s STATEMENT below is unchanged to the character; only its proof differs. *)
Lemma TYPS_pos_b : forall r, forallb (fun z => (1 <=? z) && (z <=? 2 ^ 64 - 1))%bool (TYPS r) = true.
Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.

Lemma TYPS_pos : forall r i, (i < length (TYPS r))%nat -> 1 <= nth i (TYPS r) 0 <= 2 ^ 64 - 1.
Proof.
  intros r i Hi.
  assert (Hin : In (nth i (TYPS r) 0) (TYPS r)) by (apply nth_In; exact Hi).
  pose proof (proj1 (forallb_forall _ _) (TYPS_pos_b r) _ Hin) as Hb.
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [exact H1 | exact H2].
Qed.

Lemma TYPS_rnd : forall r, In 25 (TYPS r).
Proof. intros r. unfold TYPS. destruct r; cbn [app]; repeat (first [apply in_eq | apply in_cons]). Qed.

(* 25 (AT_RANDOM) occurs once, at index 24 in either table. *)
(* MEASURED CURE, 2026-11-07.  The byte-identical twin of PHeapTyps.v's
   TYPS_rnd_idx, and the SECOND non-termination bug in this pair: the uncured form hung
   the first build of the cured files inside PHeapTyps.vo
   after TYPS_pos passed.  `repeat (destruct i as [|i]; [ ... first [reflexivity |
   discriminate Hc] |])` has no fixed point -- past the end of TYPS the hypothesis is
   `nth i [] 0 = 25`, i.e. `0 = 25`, which `discriminate` closes, so the bracket succeeds
   on the out-of-range branch and `repeat` peels S forever.  Same cure as TYPS_pos: one
   closed boolean over the concrete list, decided once on the VM.
   The statement below is unchanged to the character; TYPS_rnd_idx_b is an added helper. *)
Lemma TYPS_rnd_idx_b : forall r,
  forallb (fun i => implb (Z.eqb (nth i (TYPS r) 0) 25) (Nat.eqb i 24)) (seq 0 (length (TYPS r))) = true.
Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.

Lemma TYPS_rnd_idx : forall r i, nth i (TYPS r) 0 = 25 -> (i < length (TYPS r))%nat -> i = 24%nat.
Proof.
  intros r i Hnth Hi.
  assert (Hin : In i (seq 0 (length (TYPS r)))) by
    (apply in_seq; split; [apply Nat.le_0_l | rewrite Nat.add_0_l; exact Hi]).
  pose proof (proj1 (forallb_forall _ _) (TYPS_rnd_idx_b r) i Hin) as Hb.
  cbv beta in Hb.
  rewrite Hnth, Z.eqb_refl in Hb. cbn [implb] in Hb.
  apply Nat.eqb_eq. exact Hb.
Qed.

(* [comment removed for export] *)
Definition opt_bytes_eqb (a b : option (list byte)) : bool :=
  match a, b with
  | Some x, Some y => (Nat.eqb (length x) (length y) && forallb (fun '(u, v) => bv_eqb u v) (combine x y))%bool
  | None, None => true
  | _, _ => false
  end.
Lemma opt_bytes_eqb_eq : forall a b, opt_bytes_eqb a b = true -> a = b.
Proof.
  intros [x|] [y|] H; cbn in H; try discriminate; [|reflexivity]. f_equal.
  apply andb_prop in H as [Hl Hc]. apply Nat.eqb_eq in Hl. revert y Hl Hc.
  induction x as [|u x IH]; intros [|v y] Hl Hc; cbn in *; try discriminate; [reflexivity|].
  apply andb_prop in Hc as [Huv Hc]. apply bv_eqb_eq in Huv. subst v. f_equal. apply IH; [lia | exact Hc].
Qed.

(* MEASURED CURE, 2026-11-07.  The same two VM pathologies the P side
   has already paid for, still uncured on this twin.  Both are PHeapImgCtx.v's own
   finding, in its header comment:
     (1) [vm_compute. reflexivity.] runs the VM TWICE -- once in the tactic and again
         over the VMcast at [Qed] -- and holds the tactic-time normal form alive in
         between; [vm_cast_no_check] runs it ONCE, at [Qed].
     (2) a window whose body is a read of the ELF image has its whole reduction live
         at once, so it is proved in halves, each its own lemma and so its own VM heap.
   [ctx_img_zero] below is the 928-byte window: the P side's identical shape was
   measured at >= 33.96 GiB, monotonic and still climbing at t = 4149.82 s on one core
   in one build, and at 4.22 GiB and 191 s in the cured shape
   in another.  [tables_img_ok] is the shape that killed
   three builds
   at 48.00 GiB inside PHeapImgTab.v.
   EVERY STATEMENT BELOW IS UNCHANGED TO THE CHARACTER; only the proofs differ, and
   the helper lemmas state the originals' conjuncts and halves verbatim. *)
Lemma tables_img_ok_sc :
  forallb (fun sc => opt_bytes_eqb (rdn PSEGS (fun _ => None) (wa (98984 + 2 * Z.of_nat sc)) 2)
                                   (Some (word_to_le_bytes 2 (wa (znth (Z.of_nat sc) size_classes))))) (seq 0 48) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma tables_img_ok_db :
  forallb (fun j => opt_bytes_eqb (rdn PSEGS (fun _ => None) (wa (98952 + Z.of_nat j)) 1)
                                  (Some (word_to_le_bytes 1 (wa (znth (Z.of_nat j) debruijn))))) (seq 0 32) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma ctx_img_zero_c0 : forallb (fun i => match bview PSEGS (fun _ => None) (0x97c98 + Z.of_nat i) with Some 0 => true | _ => false end) (seq 0 464) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma ctx_img_zero_c1 : forallb (fun i => match bview PSEGS (fun _ => None) (0x97c98 + Z.of_nat i) with Some 0 => true | _ => false end) (seq 464 464) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma tables_img_ok :
  forallb (fun sc => opt_bytes_eqb (rdn PSEGS (fun _ => None) (wa (98984 + 2 * Z.of_nat sc)) 2)
                                   (Some (word_to_le_bytes 2 (wa (znth (Z.of_nat sc) size_classes))))) (seq 0 48) = true /\
  forallb (fun j => opt_bytes_eqb (rdn PSEGS (fun _ => None) (wa (98952 + Z.of_nat j)) 1)
                                  (Some (word_to_le_bytes 1 (wa (znth (Z.of_nat j) debruijn))))) (seq 0 32) = true.
Proof. split; [exact tables_img_ok_sc | exact tables_img_ok_db]. Qed.

Lemma ctx_img_zero : forallb (fun i => match bview PSEGS (fun _ => None) (0x97c98 + Z.of_nat i) with Some 0 => true | _ => false end) (seq 0 928) = true.
Proof.
  change 928%nat with (464 + 464)%nat.
  rewrite (seq_app 464 464 0), forallb_app, ctx_img_zero_c0.
  cbn [Nat.add]. rewrite ctx_img_zero_c1. reflexivity.
Qed.

Lemma errno_img_w : forallb (fun i => match wview PSEGS (fun _ => None) (wa (0x778ec + Z.of_nat i)) with Some _ => true | None => false end) (seq 0 4) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bview_none : forall m x, m (wa x) = None -> bview PSEGS m x = bview PSEGS (fun _ => None) x.
Proof. intros m x H. unfold bview, RiscvSemantics.wview. cbn [RiscvSemantics.ov_read_bytes]. rewrite H. reflexivity. Qed.
Lemma wview_none : forall m a, m a = None -> wview PSEGS m a = wview PSEGS (fun _ => None) a.
Proof. intros m a H. unfold RiscvSemantics.wview. rewrite H. reflexivity. Qed.

Lemma tot_firstn2 : forall l : list (list byte), (2 <= length l)%nat ->
  total_arg_bytes_nat (firstn 2 l) = (total_arg_bytes_nat (firstn 1 l) + length (nth 1 l []) + 1)%nat.
Proof. intros [|a [|b l]] H; cbn [length] in H; try lia. simpl. lia. Qed.

Section HIS.
(* LPS 08b1429: the section takes the launch ([inp], [mbase], [entry], [brk], with
   [Hvl] and [Hlau]) instead of argv/envp/uid/hwcap, as UDrvMain's Handoff section
   does; [Hfits] is kept so the statement is unchanged, now stated over the [av]/[ev]
   notations.  [brk] is the launch's program break, so [heapI_main] no longer
   quantifies over one of its own: [Hlau] names it. *)
Variable inp : ProcInput.
Variables mbase entry : word.
Variables sp0 brk : word.
Variable tid : word.
Variable rdraw : EntryDraw.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Local Notation av := (in_argv inp) (only parsing).
Local Notation ev := (in_envp inp) (only parsing).
Hypothesis Hsp : valid_sp sp0.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
Hypothesis Hfits : entry_stack_fits sp0 av ev.
Hypothesis ME : main_entry inp mbase entry sp0 rdraw tid regs mem.

Local Notation RSQ := (kb_rseq (in_kernel inp)) (only parsing).
Local Notation AUXV := (bv_unsigned sp0 + Z.of_nat (auxv_off av ev)).
Local Notation RND := (bv_unsigned (at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev)).
Local Notation bsb := (entry_stack_image inp mbase RPH entry sp0 rdraw) (only parsing).
(* The auxv words of THIS launch: [StackLayout.auxv_words] now takes the whole
   launch auxv, the phdr record, the entry point and both ids. *)
Local Notation AUXW := (auxv_words (launch_auxv inp sp0 mbase) RPH entry
                          (in_uid inp) (in_gid inp) (in_hwcap inp)
                          (at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev)
                          (at_execfn_ptr (ed_top rdraw) (in_execfn inp))) (only parsing).

#[using="Hsp"] Lemma his_sp : 0x7fff80000000 <= bv_unsigned sp0 /\ bv_unsigned sp0 <= 0x800000000000 /\ bv_unsigned sp0 mod 16 = 0.
Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0). destruct Hsp as (A & B & C). unfold sp_window_lo, sp_window_hi in *. lia. Qed.

(* The head block is a prefix of the image; [length_build_stack_bytes] is the only
   fact about the image's length this file needs below the launch bound. *)
#[using="mbase entry"] Lemma his_head_le : (block_head_size RSQ av ev <= length bsb)%nat.
Proof. LiaFast.lf_pins (fun (mbase entry : LiaFast.U) => LiaFast.u0).
  unfold entry_stack_image. rewrite length_build_stack_bytes. cbn [launch_auxv la_rseq]. lia.
Qed.

(* LPS 08b1429: [build_stack_bytes_within_span] is gone; the image now runs from
   [sp0] to the draw's page-aligned [ed_top], and the launch bounds that top. *)
#[using="mbase entry brk Hlau"] Lemma his_block : bv_unsigned sp0 + Z.of_nat (length bsb) <= 2 ^ 47.
Proof. LiaFast.lf_pins (fun (mbase entry brk Hlau : LiaFast.U) => LiaFast.u0).
  rewrite (length_entry_stack_image_launch Sv48 inp mbase RPH entry sp0 brk rdraw Hlau).
  pose proof (entry_page_top_within_window Sv48 inp mbase sp0 brk rdraw Hlau) as W.
  unfold entry_page_top in W. cbn [va_stack_top] in W. unfold sp_window_hi in W. lia.
Qed.

#[using="mbase entry"] Lemma his_auxv_off : Z.of_nat (auxv_off av ev) + Z.of_nat (auxv_size RSQ) + 16 <= Z.of_nat (length bsb).
Proof. LiaFast.lf_pins (fun (mbase entry : LiaFast.U) => LiaFast.u0).
  pose proof his_head_le as H. unfold auxv_off, block_head_size, block_items in *. cbv zeta in *. lia.
Qed.

(* AT_RANDOM sits sixteen bytes below the end of the head block. *)
#[using="mbase entry brk Hlau Hsp"] Lemma his_rnd_eq : RND = bv_unsigned sp0 + Z.of_nat (block_head_size RSQ av ev - 16).
Proof. LiaFast.lf_pins (fun (mbase entry brk Hlau Hsp : LiaFast.U) => LiaFast.u0).
  pose proof his_sp as (L & H & _). pose proof his_block as B. pose proof his_head_le as HB.
  unfold at_random_ptr. rewrite word_add_nat. apply u_small64. unfold two64. lia.
Qed.

(* The auxv is at least 432 bytes ([UDrvMain.auxv_size_ge432], the only auxv-size
   fact), so the random bytes sit well above the auxv's own first word. *)
#[using="mbase entry brk Hlau Hsp"] Lemma his_rnd_lo : bv_unsigned sp0 + Z.of_nat (auxv_off av ev) + 432 <= RND.
Proof. LiaFast.lf_pins (fun (mbase entry brk Hlau Hsp : LiaFast.U) => LiaFast.u0).
  pose proof his_rnd_eq as E. pose proof (auxv_size_ge432 RSQ) as A.
  rewrite E. unfold auxv_off, block_head_size, block_items. cbv zeta. lia.
Qed.

(* [comment removed for export] *)
#[using="inp mbase entry sp0 tid rdraw regs Hsp ME"] Lemma hi_page : rdn PSEGS mem (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096)).
Proof. LiaFast.lf_pins (fun (inp mbase entry sp0 tid rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0).
  pose proof his_sp as (L & _).
  rewrite (main_entry_rdn_data _ _ _ _ _ _ _ _ ME) by (unfold wa; rewrite u_small64 by (unfold two64; lia); unfold stack_max_size; lia).
  reflexivity.
Qed.

#[using="inp mbase entry sp0 tid rdraw regs Hsp ME"] Lemma hi_auxv_ptr : rdn PSEGS mem (wa 621608) 8 = Some (word_to_le_bytes 8 (wa AUXV)).
Proof. LiaFast.lf_pins (fun (inp mbase entry sp0 tid rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0).
  pose proof his_sp as (L & _).
  rewrite (main_entry_rdn_data _ _ _ _ _ _ _ _ ME) by (unfold wa; rewrite u_small64 by (unfold two64; lia); unfold stack_max_size; lia).
  transitivity (Some (word_to_le_bytes 8 (auxv_w inp sp0))); [reflexivity|].
  unfold auxv_w, wa, auxv_off. do 3 f_equal. lia.
Qed.

(* LPS 08b1429: [read_auxv_word] reads the launch's own auxv and derives its
   no-wrap side condition from [Hlau]; the bound is the model's [auxv_count],
   not the ten entries this file used to assume.  [wmem]/[rdn_wmem_stack] are
   gone: [rdn_wrap_stack_above] is the one step, as UDrvMain uses it. *)
#[using="mbase entry brk tid regs Hsp Hvl Hlau ME"] Lemma hi_auxv_w : forall j, (j < 2 * auxv_count RSQ)%nat ->
  rdn PSEGS mem (wa (AUXV + 8 * Z.of_nat j)) 8 = Some (word_le8 (nth j AUXW (Z_to_bv 64 0))).
Proof. LiaFast.lf_pins (fun (mbase entry brk tid regs Hsp Hvl Hlau ME : LiaFast.U) => LiaFast.u0).
  intros j Hj. pose proof his_sp as (L & H & _). pose proof his_block as B. pose proof his_auxv_off as AO.
  assert (Hc : Z.of_nat (auxv_size RSQ) = 16 * Z.of_nat (auxv_count RSQ)) by (unfold auxv_size; lia).
  assert (U : bv_unsigned (wa (AUXV + 8 * Z.of_nat j)) = AUXV + 8 * Z.of_nat j)
    by (unfold wa; apply u_small64; unfold two64; lia).
  rewrite (main_entry_rdn_above _ _ _ _ _ _ _ _ ME) by (rewrite U; lia).
  rewrite rdn_wrap_stack_above by (rewrite U; lia).
  pose proof (read_auxv_word PSEGS Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau
                ltac:(unfold sp_window_hi; lia) j Hj) as R.
  rewrite word_add_nat in R. unfold wa. rewrite <- R. do 2 f_equal. lia.
Qed.

#[using="mbase entry brk tid regs Hsp Hva Hve Hvl Hlau ME"] Lemma hi_rnd : RND mod 8 = 0 /\ bv_unsigned sp0 + Z.of_nat (auxv_off av ev) + 160 <= RND /\ RND + 16 <= 2 ^ 47 /\
  rdn PSEGS mem (wa (RND + 8)) 8 = Some (firstn 8 (skipn 8 (at_random_bytes (ed_random rdraw)))).
Proof. LiaFast.lf_pins (fun (mbase entry brk tid regs Hsp Hva Hve Hvl Hlau ME : LiaFast.U) => LiaFast.u0).
  pose proof his_sp as (L & H & Al). pose proof his_block as B. pose proof his_rnd_lo as RL.
  pose proof his_head_le as HB. pose proof his_rnd_eq as RE.
  destruct (rnd_facts PSEGS Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau
              ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) Al)
    as (R1 & R2 & R3 & R4 & R5).
  split; [exact R4|]. split; [lia|]. split; [lia|].
  assert (U : bv_unsigned (wa (RND + 8)) = RND + 8) by (unfold wa; apply u_small64; unfold two64; lia).
  rewrite (main_entry_rdn_above _ _ _ _ _ _ _ _ ME) by (rewrite U; lia).
  rewrite rdn_wrap_stack_above by (rewrite U; lia).
  exact (R5 8%nat 8%nat ltac:(lia)).
Qed.

(* [comment removed for export] *)
Definition SEC : Z := lez (firstn 8 (skipn 8 (at_random_bytes (ed_random rdraw)))).
#[using="Type"] Lemma his_sec : word_to_le_bytes 8 (wa SEC) = firstn 8 (skipn 8 (at_random_bytes (ed_random rdraw))).
Proof. LiaFast.lf_pins LiaFast.u0.
  assert (HL : length (firstn 8 (skipn 8 (at_random_bytes (ed_random rdraw)))) = 8%nat) by reflexivity.
  pose proof (lez_bound_len _ 8 HL) as B. unfold word_to_le_bytes, SEC, wa. rewrite u_small64 by (unfold two64; lia).
  rewrite <- HL at 1. apply Z_to_le_bytes_lez.
Qed.

(* [comment removed for export] *)
#[using="mbase entry brk tid regs Hsp Hvl Hlau ME"] Lemma hi_auxv_types : forall i, (i < length (TYPS RSQ))%nat ->
  rdn PSEGS mem (wa (AUXV + 16 * Z.of_nat i)) 8 = Some (word_to_le_bytes 8 (wa (nth i (TYPS RSQ) 0))).
Proof. LiaFast.lf_pins (fun (mbase entry brk tid regs Hsp Hvl Hlau ME : LiaFast.U) => LiaFast.u0).
  intros i Hi.
  assert (Hb : (2 * i < 2 * auxv_count RSQ)%nat) by (pose proof (TYPS_len RSQ); lia).
  pose proof (hi_auxv_w (2 * i) Hb) as R.
  replace (8 * Z.of_nat (2 * i)) with (16 * Z.of_nat i) in R by lia.
  rewrite R, n_to_le_8_spec. do 2 f_equal.
  revert Hi. unfold auxv_words, auxv_entries, TYPS. cbn [launch_auxv la_rseq].
  (* MEASURED CURE, 2026-11-07.  Byte-identical twin of PHeapInst.v's runaway
     (see the note there).  `repeat (destruct i as [|i]; [...|])` has no fixed point: past
     the table both sides are the nth DEFAULT, so `reflexivity` closes the out-of-range
     branch and `repeat` peels S forever.  TYPS is 26 ++ (if rseq then [27;28] else [])
     (PHeapTyps.v:33-35) = 28 and 26, confirmed verbatim by a goal
     print.  Bounded iteration terminates by construction; the
     STATEMENT is unchanged to the character and no lemma is added. *)
  destruct (kb_rseq (in_kernel inp)); cbn [app length];
    [ do 28 (destruct i as [|i]; [intros _; reflexivity|])
    | do 26 (destruct i as [|i]; [intros _; reflexivity|]) ];
    intros Hc; lia.
Qed.

(* AT_RANDOM is the twenty-fifth entry of the model's table (index 24), so its
   value is auxv word 49; the rseq pair is above it, so no case split is needed. *)
#[using="mbase entry brk tid regs Hsp Hvl Hlau ME"] Lemma hi_auxv_rnd : rdn PSEGS mem (wa (AUXV + 16 * Z.of_nat 24 + 8)) 8 = Some (word_to_le_bytes 8 (wa RND)).
Proof. LiaFast.lf_pins (fun (mbase entry brk tid regs Hsp Hvl Hlau ME : LiaFast.U) => LiaFast.u0).
  pose proof (hi_auxv_w 49 ltac:(unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia)) as R.
  replace (AUXV + 8 * Z.of_nat 49) with (AUXV + 16 * Z.of_nat 24 + 8) in R by lia.
  rewrite R, n_to_le_8_spec. unfold wa. rewrite Z_to_bv_bv_unsigned.
  unfold auxv_words, auxv_entries. cbn [launch_auxv la_rseq]. reflexivity.
Qed.

#[using="mbase entry brk tid regs Hsp Hvl Hlau ME"] Lemma hi_auxv_null :
  rdn PSEGS mem (wa (AUXV + 16 * Z.of_nat (length (TYPS RSQ)))) 8 = Some (word_to_le_bytes 8 (wa 0)).
Proof. LiaFast.lf_pins (fun (mbase entry brk tid regs Hsp Hvl Hlau ME : LiaFast.U) => LiaFast.u0).
  assert (Hb : (2 * length (TYPS RSQ) < 2 * auxv_count RSQ)%nat) by (pose proof (TYPS_len RSQ); lia).
  pose proof (hi_auxv_w (2 * length (TYPS RSQ)) Hb) as R.
  replace (8 * Z.of_nat (2 * length (TYPS RSQ))) with (16 * Z.of_nat (length (TYPS RSQ))) in R by lia.
  rewrite R, n_to_le_8_spec. do 2 f_equal.
  unfold auxv_words, auxv_entries, TYPS. cbn [launch_auxv la_rseq].
  destruct (kb_rseq (in_kernel inp)); cbn [app length]; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="inp mbase entry sp0 tid rdraw regs Hsp ME"] Lemma hi_env : env mem (bv_unsigned (canary rdraw)).
Proof. LiaFast.lf_pins (fun (inp mbase entry sp0 tid rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0).
  pose proof his_sp as (L & _). destruct tables_img_ok as [T1 T2]. rewrite forallb_forall in T1, T2.
  split; [exact (hi_need_locks inp mbase entry sp0 tid rdraw regs mem Hsp ME)|].
  split.
  { intros sc Hsc. rewrite (hi_tables inp mbase entry sp0 tid rdraw regs mem Hsp ME) by lia.
    apply opt_bytes_eqb_eq. specialize (T1 (Z.to_nat sc) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in T1 by lia. exact T1. }
  split.
  { intros j Hj. rewrite (hi_tables inp mbase entry sp0 tid rdraw regs mem Hsp ME) by lia.
    apply opt_bytes_eqb_eq. specialize (T2 (Z.to_nat j) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in T2 by lia. exact T2. }
  split; [exact (hi_can_range rdraw)|].
  split; [exact (hi_got_guard inp mbase entry sp0 tid rdraw regs mem Hsp ME)|].
  split; [exact (hi_canary inp mbase entry sp0 tid rdraw regs mem Hsp ME)|].
  split; [exact (hi_lock inp mbase entry sp0 tid rdraw regs mem Hsp ME)|].
  split; [intros j Hj; exact (hi_errno_rd inp mbase entry sp0 tid rdraw regs mem Hsp ME j Hj)|].
  intros d k Hd Hk. apply store_ok_of_all; [unfold wa; rewrite u_small64 by (unfold two64, ERRNO; lia); unfold ERRNO; lia|].
  intros x Hx. unfold wa, ERRNO in Hx. rewrite u_small64 in Hx by (unfold two64; lia).
  destruct (hi_errno_pristine inp mbase entry sp0 tid rdraw regs mem Hsp ME) as (_ & _ & HP).
  assert (Hxe : x = wa (bv_unsigned x)) by (unfold wa; rewrite Z_to_bv_bv_unsigned; reflexivity).
  rewrite wview_none by (rewrite Hxe; apply HP; lia).
  pose proof errno_img_w as W. rewrite forallb_forall in W. specialize (W (Z.to_nat (bv_unsigned x - 0x778ec)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in W by lia. replace (0x778ec + (bv_unsigned x - 0x778ec)) with (bv_unsigned x) in W by lia. rewrite <- Hxe in W.
  destruct (wview PSEGS (fun _ => None) x); [discriminate | discriminate W].
Qed.

#[using="inp mbase entry sp0 tid rdraw regs Hsp ME"] Lemma hi_ctx_zero : forall x, 0x97c98 <= x < 0x98038 -> bview PSEGS mem x = Some 0.
Proof. LiaFast.lf_pins (fun (inp mbase entry sp0 tid rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0).
  intros x Hx. destruct (hi_ctx inp mbase entry sp0 tid rdraw regs mem Hsp ME) as (_ & _ & HP).
  rewrite bview_none by (apply HP; lia).
  pose proof ctx_img_zero as C. rewrite forallb_forall in C. specialize (C (Z.to_nat (x - 0x97c98)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in C by lia. replace (0x97c98 + (x - 0x97c98)) with x in C by lia.
  destruct (bview PSEGS (fun _ => None) x) as [[|z|z]|]; try discriminate; reflexivity.
Qed.

(* [b] rather than [brk]: [brk] is a section variable now. *)
Definition LY (b : word) : layout := Layout 0x97c98 (fun _ => 0) (bv_unsigned b) SEC.

(* The auxv table ends inside the head block, which ends inside the image. *)
#[using="mbase entry brk Hlau"] Lemma his_auxv_top : AUXV + 16 * Z.of_nat (length (TYPS RSQ)) + 8 <= 2 ^ 47.
Proof. LiaFast.lf_pins (fun (mbase entry brk Hlau : LiaFast.U) => LiaFast.u0).
  pose proof his_block as B. pose proof his_head_le as HB. pose proof (TYPS_len RSQ) as TL.
  assert (Hc : Z.of_nat (auxv_size RSQ) = 16 * Z.of_nat (auxv_count RSQ)) by (unfold auxv_size; lia).
  unfold auxv_off, block_head_size, block_items in *. cbv zeta in *. lia.
Qed.

#[using="mbase entry brk tid regs Hsp Hva Hve Hvl Hlau ME"] Lemma hi_init_env : forall b, init_env (LY b) mem AUXV RND (TYPS RSQ).
Proof. LiaFast.lf_pins (fun (mbase entry brk tid regs Hsp Hva Hve Hvl Hlau ME : LiaFast.U) => LiaFast.u0).
  intros b. pose proof his_sp as (L & H & Al). pose proof his_block as B. pose proof his_auxv_off as AO.
  pose proof his_rnd_lo as RL. pose proof his_auxv_top as AT.
  destruct hi_rnd as (R1 & R2 & R3 & R4).
  split; [exact hi_auxv_ptr|].
  split; [unfold auxv_off, block_items; lia|].
  split; [clear - Al; unfold auxv_off, block_items; lia|].
  split; [exact AT|].
  split.
  { intros i Hi. split; [exact (TYPS_pos _ i Hi)|].
    split; [exact (hi_auxv_types i Hi)|].
    intros E25. rewrite (TYPS_rnd_idx _ i E25 Hi). exact hi_auxv_rnd. }
  split; [exact hi_auxv_null|].
  split; [exact (TYPS_rnd RSQ)|].
  split; [lia|]. split; [exact R1|]. split; [exact R3|].
  rewrite R4. f_equal. cbn [LY ly_sec]. symmetry. exact his_sec.
Qed.

(* [comment removed for export] *)
#[using="mbase entry brk tid regs Hsp Hva Hve Hvl Hlau ME"] Theorem heapI_main : forall lim, valid_brk PSEGS brk -> valid_mmap_base mbase -> 2 ^ 31 <= lim ->
  exists hs, HeapI (bv_unsigned sp0 - stack_max_size) hs mem (with_tid tid (init_model (segments_reserved PSEGS) brk mbase sp0 lim inp)) /\
    INITO inp sp0 rdraw (HI (bv_unsigned sp0 - stack_max_size)) INIT hs.
Proof. LiaFast.lf_pins (fun (mbase entry brk tid regs Hsp Hva Hve Hvl Hlau ME : LiaFast.U) => LiaFast.u0).
  intros lim Hbrk Hmb Hlim. pose proof his_sp as (L & H & Al). pose proof his_block as B. pose proof his_auxv_off as AO.
  destruct hi_rnd as (R1 & R2 & R3 & _). pose proof his_rnd_lo as RL. pose proof his_auxv_top as AT.
  pose proof his_head_le as HB. pose proof his_rnd_eq as RE.
  set (HTOP := bv_unsigned sp0 - stack_max_size).
  set (md := with_tid tid (init_model (segments_reserved PSEGS) brk mbase sp0 lim inp)).
  assert (RT : reserved_top (segments_reserved PSEGS) = 0x99000) by (vm_compute; reflexivity).
  destruct Hbrk as (B1 & B2 & B3). rewrite RT in B1, B2. unfold brk_aslr_max in B2. unfold page_size in B3.
  assert (HLK : MngRz2.LINK HTOP FORB_P (LY brk) (MallocWfKf.kf_of init_state) md).
  { apply LINK_init.
    - unfold md. rewrite m_halted_with_tid, m_halted_init_model. reflexivity.
    - reflexivity.
    - change (m_vmmaps md) with (mkVmMapsFull (init_reserved (segments_reserved PSEGS) mbase sp0 (in_kernel inp)) [] [] brk brk lim mbase sp0). reflexivity.
    - change (m_vmmaps md) with (mkVmMapsFull (init_reserved (segments_reserved PSEGS) mbase sp0 (in_kernel inp)) [] [] brk brk lim mbase sp0). unfold alloc_top. cbn [vm_init_sp]. lia.
    - (* LPS 08b1429: the launch ledger is the image's segments plus the kernel's vDSO/vvar pair *)
      exact (vm_reserved_init_model (segments_reserved PSEGS) brk mbase sp0 lim inp).
    - reflexivity.
    - change (m_vmmaps md) with (mkVmMapsFull (init_reserved (segments_reserved PSEGS) mbase sp0 (in_kernel inp)) [] [] brk brk lim mbase sp0). reflexivity.
    - cbn [LY ly_brk0]. unfold PGSZ. lia.
    - cbn [LY ly_brk0]. unfold PGSZ. exact B3.
    - change (m_vmmaps md) with (mkVmMapsFull (init_reserved (segments_reserved PSEGS) mbase sp0 (in_kernel inp)) [] [] brk brk lim mbase sp0). unfold Mmap.min_brk. cbn. lia.
    - cbn [LY ly_brk0]. unfold HTOP, stack_max_size. lia.
    - change (m_vmmaps md) with (mkVmMapsFull (init_reserved (segments_reserved PSEGS) mbase sp0 (in_kernel inp)) [] [] brk brk lim mbase sp0). reflexivity.
    - change (m_vmmaps md) with (mkVmMapsFull (init_reserved (segments_reserved PSEGS) mbase sp0 (in_kernel inp)) [] [] brk brk lim mbase sp0). unfold alloc_top. cbn [vm_init_sp].
      unfold stack_max_size in *. lia.
    - change (m_vmmaps md) with (mkVmMapsFull (init_reserved (segments_reserved PSEGS) mbase sp0 (in_kernel inp)) [] [] brk brk lim mbase sp0). cbn. lia. }
  destruct (heap_initI HTOP (LY brk) (bv_unsigned (canary rdraw)) AUXV RND (TYPS RSQ) mem md eq_refl ltac:(unfold HTOP, stack_max_size; lia)
              hi_env (hi_kro inp mbase entry sp0 tid rdraw regs mem Hsp ME) hi_page (hi_init_env brk) ltac:(lia) ltac:(lia) HLK hi_ctx_zero)
    as (hs0 & HQ & _ & _ & _ & _ & Ha & Hr & Ht).
  exists hs0. split; [exact HQ|].
  intros x Hx. unfold INIT in Hx. rewrite Ha, Hr, Ht in Hx. cbn [ioutside] in Hx.
  assert (HX : AUXV <= x < AUXV + 16 * Z.of_nat (length (TYPS RSQ)) + 8 \/ RND + 8 <= x < RND + 16) by lia. clear Hx.
  split; [unfold auxv_off, block_items in *; lia|].
  pose proof Hva as [[LA _] _].
  destruct (Nat.eq_dec (length av) 1) as [E1|E1].
  - (* [comment removed for export] *)
    right. unfold cat_argv_ptr. rewrite nth_overflow by (rewrite length_string_addrs_fst; lia). rewrite (nth_overflow av) by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0. cbn [length]. unfold auxv_off, block_items in *. lia.
  - (* LPS 08b1429: the argv strings now sit ABOVE the head block, so both of the
       windows [INIT] names are below [p1] and the disjunct is always the left one. *)
    left.
    pose proof (u_PA inp mbase entry sp0 brk rdraw Hlau 1 ltac:(lia)) as U1.
    pose proof (total_arg_bytes_firstn_le 1 av) as T1.
    pose proof (TYPS_len RSQ) as TL.
    assert (Hc : Z.of_nat (auxv_size RSQ) = 16 * Z.of_nat (auxv_count RSQ)) by (unfold auxv_size; lia).
    unfold cat_string_off in U1.
    unfold auxv_off, block_head_size, block_items in *. cbv zeta in *. lia.
Qed.

End HIS.
