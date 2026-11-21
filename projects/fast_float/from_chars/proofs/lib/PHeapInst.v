(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput; the launch premises valid_launch and entry_launch_ok_va; the launch's reservations with the vDSO pair; the CONFIG_RSEQ flag of the start-up layer; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec StoreOk CatExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout MemSplit RefMemcpyLib FxLin FxMem.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout OSSVerify.Proofs.fast_float.from_chars.lib.Common.MemSplit OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Image.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface HIfaceInit.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import RefStartup RefStartupDefs PDrvData PDrvMain PHeapInit PHeapIGlue.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfKf.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxMalloc MngRepr MngL4 MngL4I.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngRz2.
(* SPLIT (G2FfPHeapSentence, 2026-11-06).  The nine top-level sentences that used
   to sit here are now four separate compilation units.  The reason is measured,
   not stylistic: the cost of this file was SUPERADDITIVE ACROSS SENTENCES.  Each
   sentence is cheap alone -- tables_img_ok 3.88 GiB,
   the chunk-split ctx_img_zero 4.22 GiB, each
   figure INCLUDING the shared dependency cone -- yet the same sentences together
   in one file, with the section removed entirely and nothing else present, passed
   13.27 GiB and were still climbing, and the whole
   file was OOM-killed at 48.00 GiB, as was the
   whole file WITHOUT heapI_main.  All on image
   2c6b6db8, all kernel peak, the same instrument throughout.
   Four named suspects are each refuted by its own measurement:
   heapI_main, ctx_img_zero, tables_img_ok, and kernel conversion over
   PSEGS.  There is no runaway sentence; a compilation unit frees its heap and a
   sentence does not, so the division has to be into FILES.
   Every statement moved is byte-identical to the text it moved from. *)
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PHeapTyps PHeapImgTab PHeapImgCtx PHeapImgErr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Open Scope Z_scope.

Local Ltac bvlit := vm_compute; try (f_equal; repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]); try reflexivity).

Section HIS.
(* LPS 08b1429: the section takes the launch ([inp], [mbase], [entry], [brk], with
   [Hvl] and [Hlau]) instead of argv/envp/uid/hwcap, as PDrvMain's Handoff section
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

(* The auxv is at least 432 bytes ([PDrvMain.auxv_size_ge432], the only auxv-size
   fact), so the random bytes sit well above the auxv's own first word. *)
#[using="mbase entry brk Hlau Hsp"] Lemma his_rnd_lo : bv_unsigned sp0 + Z.of_nat (auxv_off av ev) + 432 <= RND.
Proof. LiaFast.lf_pins (fun (mbase entry brk Hlau Hsp : LiaFast.U) => LiaFast.u0).
  pose proof his_rnd_eq as E. pose proof (auxv_size_ge432 RSQ) as A.
  rewrite E. unfold auxv_off, block_head_size, block_items. cbv zeta. lia.
Qed.

(* [comment removed for export] *)
#[using="inp mbase entry sp0 tid rdraw regs Hsp ME"] Lemma hi_page : rdn PSEGS mem (wa 614032) 8 = Some (word_to_le_bytes 8 (wa 4096)).
Proof. LiaFast.lf_pins (fun (inp mbase entry sp0 tid rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0).
  pose proof his_sp as (L & _).
  rewrite (main_entry_rdn_data _ _ _ _ _ _ _ _ ME) by (unfold wa; rewrite u_small64 by (unfold two64; lia); unfold stack_max_size; lia).
  reflexivity.
Qed.

#[using="inp mbase entry sp0 tid rdraw regs Hsp ME"] Lemma hi_auxv_ptr : rdn PSEGS mem (wa 613992) 8 = Some (word_to_le_bytes 8 (wa AUXV)).
Proof. LiaFast.lf_pins (fun (inp mbase entry sp0 tid rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0).
  pose proof his_sp as (L & _).
  rewrite (main_entry_rdn_data _ _ _ _ _ _ _ _ ME) by (unfold wa; rewrite u_small64 by (unfold two64; lia); unfold stack_max_size; lia).
  transitivity (Some (word_to_le_bytes 8 (auxv_w inp sp0))); [reflexivity|].
  unfold auxv_w, wa, auxv_off. do 3 f_equal. lia.
Qed.

(* LPS 08b1429: [read_auxv_word] reads the launch's own auxv and derives its
   no-wrap side condition from [Hlau]; the bound is the model's [auxv_count],
   not the ten entries this file used to assume.  [wmem]/[rdn_wmem_stack] are
   gone: [rdn_wrap_stack_above] is the one step, as PDrvMain.v:295 uses it. *)
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
  (* MEASURED CURE, 2026-11-07.  `repeat (destruct i as [|i]; [...|])` has NO
     FIXED POINT here, the third instance of the class TYPS_pos and TYPS_rnd_idx carried:
     past the end of the table BOTH sides are the nth DEFAULT, so the bracket's `reflexivity`
     closes the out-of-range branch too and `repeat` peels S forever, never reaching the
     trailing `lia`.  (TYPS_pos failed by `lia` closing it, TYPS_rnd_idx by `discriminate`
     closing 0 = 25 -- three closing tactics, one shape.)  This is why PHeapInst.vo and its
     UHeapInst.v twin do not compile at #38 in the old form, and why four builds died
     at 64.00/64.00/96/32 GiB: a runaway exhausts any ceiling, so four caps are ONE reading.
     THE BOUND IS KNOWN, so the fix is to bound the iteration rather than to restate anything:
     TYPS is 26 entries ++ (if rseq then [27;28] else []) (PHeapTyps.v:33-35), i.e. 28 and 26,
     confirmed verbatim by a goal print ("(i < 28)%nat" and
     "(i < 26)%nat").  `do N` terminates by construction and leaves exactly the out-of-range
     hypothesis the trailing `lia` was always meant to close.  The STATEMENT is unchanged to
     the character and no lemma is added. *)
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
  pose proof errno_img_w as W. rewrite forallb_forall in W. specialize (W (Z.to_nat (bv_unsigned x - 0x75b2c)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in W by lia. replace (0x75b2c + (bv_unsigned x - 0x75b2c)) with (bv_unsigned x) in W by lia. rewrite <- Hxe in W.
  destruct (wview PSEGS (fun _ => None) x); [discriminate | discriminate W].
Qed.

#[using="inp mbase entry sp0 tid rdraw regs Hsp ME"] Lemma hi_ctx_zero : forall x, 0x95ed8 <= x < 0x96278 -> bview PSEGS mem x = Some 0.
Proof. LiaFast.lf_pins (fun (inp mbase entry sp0 tid rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0).
  intros x Hx. destruct (hi_ctx inp mbase entry sp0 tid rdraw regs mem Hsp ME) as (_ & _ & HP).
  rewrite bview_none by (apply HP; lia).
  pose proof ctx_img_zero as C. rewrite forallb_forall in C. specialize (C (Z.to_nat (x - 0x95ed8)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in C by lia. replace (0x95ed8 + (x - 0x95ed8)) with x in C by lia.
  destruct (bview PSEGS (fun _ => None) x) as [[|z|z]|]; try discriminate; reflexivity.
Qed.

(* [b] rather than [brk]: [brk] is a section variable now. *)
Definition LY (b : word) : layout := Layout 0x95ed8 (fun _ => 0) (bv_unsigned b) SEC.

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
  assert (RT : reserved_top (segments_reserved PSEGS) = 0x97000) by (vm_compute; reflexivity).
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
