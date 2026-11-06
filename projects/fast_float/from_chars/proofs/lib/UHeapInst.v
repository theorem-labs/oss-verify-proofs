(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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

(* [comment removed for export] *)
Definition TYPS : list Z := [3; 4; 5; 16; 6; 11; 12; 23; 25].

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

Lemma tables_img_ok :
  forallb (fun sc => opt_bytes_eqb (rdn PSEGS (fun _ => None) (wa (98984 + 2 * Z.of_nat sc)) 2)
                                   (Some (word_to_le_bytes 2 (wa (znth (Z.of_nat sc) size_classes))))) (seq 0 48) = true /\
  forallb (fun j => opt_bytes_eqb (rdn PSEGS (fun _ => None) (wa (98952 + Z.of_nat j)) 1)
                                  (Some (word_to_le_bytes 1 (wa (znth (Z.of_nat j) debruijn))))) (seq 0 32) = true.
Proof. split; vm_compute; reflexivity. Qed.

Lemma ctx_img_zero : forallb (fun i => match bview PSEGS (fun _ => None) (0x97c98 + Z.of_nat i) with Some 0 => true | _ => false end) (seq 0 928) = true.
Proof. vm_compute. reflexivity. Qed.

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
Variable sp0 : word.
Variables av ev : list (list byte).
Variables uid tid hw : word.
Variable rdraw : EntryDraw.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Hypothesis Hsp : valid_sp sp0.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hfits : entry_stack_fits sp0 av ev.
Hypothesis ME : main_entry sp0 av ev uid tid hw rdraw regs mem.

Local Notation AUXV := (bv_unsigned sp0 + Z.of_nat (auxv_off av ev)).
Local Notation RND := (bv_unsigned (at_random_ptr sp0 av ev)).
Local Notation bsb := (build_stack_bytes RPH sp0 av ev uid hw rdraw).

#[using="Hsp"] Lemma his_sp : 0x7fff80000000 <= bv_unsigned sp0 /\ bv_unsigned sp0 <= 0x800000000000 /\ bv_unsigned sp0 mod 16 = 0.
Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0). destruct Hsp as (A & B & C). unfold sp_window_lo, sp_window_hi in *. lia. Qed.

#[using="Hfits"] Lemma his_block : bv_unsigned sp0 + Z.of_nat (length bsb) <= 2 ^ 47.
Proof. LiaFast.lf_pins (fun (Hfits : LiaFast.U) => LiaFast.u0).
  pose proof (build_stack_bytes_within_span RPH sp0 av ev uid hw rdraw) as H. unfold entry_stack_fits, sp_window_hi in Hfits. lia.
Qed.

#[using="Type"] Lemma his_auxv_off : Z.of_nat (auxv_off av ev) + 160 + 16 <= Z.of_nat (length bsb).
Proof. LiaFast.lf_pins LiaFast.u0. pose proof (auxv_off_bound RPH sp0 rdraw av ev uid hw) as H. lia. Qed.

(* [comment removed for export] *)
#[using="sp0 av ev uid tid hw rdraw regs Hsp ME"] Lemma hi_page : rdn PSEGS mem (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096)).
Proof. LiaFast.lf_pins (fun (sp0 av ev uid tid hw rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0).
  pose proof his_sp as (L & _).
  rewrite (main_entry_rdn_data sp0 av ev uid tid hw rdraw regs mem ME) by (unfold wa; rewrite u_small64 by (unfold two64; lia); unfold stack_max_size; lia).
  reflexivity.
Qed.

#[using="uid tid hw rdraw regs Hsp ME"] Lemma hi_auxv_ptr : rdn PSEGS mem (wa 621608) 8 = Some (word_to_le_bytes 8 (wa AUXV)).
Proof. LiaFast.lf_pins (fun (uid tid hw rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0).
  pose proof his_sp as (L & _).
  rewrite (main_entry_rdn_data sp0 av ev uid tid hw rdraw regs mem ME) by (unfold wa; rewrite u_small64 by (unfold two64; lia); unfold stack_max_size; lia).
  transitivity (Some (word_to_le_bytes 8 (auxv_w sp0 av ev))); [reflexivity|].
  unfold auxv_w, wa, auxv_off. do 3 f_equal. lia.
Qed.

(* [comment removed for export] *)
#[using="tid rdraw regs Hsp Hva Hve Hfits ME"] Lemma hi_auxv_w : forall j, (j < 20)%nat ->
  rdn PSEGS mem (wa (AUXV + 8 * Z.of_nat j)) 8 = Some (word_le8 (nth j (auxv_words RPH (at_random_ptr sp0 av ev) uid hw) (Z_to_bv 64 0))).
Proof. LiaFast.lf_pins (fun (tid rdraw regs Hsp Hva Hve Hfits ME : LiaFast.U) => LiaFast.u0).
  intros j Hj. pose proof his_sp as (L & H & _). pose proof his_block as B. pose proof his_auxv_off as AO.
  assert (U : bv_unsigned (wa (AUXV + 8 * Z.of_nat j)) = AUXV + 8 * Z.of_nat j) by (unfold wa; apply u_small64; unfold two64; lia).
  rewrite (main_entry_rdn_above sp0 av ev uid tid hw rdraw regs mem ME) by (rewrite U; lia).
  change (wrap_mem RPH sp0 av ev uid hw rdraw) with (wmem RPH sp0 av ev uid hw rdraw).
  rewrite (rdn_wmem_stack PSEGS RPH sp0 av ev uid hw rdraw) by (rewrite U; lia).
  pose proof (read_auxv_word PSEGS RPH sp0 rdraw av ev uid hw Hva Hve ltac:(unfold sp_window_hi; lia) j Hj) as R.
  rewrite word_add_nat in R. unfold wa. rewrite <- R. do 2 f_equal. lia.
Qed.

(* [comment removed for export] *)
#[using="uid hw rdraw Hsp Hva Hve"] Lemma his_rnd_lo : bv_unsigned sp0 + Z.of_nat (cat_struct_size av ev) + Z.of_nat (total_arg_bytes_nat av) <= RND.
Proof. LiaFast.lf_pins (fun (uid hw rdraw Hsp Hva Hve : LiaFast.U) => LiaFast.u0).
  pose proof his_sp as (L & H & _). pose proof (bsb_bound RPH sp0 av ev uid hw rdraw Hva Hve) as BB.
  pose proof (build_stack_bytes_within_span RPH sp0 av ev uid hw rdraw) as SP.
  unfold at_random_ptr. cbv zeta. rewrite word_add_nat.
  rewrite !length_flatten_strings.
  set (len := (8 + (length av + 1) * 8 + (length ev + 1) * 8 + auxv_size + total_arg_bytes_nat av + total_arg_bytes_nat ev)%nat).
  set (pad := Z.to_nat ((8 - Z.of_nat len mod 8) mod 8)).
  assert (Hpad : (pad <= 7)%nat).
  { unfold pad. pose proof (Z.mod_pos_bound (8 - Z.of_nat len mod 8) 8 ltac:(lia)). lia. }
  assert (Hlen : Z.of_nat len <= 2240000).
  { unfold len. pose proof Hva as [[Hl0 Hl] [Hta _]]. pose proof Hve as [Hle [Hte _]]. rewrite total_arg_bytes_Z in Hta, Hte. unfold auxv_size. lia. }
  rewrite u_small64 by (unfold two64; lia).
  unfold cat_struct_size, len. lia.
Qed.

#[using="uid tid hw regs Hsp Hva Hve Hfits ME"] Lemma hi_rnd : RND mod 8 = 0 /\ bv_unsigned sp0 + Z.of_nat (auxv_off av ev) + 160 <= RND /\ RND + 16 <= 2 ^ 47 /\
  rdn PSEGS mem (wa (RND + 8)) 8 = Some (firstn 8 (skipn 8 (at_random_bytes (ed_random rdraw)))).
Proof. LiaFast.lf_pins (fun (uid tid hw regs Hsp Hva Hve Hfits ME : LiaFast.U) => LiaFast.u0).
  pose proof his_sp as (L & H & Al). pose proof his_block as B. pose proof his_rnd_lo as RL.
  destruct (rnd_facts PSEGS RPH sp0 rdraw av ev uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) Al)
    as (R1 & R2 & R3 & R4 & R5).
  split; [exact R4|]. split; [clear - RL; unfold cat_struct_size, auxv_off, auxv_size in *; lia|]. split; [lia|].
  assert (U : bv_unsigned (wa (RND + 8)) = RND + 8) by (unfold wa; apply u_small64; unfold two64; lia).
  rewrite (main_entry_rdn_above sp0 av ev uid tid hw rdraw regs mem ME) by (rewrite U; lia).
  change (wrap_mem RPH sp0 av ev uid hw rdraw) with (wmem RPH sp0 av ev uid hw rdraw).
  rewrite (rdn_wmem_stack PSEGS RPH sp0 av ev uid hw rdraw) by (rewrite U; lia).
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
#[using="uid tid hw rdraw regs Hsp Hva Hve Hfits ME"] Lemma hi_auxv_types : forall i, (i < 9)%nat ->
  rdn PSEGS mem (wa (AUXV + 16 * Z.of_nat i)) 8 = Some (word_to_le_bytes 8 (wa (nth i TYPS 0))).
Proof. LiaFast.lf_pins (fun (uid tid hw rdraw regs Hsp Hva Hve Hfits ME : LiaFast.U) => LiaFast.u0).
  intros i Hi. pose proof (hi_auxv_w (2 * i) ltac:(lia)) as R. replace (8 * Z.of_nat (2 * i)) with (16 * Z.of_nat i) in R by lia.
  rewrite R. rewrite n_to_le_8_spec. do 2 f_equal.
  rewrite (auxv_words_eq RPH uid hw (at_random_ptr sp0 av ev)).
  destruct i as [|[|[|[|[|[|[|[|[|i]]]]]]]]]; try lia; reflexivity.
Qed.
#[using="uid tid hw rdraw regs Hsp Hva Hve Hfits ME"] Lemma hi_auxv_rnd : rdn PSEGS mem (wa (AUXV + 16 * 8 + 8)) 8 = Some (word_to_le_bytes 8 (wa RND)).
Proof. LiaFast.lf_pins (fun (uid tid hw rdraw regs Hsp Hva Hve Hfits ME : LiaFast.U) => LiaFast.u0).
  pose proof (hi_auxv_w 17 ltac:(lia)) as R. replace (AUXV + 8 * Z.of_nat 17) with (AUXV + 16 * 8 + 8) in R by lia.
  rewrite R. rewrite n_to_le_8_spec. unfold wa. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
#[using="uid tid hw rdraw regs Hsp Hva Hve Hfits ME"] Lemma hi_auxv_null : rdn PSEGS mem (wa (AUXV + 16 * 9)) 8 = Some (word_to_le_bytes 8 (wa 0)).
Proof. LiaFast.lf_pins (fun (uid tid hw rdraw regs Hsp Hva Hve Hfits ME : LiaFast.U) => LiaFast.u0).
  pose proof (hi_auxv_w 18 ltac:(lia)) as R. replace (8 * Z.of_nat 18) with (16 * 9) in R by lia.
  rewrite R. rewrite n_to_le_8_spec. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="sp0 av ev uid tid hw regs Hsp ME"] Lemma hi_env : env mem (bv_unsigned (canary rdraw)).
Proof. LiaFast.lf_pins (fun (sp0 av ev uid tid hw regs Hsp ME : LiaFast.U) => LiaFast.u0).
  pose proof his_sp as (L & _). destruct tables_img_ok as [T1 T2]. rewrite forallb_forall in T1, T2.
  split; [exact (hi_need_locks sp0 av ev uid tid hw rdraw regs mem Hsp ME)|].
  split.
  { intros sc Hsc. rewrite (hi_tables sp0 av ev uid tid hw rdraw regs mem Hsp ME) by lia.
    apply opt_bytes_eqb_eq. specialize (T1 (Z.to_nat sc) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in T1 by lia. exact T1. }
  split.
  { intros j Hj. rewrite (hi_tables sp0 av ev uid tid hw rdraw regs mem Hsp ME) by lia.
    apply opt_bytes_eqb_eq. specialize (T2 (Z.to_nat j) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in T2 by lia. exact T2. }
  split; [exact (hi_can_range rdraw)|].
  split; [exact (hi_got_guard sp0 av ev uid tid hw rdraw regs mem Hsp ME)|].
  split; [exact (hi_canary sp0 av ev uid tid hw rdraw regs mem Hsp ME)|].
  split; [exact (hi_lock sp0 av ev uid tid hw rdraw regs mem Hsp ME)|].
  split; [intros j Hj; exact (hi_errno_rd sp0 av ev uid tid hw rdraw regs mem Hsp ME j Hj)|].
  intros d k Hd Hk. apply store_ok_of_all; [unfold wa; rewrite u_small64 by (unfold two64, ERRNO; lia); unfold ERRNO; lia|].
  intros x Hx. unfold wa, ERRNO in Hx. rewrite u_small64 in Hx by (unfold two64; lia).
  destruct (hi_errno_pristine sp0 av ev uid tid hw rdraw regs mem Hsp ME) as (_ & _ & HP).
  assert (Hxe : x = wa (bv_unsigned x)) by (unfold wa; rewrite Z_to_bv_bv_unsigned; reflexivity).
  rewrite wview_none by (rewrite Hxe; apply HP; lia).
  pose proof errno_img_w as W. rewrite forallb_forall in W. specialize (W (Z.to_nat (bv_unsigned x - 0x778ec)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in W by lia. replace (0x778ec + (bv_unsigned x - 0x778ec)) with (bv_unsigned x) in W by lia. rewrite <- Hxe in W.
  destruct (wview PSEGS (fun _ => None) x); [discriminate | discriminate W].
Qed.

#[using="sp0 av ev uid tid hw rdraw regs Hsp ME"] Lemma hi_ctx_zero : forall x, 0x97c98 <= x < 0x98038 -> bview PSEGS mem x = Some 0.
Proof. LiaFast.lf_pins (fun (sp0 av ev uid tid hw rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0).
  intros x Hx. destruct (hi_ctx sp0 av ev uid tid hw rdraw regs mem Hsp ME) as (_ & _ & HP).
  rewrite bview_none by (apply HP; lia).
  pose proof ctx_img_zero as C. rewrite forallb_forall in C. specialize (C (Z.to_nat (x - 0x97c98)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in C by lia. replace (0x97c98 + (x - 0x97c98)) with x in C by lia.
  destruct (bview PSEGS (fun _ => None) x) as [[|z|z]|]; try discriminate; reflexivity.
Qed.

Definition LY (brk : word) : layout := Layout 0x97c98 (fun _ => 0) (bv_unsigned brk) SEC.

#[using="uid tid hw regs Hsp Hva Hve Hfits ME"] Lemma hi_init_env : forall brk, init_env (LY brk) mem AUXV RND TYPS.
Proof. LiaFast.lf_pins (fun (uid tid hw regs Hsp Hva Hve Hfits ME : LiaFast.U) => LiaFast.u0).
  intros brk. pose proof his_sp as (L & H & Al). pose proof his_block as B. pose proof his_auxv_off as AO.
  destruct hi_rnd as (R1 & R2 & R3 & R4).
  split; [exact hi_auxv_ptr|].
  split; [lia|]. split; [clear - Al; unfold auxv_off; lia|].
  split; [change (Z.of_nat (length TYPS)) with 9; lia|].
  split.
  { intros i Hi. change (length TYPS) with 9%nat in Hi. split.
    - destruct i as [|[|[|[|[|[|[|[|[|i]]]]]]]]]; cbn; lia.
    - split; [exact (hi_auxv_types i Hi)|].
      intros E25. destruct i as [|[|[|[|[|[|[|[|[|i]]]]]]]]]; cbn in E25; try discriminate; [|lia].
      exact hi_auxv_rnd. }
  split; [change (Z.of_nat (length TYPS)) with 9; exact hi_auxv_null|].
  split; [unfold TYPS; repeat (first [apply in_eq | apply in_cons])|].
  split; [lia|]. split; [exact R1|]. split; [exact R3|].
  rewrite R4. f_equal. cbn [LY ly_sec]. symmetry. exact his_sec.
Qed.

(* [comment removed for export] *)
#[using="uid hw rdraw regs Hsp Hva Hve Hfits ME"] Theorem heapI_main : forall brk mbase lim inp, valid_brk PSEGS brk -> valid_mmap_base mbase -> 2 ^ 31 <= lim ->
  exists hs, HeapI (bv_unsigned sp0 - stack_max_size) hs mem (with_tid tid (init_model (segments_reserved PSEGS) brk mbase sp0 lim inp)) /\
    INITO sp0 av ev (HI (bv_unsigned sp0 - stack_max_size)) INIT hs.
Proof. LiaFast.lf_pins (fun (uid hw rdraw regs Hsp Hva Hve Hfits ME : LiaFast.U) => LiaFast.u0).
  intros brk mbase lim inp Hbrk Hmb Hlim. pose proof his_sp as (L & H & Al). pose proof his_block as B. pose proof his_auxv_off as AO.
  destruct hi_rnd as (R1 & R2 & R3 & _). pose proof his_rnd_lo as RL.
  set (HTOP := bv_unsigned sp0 - stack_max_size).
  set (md := with_tid tid (init_model (segments_reserved PSEGS) brk mbase sp0 lim inp)).
  assert (RT : reserved_top (segments_reserved PSEGS) = 0x99000) by (vm_compute; reflexivity).
  destruct Hbrk as (B1 & B2 & B3). rewrite RT in B1, B2. unfold brk_aslr_max in B2. unfold page_size in B3.
  assert (HLK : MngRz2.LINK HTOP FORB_P (LY brk) (MallocWfKf.kf_of init_state) md).
  { apply LINK_init.
    - unfold md. rewrite m_halted_with_tid, m_halted_init_model. reflexivity.
    - reflexivity.
    - change (m_vmmaps md) with (mkVmMapsFull (segments_reserved PSEGS) [] [] brk brk lim mbase sp0). reflexivity.
    - change (m_vmmaps md) with (mkVmMapsFull (segments_reserved PSEGS) [] [] brk brk lim mbase sp0). unfold alloc_top. cbn [vm_init_sp]. lia.
    - change (m_vmmaps md) with (mkVmMapsFull (segments_reserved PSEGS) [] [] brk brk lim mbase sp0). reflexivity.
    - reflexivity.
    - change (m_vmmaps md) with (mkVmMapsFull (segments_reserved PSEGS) [] [] brk brk lim mbase sp0). reflexivity.
    - cbn [LY ly_brk0]. unfold PGSZ. lia.
    - cbn [LY ly_brk0]. unfold PGSZ. exact B3.
    - change (m_vmmaps md) with (mkVmMapsFull (segments_reserved PSEGS) [] [] brk brk lim mbase sp0). unfold Mmap.min_brk. cbn. lia.
    - cbn [LY ly_brk0]. unfold HTOP, stack_max_size. lia.
    - change (m_vmmaps md) with (mkVmMapsFull (segments_reserved PSEGS) [] [] brk brk lim mbase sp0). reflexivity.
    - change (m_vmmaps md) with (mkVmMapsFull (segments_reserved PSEGS) [] [] brk brk lim mbase sp0). unfold alloc_top. cbn [vm_init_sp].
      unfold stack_max_size in *. lia.
    - change (m_vmmaps md) with (mkVmMapsFull (segments_reserved PSEGS) [] [] brk brk lim mbase sp0). cbn. lia. }
  destruct (heap_initI HTOP (LY brk) (bv_unsigned (canary rdraw)) AUXV RND TYPS mem md eq_refl ltac:(unfold HTOP, stack_max_size; lia)
              hi_env (hi_kro sp0 av ev uid tid hw rdraw regs mem Hsp ME) hi_page (hi_init_env brk) ltac:(lia) ltac:(lia) HLK hi_ctx_zero)
    as (hs0 & HQ & _ & _ & _ & _ & Ha & Hr & Ht).
  exists hs0. split; [exact HQ|].
  intros x Hx. unfold INIT in Hx. rewrite Ha, Hr, Ht in Hx. change (Z.of_nat (length TYPS)) with 9 in Hx. cbn [ioutside] in Hx.
  assert (HX : AUXV <= x < AUXV + 16 * 9 + 8 \/ RND + 8 <= x < RND + 16) by lia. clear Hx.
  split; [unfold auxv_off in *; lia|].
  pose proof Hva as [[LA _] _].
  destruct (Nat.eq_dec (length av) 1) as [E1|E1].
  - (* [comment removed for export] *)
    right. unfold cat_argv_ptr. rewrite nth_overflow by (rewrite length_string_addrs_fst; lia). rewrite (nth_overflow av) by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0. cbn [length]. unfold auxv_off in *. lia.
  - pose proof (u_cat_argv_ptr RPH sp0 rdraw av ev uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 1 ltac:(lia)) as U1.
    pose proof (total_arg_bytes_firstn_le 2 av) as T2. rewrite tot_firstn2 in T2 by lia.
    destruct HX as [HX|HX]; [left | right]; unfold cat_struct_size, auxv_off, auxv_size in *; lia.
Qed.

End HIS.
