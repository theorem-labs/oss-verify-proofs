(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge SysStep ITree Nodes Decode Frame ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog HeapFull Stdio PcapTypes Pcap. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.EntryRnd.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU MallocTree MallocHINV. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_main_A__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_fwritex__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMalloc_final. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.GIInit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceT.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceTB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_final.TwB.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL}.
(* [comment removed for export] *)
Notation MSR R := (msec_of_rnd (rc_rnd R)) (only parsing).
Definition KS : modkit fheap hptr :=
  {| mk_heap := fun h R CL m => HEAPT (MSECV := MSR R) h (utp R) CL m ;
     mk_stdio := fun l R FB m => STDIOR l FB m |}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition heap_client_iv_okT__stmt : Prop := forall R LB iv, heap_client_iv R LB iv -> client_write_okT (utp R) LB iv.
Section Sz1.
Variables R LB : ltac2:(SecDiet.SzSec.tyM 'heap_client_iv_okT__stmt "vv" @R).
Lemma heap_client_iv_okT__body : ltac2:(SecDiet.SzSec.bodyP 'heap_client_iv_okT__stmt "vv").
Proof using Type. pin_using tt. ceil_facts.
  intros [lo hi] H.
 unfold heap_client_iv, client_write_okT, iv_in_block in *. cbn [fst snd] in *.
  unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; ceil_facts.
  destruct H as [H|[H|[H|H]]].
  - left. lia.
  - right; right; left. apply Exists_exists in H. destruct H as (b & Hb & H1 & H2). exists b. split; [exact Hb|].
    unfold cb_addr, cb_size, tb_addr, tb_size in *. lia.
  - right; left. lia.
  - right; right; right. lia.
Qed.
End Sz1.
Lemma heap_client_iv_okT : ltac:(let t := eval cbv delta [heap_client_iv_okT__stmt] in heap_client_iv_okT__stmt in exact t).
Proof using Type. intros R LB. ltac2:(SecDiet.SzSec.closeP 'heap_client_iv_okT__body "vv"). Qed.

Theorem KS_heap_frame_law : heap_frame_law KS.
Proof using Type. pin_using tt. ceil_facts.
  intros h R LB m m' W HH MU WM FW. cbn [mk_heap KS] in *.
  eapply HEAPT_frame; [exact HH| exact MU| exact WM|].
  eapply Forall_impl; [| exact FW]. intros iv. apply heap_client_iv_okT.
Qed.

Theorem KS_heap_perm_law : heap_perm_law KS.
Proof using Type. pin_using tt. ceil_facts. intros h R LB LB' m HH P. cbn [mk_heap KS] in *. eapply HEAPT_perm; [exact HH| exact P]. Qed.

Theorem KS_heap_addr_law : heap_addr_law KS full_ops.
Proof using Type. pin_using tt. ceil_facts.
  intros h R LB m [[q A] n] HH Hin. cbn [mk_heap KS ho_addr full_ops cb_tok cb_addr fst snd] in *.
  exact (HEAPT_addr h (utp R) LB m q A n HH Hin).
Qed.

Lemma blocks_apart_of : forall u (LB : list (@cblock hptr)),
  Forall (block_ok u) LB ->
  (forall b1 b2, In b1 LB -> In b2 LB -> cb_tok b1 <> cb_tok b2 -> apart b1 b2) ->
  List.NoDup (map cb_tok LB) -> blocks_apart LB.
Proof using Type. pin_using tt. ceil_facts.
  induction LB as [|b LB IH]; intros BO AP ND; cbn; [exact I|].
  apply Forall_cons_iff in BO. destruct BO as [Bb BO]. cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND]. split.
  - apply Forall_forall. intros b' Hb'. apply AP; [left; reflexivity| right; exact Hb'|].
    intros E. apply NI. rewrite E. apply in_map. exact Hb'.
  - apply IH; [exact BO| intros b1 b2 H1 H2; apply AP; right; assumption| exact ND].
Qed.

Definition KS_heap_blocks_law__stmt : Prop := heap_blocks_law KS.
Section Sz6.
Variables h R LB m : ltac2:(SecDiet.SzSec.tyM 'KS_heap_blocks_law__stmt "vvvv" @h).
Lemma KS_heap_blocks_law__body : ltac2:(SecDiet.SzSec.bodyP 'KS_heap_blocks_law__stmt "vvvv").
Proof using Type. pin_using tt. ceil_facts.
  intros HH.
 cbn [mk_heap KS] in HH. split.
  - apply Forall_forall. intros [[q A] n] Hin. pose proof (HEAPT_range h (utp R) LB m q A n HH Hin) as BR.
    unfold block_ok, rblock_rangeu, cb_addr, cb_size in *; ceil_facts. cbn [fst snd]. lia.
  - destruct HH as (H & ids & HR & CR & ND & FR).
    apply (blocks_apart_of (utp R)).
    + apply Forall_forall. intros [[q A] n] Hin. pose proof (HEAPT_range h (utp R) LB m q A n (ex_intro _ H (ex_intro _ ids (conj HR (conj CR (conj ND FR))))) Hin) as BR.
      unfold block_ok, rblock_rangeu, cb_addr, cb_size in *; ceil_facts. cbn [fst snd]. lia.
    + intros b1 b2 H1 H2 NE. unfold apart.
      exact (HEAPT_disjoint h (utp R) LB m b1 b2 (ex_intro _ H (ex_intro _ ids (conj HR (conj CR (conj ND FR))))) H1 H2 NE).
    + exact ND.
Qed.
End Sz6.
Theorem KS_heap_blocks_law : ltac:(let t := eval cbv delta [KS_heap_blocks_law__stmt] in KS_heap_blocks_law__stmt in exact t).
Proof using Type. intros h R LB m. ltac2:(SecDiet.SzSec.closeP 'KS_heap_blocks_law__body "vvvv"). Qed.

(* [comment removed for export] *)
Definition KS_heap_init_law__stmt : Prop := forall rnd0 : EntryDraw,
  heap_init_law full_ops KS (fheap_init (bv_unsigned (malloc_secret rnd0)) (reservedZ usegs)) rnd0.
Section Sz7.
Variables rnd0 R m : ltac2:(SecDiet.SzSec.tyM 'KS_heap_init_law__stmt "vvv" @rnd0).
Lemma KS_heap_init_law__body : ltac2:(SecDiet.SzSec.bodyP 'KS_heap_init_law__stmt "vvv").
Proof using Type. pin_using tt. ceil_facts.
  intros ERND IM TB SPW CLO.
 cbn [mk_heap KS ho_pin full_ops]. rewrite hf_pin_init.
  rewrite <- ERND. change (bv_unsigned (malloc_secret (rc_rnd R))) with (@msecret (MSR R)).
  apply (HEAPT_init (MSECV := MSR R)).
  { unfold tls_block_ok_u in TB. unfold tls_ok. destruct TB as (T1 & T2 & T3 & T4).
    split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. left; lia. }
  destruct IM as (ML & CB & CW & NL & PS & GOT & GUARD & REPL).
  unfold rheap_init_mem, RMREPLACED, RMLOCK, RCTX, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD.
  replace (0x54560 + 928) with 0x54900 by reflexivity.
  exact (conj ML (conj CB (conj CW (conj NL (conj PS (conj GOT (conj GUARD REPL))))))).
Qed.
End Sz7.
Theorem KS_heap_init_law : ltac:(let t := eval cbv delta [KS_heap_init_law__stmt] in KS_heap_init_law__stmt in exact t).
Proof using Type. intros rnd0 R m. ltac2:(SecDiet.SzSec.closeP 'KS_heap_init_law__body "vvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rauxv_ok_of_core : forall R m,
  CORE_LIBC R m -> CORE_STK R m -> 0x7fff80000000 <= usp0 R -> CEILZ <= rc_lo R -> auxv_ok (MSECV := MSR R) usegs RAUXV_CELL m (usp0 R).
Proof using Type. pin_using tt. ceil_facts.
  (* [comment removed for export] *)
  intros R m (LC & _) STK SPW CLO. unfold rc_lo in CLO.
  set (sp0 := rc_sp0 R) in *. set (argv := rc_argv R) in *. set (envp := rc_envp R) in *. set (uid := rc_uid R) in *.
  set (hw := rc_hw R) in *. set (rnd := rc_rnd R) in *.
  set (ph := Ubsan.M.phdrs) in *.
  unfold usp0 in *. fold sp0 in SPW, CLO |- *.
  unfold libc_cells in LC.
  apply (proj1 (InitMem.rw_cells_app usegs m _ [_; _; _; _; _] _)) in LC as [_ LC]. cbn [cells_size csize Nat.add] in LC.
  apply (proj1 (InitMem.rw_cells_app usegs m _ [_] _)) in LC as [AUX _].
  match type of AUX with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in AUX end.
  unfold CORE_STK, usp0 in STK. fold ph sp0 argv envp uid hw rnd in STK. rewrite build_stack_bytes_eq in STK.
  pose proof (raw_bytes_length ph sp0 argv envp uid hw) as RL.
  pose proof (raw_len_nonneg ph sp0 argv envp uid hw rnd) as RN.
  apply bytes_at_app in STK. destruct STK as [RAW STK].
  apply bytes_at_app in STK. destruct STK as [_ RND]. rewrite repeat_length in RND.
  rewrite at_random_split in RND.
  apply bytes_at_app in RND. destruct RND as [_ RND]. rewrite length_at_random_lo in RND.
  unfold raw_bytes in RAW. apply bytes_at_app in RAW. destruct RAW as [B _].
  cbn [u64s app] in B. rewrite u64s_app in B. cbn [u64s app] in B. rewrite u64s_app in B. cbn [u64s app] in B.
  repeat rewrite <- app_assoc in B. cbn [app] in B.
  apply bytes_at_app in B. destruct B as [_ B]. rewrite length_le8 in B.
  apply bytes_at_app in B. destruct B as [_ B]. rewrite u64s_length in B. unfold argv_ptrs in B. rewrite length_map, str_ptrs_length in B.
  apply bytes_at_app in B. destruct B as [_ B]. rewrite length_le8 in B.
  apply bytes_at_app in B. destruct B as [_ B]. rewrite u64s_length in B. unfold envp_ptrs in B. rewrite length_map, str_ptrs_length in B.
  apply bytes_at_app in B. destruct B as [_ B]. rewrite length_le8 in B.
  pose proof B as BB. destruct BB as (B0 & B1 & _). rewrite u64s_length in B1. change (length (auxv_words _ _ _ _ _ _)) with 20%nat in B1.
  pose proof RND as RR. destruct RR as (R0 & R1 & _). rewrite length_at_random_hi in R1.
  unfold auxv_ok.
  exists (auxv_addr sp0 argv envp), (Z.of_N (ph_addr ph) mod 2^64), (Z.of_N (ph_ent ph) mod 2^64),
         (Z.of_N (ph_num ph) mod 2^64), (bv_unsigned hw), 4096, (bv_unsigned uid), (bv_unsigned uid), 0, (rnd_addr sp0 argv envp).
  pose proof (zr_word uid) as UR. unfold inr64 in UR. pose proof (zr_word hw) as HWR. unfold inr64 in HWR.
  assert (EAV : auxv_addr sp0 argv envp = bv_unsigned sp0 + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8).
  { unfold auxv_addr, argc, envc. lia. }
  split. { unfold wz. exact AUX. }
  split. { rewrite EAV. unfold auxv_list, wz. cbn [map]. rewrite !Z_to_bv_mod64, !Z_to_bv_bv_unsigned. exact B. }
  split. { replace (le8 (wz (@msecret (MSR R)))) with (at_random_hi rnd).
           2:{ rewrite msecret_of_rnd. unfold wz. rewrite Z_to_bv_bv_unsigned. symmetry. apply le8_malloc_secret. }
           replace (rnd_addr sp0 argv envp + 8) with
             (bv_unsigned sp0 + Z.of_nat (length (raw_bytes ph sp0 argv envp uid hw)) + Z.of_nat (Z.to_nat (pad_len argv envp)) + Z.of_nat 8).
           2:{ unfold rnd_addr. lia. }
           exact RND. }
  ceil_facts. unfold rnd_addr in *.
  repeat split; try lia; try (apply Z.mod_pos_bound; lia).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma heap_pres_of_presT : forall R (LB : list (@cblock hptr)) SP m m',
  heap_presT (utp R) LB SP m m' -> heap_pres R LB SP m m'.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros R LB SP m m' PR a Ha Hk. apply (PR a Ha).
  unfold heap_keeps, heap_static, RMLOCK, RCTX in *.
  destruct Hk as [K|[K|[K|K]]]; [left; exact K| | right; left; lia| right; right; right; lia].
  right; right; left. apply in_block_In in K. destruct K as (b & Hb & K). exists b. split; [exact Hb|].
  unfold cb_addr, cb_size, tb_addr, tb_size in *. lia.
Qed.

(* [comment removed for export] *)
Lemma CORE_TLS_heap_agree : forall P R m m' (errv' : word),
  agrees_on P m m' ->
  (forall a, core_tls_fp R a -> ~ (utp R - 164 <= a < utp R - 160) -> P a) ->
  rw_cells usegs m' (utp R + -164) [C4 errv'] ->
  CORE_TLS R m -> CORE_TLS R m'.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros P R m m' errv' AG HP ERR (t & e & A1 & A2 & A3 & A4 & A5 & A6 & Ht). unfold core_tls_fp in HP. exists t, errv'.
  Local Ltac trx AG HP A := eapply agrees_rw_cells; [exact AG | exact A | intros a Ha; apply HP; sl_lit_sizes_in Ha; cbn in Ha; lia].
  split; [trx AG HP A1|]. split; [exact ERR|]. split; [trx AG HP A3|]. split; [trx AG HP A4|]. split; [trx AG HP A5|]. split; [trx AG HP A6| exact Ht].
Qed.

Section Glue.
  (* [comment removed for export] *)
  Hypothesis SFL : stdio_fp_law KS.

  #[local] Abbreviation PS := (PState fheap hptr).
  #[local] Abbreviation cblk := (@cblock hptr).

  (* [comment removed for export] *)
  Definition GIo_heap_step__stmt : Prop := forall R (s : PS) CL FB m h' l' CL' (LBp : list cblk) m' (errv' : word) SP,
    GIo KS R s CL FB m ->
    HEAPT (MSECV := MSR R) h' (utp R) (CL' ++ FB) m' ->
    heap_presT (utp R) LBp SP m m' -> (forall a, in_block FB a -> in_block LBp a) -> SP <= usp0 R ->
    rw_cells usegs m' (utp R + -164) [C4 errv'] ->
    (forall FB0 m0, mk_stdio KS (ps_libc s) R FB0 m0 -> mk_stdio KS l' R FB0 m0) ->
    GIo KS R (mkPS h' l' (ps_outfile s) (ps_tls s)) CL' FB m'.
  Section Sz10.
  Variables R s CL FB m h' l' CL' LBp m' errv' SP : ltac2:(SecDiet.SzSec.tyM 'GIo_heap_step__stmt "vvvvvvvvvvvv" @R).
  Lemma GIo_heap_step__body : ltac2:(SecDiet.SzSec.bodyP 'GIo_heap_step__stmt "vvvvvvvvvvvv").
  Proof using SFL. pin_using (fun (SFL : unit) => tt). ceil_facts.
    intros G HH' PR HFB HSP ERR HL.
    destruct G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW).
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (_ & _ & _ & TBI).
    pose proof (heap_pres_of_presT R LBp SP m m' PR) as AG. unfold heap_pres in AG.
    unfold GIo. cbn [ps_heap ps_libc ps_outfile ps_tls].
    split; [exact HH'|].
    split. { apply HL. eapply SFL; [exact HS|]. eapply agrees_on_weaken; [exact AG|].
             intros a [X|X]; [| right; left; apply HFB; exact X].
             unfold S3.GI.TwB.stdio_static, heap_keeps, heap_static in *. right; right; left. lia. }
    split. { eapply HARNR_agree; [exact AG| |exact HA]. intros a Hp. unfold harn_fp, harn_static, heap_keeps, heap_static in *. lia. }
    split. { eapply CORE_TLS_heap_agree; [exact AG| |exact ERR|exact CT]. intros a Hp Hne. unfold core_tls_fp, heap_keeps in *. right; right; right. lia. }
    split. { eapply PCAP_TLS_agree; [exact AG| |exact PT]. intros a Hp. unfold pcap_tls_fp, heap_keeps in *. right; right; right. lia. }
    split. { eapply CORE_LIBC_agree; [exact AG| |exact CLI]. intros a Hp. unfold core_libc_fp, heap_keeps, heap_static in *. right; right; left. lia. }
    split. { eapply CORE_MISC_agree; [exact AG| |exact CM]. intros a Hp. unfold core_misc_fp, heap_keeps, heap_static in *. right; right; left. lia. }
    split. { eapply CORE_EXIT_agree; [exact AG| |exact CE]. intros a Hp. unfold core_exit_fp, heap_keeps, heap_static in *. right; right; left. lia. }
    split. { eapply CORE_STK_agree; [exact AG| |exact CS]. intros a Hp. unfold core_stk_fp, heap_keeps in *. left. lia. }
    split; [exact Etls|]. split; [exact TB|]. split; [exact (KS_heap_blocks_law _ _ _ _ HH')| exact SPW].
  Qed.
  End Sz10.
  Lemma GIo_heap_step : ltac:(let t := eval cbv delta [GIo_heap_step__stmt] in GIo_heap_step__stmt in exact t).
  Proof using SFL. intros R s CL FB m h' l' CL' LBp m' errv' SP. ltac2:(SecDiet.SzSec.closeP 'GIo_heap_step__body "vvvvvvvvvvvv"). Qed.

  Lemma implM_upd_bind : forall {St B} (f : St -> St) (k : unit -> @Monad.M St B) s Q ms,
    implM usegs (k tt) (f s) Q ms -> implM usegs (mbind (mupd f) k) s Q ms.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. exact H. Qed.

  Lemma in_block_appR : forall (L1 L2 : list cblk) a, in_block L2 a -> in_block (L1 ++ L2) a.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros L1 L2 a X. apply in_block_app. right. exact X. Qed.

  Lemma client_keeps_of_presT : forall R (CL FB : list cblk) SP m m',
    heap_presT (utp R) (CL ++ FB) SP m m' -> agrees_on (client_keeps CL SP) m m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros R CL FB SP m m' PR. eapply agrees_on_weaken; [exact (heap_pres_of_presT R _ _ _ _ PR)|].
    intros a [X|X]; [left; exact X| right; left; apply in_block_app; left; exact X].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition KS_malloc_o__stmt : Prop := malloc_stmt_o full_ops KS.
  Section Sz14.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo n : ltac2:(SecDiet.SzSec.tyM 'KS_malloc_o__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma KS_malloc_o__body : ltac2:(SecDiet.SzSec.bodyP 'KS_malloc_o__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using SFL. pin_using (fun (SFL : unit) => tt). ceil_facts.
 intros (G & ST & LOR & LOB & SPM & MI & Etp & AL) Ha0 Hn.
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW).
    pose proof CT as (t & e & _ & ERR & _).
    subst tp. unfold pmalloc. cbn [ho_malloc full_ops].
    assert (HSP : bv_unsigned sp <= usp0 R) by (unfold rc_spmain in SPM; lia).
    eapply (implM_bind usegs).
    { apply (hmalloc_spec (MSECV := MSR R) ra sp gp (rc_tp R) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s (CL ++ FB) n lo (usp0 R) e).
      - exact HH.
      - apply rauxv_ok_of_core; try assumption; [exact (proj1 (proj1 SPW)) | exact (proj2 SPW)].
      - exact HSP.
      - exact ST.
      - unfold rc_lo in *; ceil_facts. lia.
      - unfold RMALLOC_STACK, MALLOC_STACK in *. lia.
      - exact ERR.
      - exact MI.
      - exact Ha0.
      - exact Hn. }
    intros r s' ms' POST.
    destruct POST as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & PRES & ES' & RES).
    pose proof (client_keeps_of_presT R CL FB _ m m' PRES) as AGC.
    unfold enomem_on_null. destruct r as [q|].
    - apply implM_ret. apply evt_done.
      destruct RES as (A & junk & Hb0 & EA & NI & BR & HH' & BLK).
      exists b0, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [rewrite ES'; reflexivity|].
      split; [exact MI'|]. split; [exact ST'|]. split; [exact AGC|].
      exists A, junk. split; [exact Hb0|]. split; [| exact BLK].
      rewrite ES'. unfold set_heap.
      eapply (GIo_heap_step R s CL FB m _ _ ((q, A, n) :: CL) (CL ++ FB) m' errv' (bv_unsigned sp));
        [exact G| exact HH'| exact PRES| apply in_block_appR| exact HSP| exact ERR'| intros FB0 m0 X; exact X].
    - destruct RES as (Hb0 & EEN & HH').
      unfold set_errno_ps, set_errno, upd_lc. apply implM_upd_bind. apply implM_ret. apply evt_done.
      exists b0, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [rewrite ES'; reflexivity|].
      split; [exact MI'|]. split; [exact ST'|]. split; [exact AGC|].
      split; [exact Hb0|]. rewrite ES'. unfold set_heap, set_libc. cbn [ps_heap ps_libc ps_outfile ps_tls].
      split.
      + eapply (GIo_heap_step R s CL FB m _ _ CL (CL ++ FB) m' errv' (bv_unsigned sp));
          [exact G| exact HH'| exact PRES| apply in_block_appR| exact HSP| exact ERR'| intros FB0 m0 X; exact X].
      + unfold enomem_at. cbn [ps_libc lc_errno set_errno_lc]. split; [reflexivity|]. rewrite <- EEN. exact ERR'.
  Qed.
  End Sz14.
  Theorem KS_malloc_o : ltac:(let t := eval cbv delta [KS_malloc_o__stmt] in KS_malloc_o__stmt in exact t).
  Proof using SFL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo n. ltac2:(SecDiet.SzSec.closeP 'KS_malloc_o__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition KS_calloc_o__stmt : Prop := calloc_stmt_o full_ops KS.
  Section Sz15.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo cnt sz : ltac2:(SecDiet.SzSec.tyM 'KS_calloc_o__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma KS_calloc_o__body : ltac2:(SecDiet.SzSec.bodyP 'KS_calloc_o__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using SFL. pin_using (fun (SFL : unit) => tt). ceil_facts.
 intros (G & ST & LOR & LOB & SPM & MI & Etp & AL) Ha0 Ha1 Hc Hs Hmax.
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW).
    pose proof CT as (t & e & _ & ERR & _).
    subst tp. unfold pcalloc. cbn [ho_calloc full_ops].
    assert (HSP : bv_unsigned sp <= usp0 R) by (unfold rc_spmain in SPM; lia).
    eapply (implM_bind usegs).
    { apply (hcalloc_spec (MSECV := MSR R) ra sp gp (rc_tp R) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s (CL ++ FB) cnt sz lo (usp0 R) e).
      - exact HH.
      - apply rauxv_ok_of_core; try assumption; [exact (proj1 (proj1 SPW)) | exact (proj2 SPW)].
      - exact HSP.
      - exact ST.
      - unfold rc_lo in *; ceil_facts. lia.
      - unfold RCALLOC_STACK, MALLOC_STACK in *. lia.
      - exact ERR.
      - exact MI.
      - exact Ha0.
      - exact Ha1.
      - lia.
      - lia.
      - unfold RCALLOC_MAX. exact Hmax. }
    intros r s' ms' POST.
    destruct POST as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & PRES & ES' & RES).
    pose proof (client_keeps_of_presT R CL FB _ m m' PRES) as AGC.
    unfold enomem_on_null. destruct r as [q|].
    - apply implM_ret. apply evt_done.
      destruct RES as (A & Hb0 & EA & NI & BR & HH' & BLK).
      exists b0, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [rewrite ES'; reflexivity|].
      split; [exact MI'|]. split; [exact ST'|]. split; [exact AGC|].
      exists A. split; [exact Hb0|]. split; [| exact BLK].
      rewrite ES'. unfold set_heap.
      eapply (GIo_heap_step R s CL FB m _ _ ((q, A, cnt * sz) :: CL) (CL ++ FB) m' errv' (bv_unsigned sp));
        [exact G| exact HH'| exact PRES| apply in_block_appR| exact HSP| exact ERR'| intros FB0 m0 X; exact X].
    - destruct RES as (Hb0 & EEN & HH').
      unfold set_errno_ps, set_errno, upd_lc. apply implM_upd_bind. apply implM_ret. apply evt_done.
      exists b0, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [rewrite ES'; reflexivity|].
      split; [exact MI'|]. split; [exact ST'|]. split; [exact AGC|].
      split; [exact Hb0|]. rewrite ES'. unfold set_heap, set_libc. cbn [ps_heap ps_libc ps_outfile ps_tls].
      split.
      + eapply (GIo_heap_step R s CL FB m _ _ CL (CL ++ FB) m' errv' (bv_unsigned sp));
          [exact G| exact HH'| exact PRES| apply in_block_appR| exact HSP| exact ERR'| intros FB0 m0 X; exact X].
      + unfold enomem_at. cbn [ps_libc lc_errno set_errno_lc]. split; [reflexivity|]. rewrite <- EEN. exact ERR'.
  Qed.
  End Sz15.
  Theorem KS_calloc_o : ltac:(let t := eval cbv delta [KS_calloc_o__stmt] in KS_calloc_o__stmt in exact t).
  Proof using SFL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo cnt sz. ltac2:(SecDiet.SzSec.closeP 'KS_calloc_o__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma filter_all_true : forall {A} (f : A -> bool) l, (forall x, In x l -> f x = true) -> List.filter f l = l.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    induction l as [|x l IH]; intros H; [reflexivity|]. cbn. rewrite (H x (or_introl eq_refl)). f_equal. apply IH.
    intros y Hy. apply H. right. exact Hy.
  Qed.

  Definition lbt_remove_mid__stmt : Prop := forall (C1 C2 FB : list cblk) q A n,
    List.NoDup (map tb_tok ((C1 ++ (q, A, n) :: C2) ++ FB)) ->
    lbt_remove q ((C1 ++ (q, A, n) :: C2) ++ FB) = (C1 ++ C2) ++ FB.
  Section Sz17.
  Variables C1 C2 FB q A n : ltac2:(SecDiet.SzSec.tyM 'lbt_remove_mid__stmt "vvvvvv" @C1).
  Lemma lbt_remove_mid__body : ltac2:(SecDiet.SzSec.bodyP 'lbt_remove_mid__stmt "vvvvvv").
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros ND.
 unfold lbt_remove.
    rewrite <- app_assoc in ND |- *. cbn [app] in ND |- *. rewrite map_app in ND. cbn [map] in ND.
    apply List.NoDup_remove in ND. destruct ND as [_ NI]. rewrite <- map_app in NI.
    assert (HT : forall x, In x (C1 ++ C2 ++ FB) -> negb (N.eqb (tb_tok x) q) = true).
    { intros x Hx. destruct (N.eqb_spec (tb_tok x) q) as [E|NE]; [|reflexivity]. exfalso. apply NI.
      change (tb_tok (q, A, n)) with q. rewrite <- E. apply in_map. exact Hx. }
    rewrite filter_app. cbn [List.filter]. change (tb_tok (q, A, n)) with q. rewrite N.eqb_refl. cbn [negb].
    rewrite <- filter_app. rewrite <- app_assoc. apply filter_all_true. exact HT.
  Qed.
  End Sz17.
  Lemma lbt_remove_mid : ltac:(let t := eval cbv delta [lbt_remove_mid__stmt] in lbt_remove_mid__stmt in exact t).
  Proof using CEILV. intros C1 C2 FB q A n. ltac2:(SecDiet.SzSec.closeP 'lbt_remove_mid__body "vvvvvv"). Qed.

  Definition KS_free_o__stmt : Prop := free_stmt_o full_ops KS.
  Section Sz18.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s C1 C2 FB q A n lo : ltac2:(SecDiet.SzSec.tyM 'KS_free_o__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma KS_free_o__body : ltac2:(SecDiet.SzSec.bodyP 'KS_free_o__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using SFL. pin_using (fun (SFL : unit) => tt). ceil_facts.
 intros (G & ST & LOR & LOB & SPM & MI & Etp & AL) Ha0.
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW).
    pose proof CT as (t & e & _ & ERR & _).
    subst tp. unfold pfree. cbn [ho_free full_ops].
    assert (HSP : bv_unsigned sp <= usp0 R) by (unfold rc_spmain in SPM; lia).
    assert (HIN : In (q, A, n) ((C1 ++ (q, A, n) :: C2) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    pose proof (lbt_remove_mid C1 C2 FB q A n (HEAPT_nodup (MSECV := MSR R) _ _ _ _ HH)) as ER.
    eapply (implM_mono usegs).
    { apply (hfree_spec (MSECV := MSR R) ra sp gp (rc_tp R) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s ((C1 ++ (q, A, n) :: C2) ++ FB) q A n lo (usp0 R) e).
      - exact HH.
      - exact HIN.
      - apply rauxv_ok_of_core; try assumption; [exact (proj1 (proj1 SPW)) | exact (proj2 SPW)].
      - exact HSP.
      - exact ST.
      - unfold rc_lo in *; ceil_facts. lia.
      - unfold RFREE_STACK, FREE_STACK in *. lia.
      - exact ERR.
      - exact MI.
      - exact Ha0. }
    intros [] s' ms' POST.
    destruct POST as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MI' & ST' & ERR' & AUX' & PRES & ES' & HH').
    rewrite ER in PRES, HH'.
    exists b0, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [rewrite ES'; reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact (client_keeps_of_presT R (C1 ++ C2) FB _ m m' PRES)|].
    rewrite ES'. unfold set_heap.
    eapply (GIo_heap_step R s _ FB m _ _ (C1 ++ C2) ((C1 ++ C2) ++ FB) m' e (bv_unsigned sp));
      [exact G| exact HH'| exact PRES| apply in_block_appR| exact HSP| exact ERR'| intros FB0 m0 X; exact X].
  Qed.
  End Sz18.
  Theorem KS_free_o : ltac:(let t := eval cbv delta [KS_free_o__stmt] in KS_free_o__stmt in exact t).
  Proof using SFL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s C1 C2 FB q A n lo. ltac2:(SecDiet.SzSec.closeP 'KS_free_o__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition KS_realloc_o__stmt : Prop := realloc_stmt_o full_ops KS.
  Section Sz19.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s C1 C2 FB q A sz lo n bs : ltac2:(SecDiet.SzSec.tyM 'KS_realloc_o__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma KS_realloc_o__body : ltac2:(SecDiet.SzSec.bodyP 'KS_realloc_o__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using SFL. pin_using (fun (SFL : unit) => tt). ceil_facts.
 intros (G & ST & LOR & LOB & SPM & MI & Etp & AL) Ha0 Ha1 Hn CH.
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW).
    pose proof CT as (t & e & _ & ERR & _).
    subst tp. unfold prealloc. cbn [ho_realloc full_ops].
    assert (HSP : bv_unsigned sp <= usp0 R) by (unfold rc_spmain in SPM; lia).
    assert (HIN : In (q, A, sz) ((C1 ++ (q, A, sz) :: C2) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    pose proof (lbt_remove_mid C1 C2 FB q A sz (HEAPT_nodup (MSECV := MSR R) _ _ _ _ HH)) as ER.
    eapply (implM_bind usegs).
    { apply (hrealloc_spec (MSECV := MSR R) ra sp gp (rc_tp R) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s
               ((C1 ++ (q, A, sz) :: C2) ++ FB) q A sz n lo (usp0 R) bs e).
      - exact HH.
      - exact HIN.
      - apply rauxv_ok_of_core; try assumption; [exact (proj1 (proj1 SPW)) | exact (proj2 SPW)].
      - exact HSP.
      - exact ST.
      - unfold rc_lo in *; ceil_facts. lia.
      - unfold RREALLOC_STACK, MALLOC_STACK in *. lia.
      - exact ERR.
      - exact MI.
      - exact CH.
      - exact Ha0.
      - exact Ha1.
      - exact Hn. }
    intros r s' ms' POST.
    destruct POST as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & PRES & ES' & RES).
    rewrite ER in PRES.
    pose proof (client_keeps_of_presT R (C1 ++ C2) FB _ m m' PRES) as AGC.
    unfold enomem_on_null. destruct r as [q'|].
    - apply implM_ret. apply evt_done.
      destruct RES as (A' & Hb0 & EA & NI & BR & HH' & BLK). rewrite ER in HH'.
      exists b0, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [rewrite ES'; reflexivity|].
      split; [exact MI'|]. split; [exact ST'|]. split; [exact AGC|].
      exists A'. destruct BLK as [junk BLK]. exists junk. split; [exact Hb0|]. split; [| exact BLK].
      rewrite ES'. unfold set_heap.
      eapply (GIo_heap_step R s _ FB m _ _ ((q', A', n) :: C1 ++ C2) ((C1 ++ C2) ++ FB) m' errv' (bv_unsigned sp));
        [exact G| exact HH'| exact PRES| apply in_block_appR| exact HSP| exact ERR'| intros FB0 m0 X; exact X].
    - destruct RES as (Hb0 & EEN & HH' & CHK).
      unfold set_errno_ps, set_errno, upd_lc. apply implM_upd_bind. apply implM_ret. apply evt_done.
      exists b0, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [rewrite ES'; reflexivity|].
      split; [exact MI'|]. split; [exact ST'|]. split; [exact AGC|].
      split; [exact Hb0|]. rewrite ES'. unfold set_heap, set_libc. cbn [ps_heap ps_libc ps_outfile ps_tls].
      split; [| split; [exact CHK|]].
      + eapply (GIo_heap_step R s _ FB m _ _ (C1 ++ (q, A, sz) :: C2) ((C1 ++ C2) ++ FB) m' errv' (bv_unsigned sp));
          [exact G| exact HH'| exact PRES| apply in_block_appR| exact HSP| exact ERR'| intros FB0 m0 X; exact X].
      + unfold enomem_at. cbn [ps_libc lc_errno set_errno_lc]. split; [reflexivity|]. rewrite <- EEN. exact ERR'.
  Qed.
  End Sz19.
  Theorem KS_realloc_o : ltac:(let t := eval cbv delta [KS_realloc_o__stmt] in KS_realloc_o__stmt in exact t).
  Proof using SFL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s C1 C2 FB q A sz lo n bs. ltac2:(SecDiet.SzSec.closeP 'KS_realloc_o__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition KS_malloc__stmt : Prop := malloc_stmt full_ops KS.
  Section Sz20.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo n : ltac2:(SecDiet.SzSec.tyM 'KS_malloc__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma KS_malloc__body : ltac2:(SecDiet.SzSec.bodyP 'KS_malloc__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using SFL. pin_using (fun (SFL : unit) => tt). ceil_facts.
 intros ([FB G] & ST & LOR & LOB & SPM & MI & Etp & AL) Ha0 Hn.
    eapply (implM_mono usegs).
    { apply (KS_malloc_o ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo n);
        [| exact Ha0| exact Hn].
      split; [exact G|]. split; [exact ST|]. split; [exact LOR|]. split; [exact LOB|]. split; [exact SPM|]. split; [exact MI|]. split; [exact Etp| exact AL]. }
    intros r s' ms' (a0v & m' & REGS & OF' & MI' & ST' & AG & RES).
    destruct REGS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
    unfold malloc_post. exists u0, u1, u2, a0v, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|].
    destruct r as [q|].
    - destruct RES as (A & junk & Ea & G' & BLK). exists A, junk. split; [exact Ea|]. split; [exists FB; exact G'|]. split; [exact BLK|].
      split.
      + exact (GIo_block_ok _ _ _ _ _ _ _ G' (or_introl eq_refl)).
      + cbn [ho_addr full_ops]. destruct G' as (HH' & _). exact (HEAPT_addr _ _ _ _ q A n HH' (or_introl eq_refl)).
    - destruct RES as (Ea & G' & _). split; [exact Ea| exists FB; exact G'].
  Qed.
  End Sz20.
  Theorem KS_malloc : ltac:(let t := eval cbv delta [KS_malloc__stmt] in KS_malloc__stmt in exact t).
  Proof using SFL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo n. ltac2:(SecDiet.SzSec.closeP 'KS_malloc__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition KS_free__stmt : Prop := free_stmt full_ops KS.
  Section Sz21.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s C1 C2 q A n lo : ltac2:(SecDiet.SzSec.tyM 'KS_free__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma KS_free__body : ltac2:(SecDiet.SzSec.bodyP 'KS_free__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using SFL. pin_using (fun (SFL : unit) => tt). ceil_facts.
 intros ([FB G] & ST & LOR & LOB & SPM & MI & Etp & AL) Ha0.
    eapply (implM_mono usegs).
    { apply (KS_free_o ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s C1 C2 FB q A n lo);
        [| exact Ha0].
      split; [exact G|]. split; [exact ST|]. split; [exact LOR|]. split; [exact LOB|]. split; [exact SPM|]. split; [exact MI|]. split; [exact Etp| exact AL]. }
    intros [] s' ms' (a0v & m' & REGS & OF' & MI' & ST' & AG & G').
    destruct REGS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
    unfold free_post. exists u0, u1, u2, a0v, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG| exists FB; exact G'].
  Qed.
  End Sz21.
  Theorem KS_free : ltac:(let t := eval cbv delta [KS_free__stmt] in KS_free__stmt in exact t).
  Proof using SFL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s C1 C2 q A n lo. ltac2:(SecDiet.SzSec.closeP 'KS_free__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Glue.

End WithCeil.
