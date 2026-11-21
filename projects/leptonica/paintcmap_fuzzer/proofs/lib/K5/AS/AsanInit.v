(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (section Init restated over the launch's ProcInput, image entry and launch facts, with the recorded-kernel and channel-reader premises (Definition inp, Lemma W_range and Let SIMG removed); the stack image and auxv layout of the new launch, symbolic in CONFIG_RSEQ (the launch auxv words in byte string K_LA, the cache words, the string area up to ed_top); the initial model's vDSO pair and its reservation in the ledger (init_co_res, init_co_totsz, init_co_split); the new zero stack window below sp; the new init_cfg_eq_segs over the run's segment list; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AS Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim StepTac ShapeAlg AgentLib StartupAux RefLayout ArgvEnv AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan AsanPlanSound.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AS Require Import AsanCeil.  (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AS Require Import LiaFastAS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.  (* [comment removed for export] *)
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= zify_fast_euclid.

Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition LIMIT : Z := target_alloc_limit.

(* the per-image facts the initial state needs *)
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

(* LPS 08b1429: the size of the initial stack image is [ed_top - sp]
   ([PropExec.length_entry_stack_image_launch]). *)
Definition stack_image_size (sp top : word) : Z :=
  (bv_unsigned top - bv_unsigned sp)%Z.

(* the auxv's size at either value of CONFIG_RSEQ, hypothesis-free: the model's own lemma
   (LPS 75d69e00 theories/Common/AsanPlanCore.v:3194, same name and statement) *)
Lemma AUXSZ_of : forall b, AUXSZ (rseq_z b) = Z.of_nat (StackLayout.auxv_size b).
Proof. intros [|]; vm_compute; reflexivity. Qed.

Lemma rseq_z_range : forall b, 0 <= rseq_z b <= 1.
Proof. intros [|]; cbn; lia. Qed.

Lemma auxv_count_rz : forall b, Z.of_nat (StackLayout.auxv_count b) = 27 + 2 * rseq_z b.
Proof. intros [|]; reflexivity. Qed.

(* THE AUXV'S SIZE AT EVERY BUILD, the one case split on CONFIG_RSEQ the layout
   arithmetic needs, taken once and at a [vm_compute]: [auxv_size b =
   16 * auxv_count b] and [auxv_count b = if b then 29 else 27]
   ([StackLayout.v:276-277] at 75d69e00), so 464 with the flag and 432 without.
   Stated for EVERY [b] rather than for one run's flag, so that no consumer can
   pick up a kernel pin from it. *)
Lemma auxv_size_bounds : forall b : bool, 432 <= Z.of_nat (StackLayout.auxv_size b) <= 464.
Proof. intros [|]; vm_compute; split; intro H; discriminate H. Qed.

(* reading one 8-byte word out of a byte string *)
Lemma blob0 : forall (v : word) post, blob_val false (word_to_le_bytes 8 v ++ post) 0 8 = v.
Proof.
  intros v post. unfold blob_val, blob_bytes. cbv beta iota zeta.
  change (Z.to_nat 0) with 0%nat. rewrite skipn_O.
  rewrite firstn_app, length_N_to_le_bytes, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite firstn_all2 by (rewrite length_N_to_le_bytes; lia).
  rewrite bytes_le_to_Z_8. apply Z_to_bv_bv_unsigned.
Qed.

Lemma blob_skip : forall (a rest : list byte) off, length a = 8%nat -> 0 <= off ->
  blob_val false (a ++ rest) (8 + off) 8 = blob_val false rest off 8.
Proof.
  intros a rest off Ha Ho. unfold blob_val, blob_bytes.
  rewrite Z2Nat.inj_add by lia. change (Z.to_nat 8) with 8%nat.
  rewrite skipn_app. rewrite (skipn_all2 a) by (rewrite Ha; lia). rewrite Ha. cbn [app].
  replace (8 + Z.to_nat off - 8)%nat with (Z.to_nat off) by lia. reflexivity.
Qed.

Section Init.
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  (* the image's ELF entry: [Run.init_config]'s pc and the auxv's AT_ENTRY *)
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* ed_random = the AT_RANDOM bytes, ed_top = the stack VMA's end *)
  Variable brk0 mbase : word.
  (* the run's input *)
  Variable inp : ProcInput.

  (* The launch's fields, named as the model's [AsanInit] names them.  The
     names matter to [lia]: [zify] reads [length argv] and
     [length (in_argv inp)] as two atoms, so a hypothesis stated over one and
     a goal over the other carry no common fact.  Everything below, the
     hypotheses included, is therefore stated over these names. *)
  Let argv := in_argv inp.
  Let envp := in_envp inp.
  Let uid := in_uid inp.
  Let gid := in_gid inp.
  Let hw := in_hwcap inp.
  Let execfn := in_execfn inp.
  Let rseq : bool := kb_rseq (in_kernel inp).
  Let entryw : word := Z_to_bv 64 (Z.of_N apc).
  Let la : LaunchAuxv := launch_auxv inp sp mbase.
  Let top : word := ed_top rdraw.

  Hypothesis IMG : img_facts segs A ph.
  Hypothesis Hapc : Z.of_N apc = a_entry A.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Huid : valid_id uid.
  (* the zero-draw base [init_kn_zero]: FALSE on every real run *)
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).
  (* [Run.valid_input]'s [valid_launch] and [Run.valid_entry]'s fifth conjunct *)
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  (* THE KERNEL OF RECORD, and nothing more: [Run.valid_input]'s last clause
     ([Run.valid_input_recorded_kernel], LPS 75d69e00 Run.v:5666).  It fixes the eight
     single-answer fields (here: [kb_vdso] for the vDSO pair, [kb_cache] for the cache words)
     and leaves [kb_thp], [kb_aslr], [kb_guard], [kb_rnd_bits] and [kb_rseq] free.  It WAS
     [in_kernel inp = default_kernel], which [kb_rseq = false] refutes under [valid_input]. *)
  Hypothesis Hrec : in_kernel inp = recorded_kernel (in_kernel inp).
  (* [Run.valid_input_channel_reader] *)
  Hypothesis Hcr : in_channel_reader inp = true.

  (* for rewriting a model lemma's output into the names above *)
  Lemma inp_argv : in_argv inp = argv.                Proof. reflexivity. Qed.
  Lemma inp_envp : in_envp inp = envp.                Proof. reflexivity. Qed.
  Lemma inp_uid : in_uid inp = uid.                   Proof. reflexivity. Qed.
  Lemma inp_gid : in_gid inp = gid.                   Proof. reflexivity. Qed.
  Lemma inp_hwcap : in_hwcap inp = hw.                Proof. reflexivity. Qed.
  Lemma inp_execfn : in_execfn inp = execfn.          Proof. reflexivity. Qed.
  Lemma inp_rseq : kb_rseq (in_kernel inp) = rseq.    Proof. reflexivity. Qed.

  Lemma la_rseq_eq : la_rseq la = rseq.
  Proof. reflexivity. Qed.
  Lemma rz_range : 0 <= rseq_z rseq <= 1.
  Proof. exact (rseq_z_range rseq). Qed.
  (* the ONE place rseq is split: the launch's auxv has the CONFIG_RSEQ pair or not *)
  Lemma rz_case : (la_rseq la = true /\ rseq_z rseq = 1) \/ (la_rseq la = false /\ rseq_z rseq = 0).
  Proof. rewrite la_rseq_eq. unfold rseq. destruct (kb_rseq (in_kernel inp)); [left|right]; split; reflexivity. Qed.

  Let bsb := entry_stack_image inp mbase ph entryw sp rdraw.
  Let usp := bv_unsigned sp.
  Let utop := bv_unsigned top.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let L0 := Z.of_nat (length (nth 0 argv [])).
  Let L1 := Z.of_nat (length (nth 1 argv [])).
  Let G := Z.of_nat (block_items argv envp mod 2).
  Let CHEAD := Z.of_nat (block_head_size rseq argv envp).
  Let LSTR := Z.of_nat (launch_string_bytes argv envp execfn).
  Let W := Z.of_nat (block_pad_len rseq sp top argv envp execfn).
  Let STR0 := usp + CHEAD + W.

  (* [V_G] is valued [G + 4 * rseq_z rseq]: THE V_G FOLD (AsanPlanCore, at [V_G]) *)
  Definition vals0 : list word :=
    [Z_to_bv 64 (usp / 32768); Z_to_bv 64 argc; Z_to_bv 64 envc; Z_to_bv 64 L0; Z_to_bv 64 W;
     Z_to_bv 64 (bv_unsigned brk0 / 4096); Z_to_bv 64 ((usp mod 32768) / 16); Z_to_bv 64 L1; uid;
     Z_to_bv 64 (G + 4 * rseq_z rseq)].
  (* byte string [K_LA]: AT_SYSINFO_EHDR, AT_MINSIGSTKSZ, AT_HWCAP, the gid, AT_EXECFN *)
  Definition LAB : list byte :=
    word_to_le_bytes 8 (la_sysinfo_ehdr la) ++ word_to_le_bytes 8 (la_minsigstksz la)
    ++ word_to_le_bytes 8 hw ++ word_to_le_bytes 8 gid ++ word_to_le_bytes 8 (at_execfn_ptr top execfn).
  Definition E0 : env := Env (fun n => nth n vals0 (Z_to_bv 64 0))
                             (fun k => if Nat.eqb k K_RND then at_random_bytes (ed_random rdraw)
                                       else if Nat.eqb k K_LA then LAB else []).

  (* hidden argument bytes: the envp pointer array (with its NULL) and the
     string area at the top of the block, argv[0] at [STR0] up to ed_top *)
  Definition argH0 (E : env) (a : word) : bool :=
    let z := bv_unsigned a in
    (((usp + 8 * argc + 16 <=? z) && (z <? usp + 8 * argc + 8 * envc + 24))
     || ((STR0 <=? z) && (z <? utop)))%bool.

  Definition SINV0 (E : env) (M : word -> option byte) : Prop :=
    (forall n, (n < NX0)%nat -> ev E n = ev E0 n)
    /\ (forall a, argH0 E a = true -> M a = wrap_mem inp mbase ph entryw sp rdraw a).

  Lemma argH0_high : forall E a, argH0 E a = true -> CEIL <= bv_unsigned a.
  Proof.
    intros E a H. unfold argH0 in H. destruct Hsp as [Hlo _]. unfold sp_window_lo in Hlo. unfold CEIL.
    pose proof (valid_argv_len argv Hva).
    assert (HC : 0 <= CHEAD) by (unfold CHEAD; lia).
    assert (HW : 0 <= W) by (unfold W; lia).
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H _]; apply Z.leb_le in H;
      unfold usp, argc, envc, STR0 in *; lia.
  Qed.

  Lemma argH0_agree : forall E E' a, env_agree NX0 E E' -> argH0 E a = argH0 E' a.
  Proof. reflexivity. Qed.

  Lemma SINV0_frame : forall E M M', (forall a, argH0 E a = true -> M' a = M a) -> SINV0 E M -> SINV0 E M'.
  Proof. intros E M M' Hf [H1 H2]. split; [exact H1|]. intros a Ha. rewrite (Hf a Ha). apply H2. exact Ha. Qed.

  Lemma SINV0_agree : forall E E' M, env_agree NX0 E E' -> SINV0 E M -> SINV0 E' M.
  Proof.
    intros E E' M [Hag _] [H1 H2]. split; [|exact H2]. intros n Hn. rewrite <- (Hag n) by (unfold NX0 in *; lia). apply H1. exact Hn.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (* Layout arithmetic                                                        *)
  (* ----------------------------------------------------------------------- *)

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

  Lemma gap_range : 0 <= G <= 1.
  Proof. unfold G. pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia. Qed.

  (* THE AUXV'S SIZE AT THE RUN'S OWN FLAG.  The layout arithmetic below must hold
     for EITHER value of [kb_rseq], one of the five fields [Run.recorded_kernel]
     carries through untouched, so it reads the section's own [rseq].  The name is
     NOT [AUXSZ]: that is the plan core's function of [r] ([AsanPlanCore.AUXSZ]). *)
  Let AUXSZr : Z := Z.of_nat (auxv_size rseq).

  (* the same bound at this run's flag; the case split lives once, at
     [auxv_size_bounds] above, so nothing in the section destructs [rseq]. *)
  Lemma auxv_size_range : 432 <= AUXSZr <= 464.
  Proof. unfold AUXSZr. exact (auxv_size_bounds rseq). Qed.

  (* the plan side's bridge, SYMBOLIC in the flag: the plan's literal offset is
     [AUXSZ 0] and the other [32 * rseq_z rseq] bytes are in [V_G]'s value.  It WAS
     [auxv_size_pin : AUXSZr = AUXSZ], the pinned [default_kernel] size, which
     [kb_rseq = false] refutes (432 <> 464). *)
  Lemma auxv_size_rz : AUXSZr = 432 + 32 * rseq_z rseq.
  Proof. unfold AUXSZr. rewrite <- AUXSZ_of. reflexivity. Qed.

  (* C = 8*items + AUXSZr + 8*g + 16, with items = argc + envc + 3 *)
  Lemma chead_eq : CHEAD = 8 * argc + 8 * envc + AUXSZr + 40 + 8 * G.
  Proof.
    unfold CHEAD, G, argc, envc, block_head_size, block_items, AUXSZr. cbv zeta. lia.
  Qed.

  (* WAS [512 <= CHEAD <= 10752], which holds only at [rseq = true]: at
     [rseq = false, argc = 1, envc = 0, G = 0] the head is 8+0+40+0+432 = 480.
     The model states the same 480 ([theories/Common/AsanInit.v:296] at
     75d69e00).  The upper end does not move: [AUXSZr <= 464] is the old
     pinned value. *)
  Lemma chead_range : 480 <= CHEAD <= 10752.
  Proof.
    pose proof chead_eq. pose proof len_av. pose proof len_ev. pose proof gap_range.
    pose proof auxv_size_range. lia.
  Qed.

  (* L >= 2: the exec file name is non-empty ([Run.valid_execfn]) and has its NUL *)
  Lemma lstr_lo : 2 <= LSTR.
  Proof.
    unfold LSTR, launch_string_bytes.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
    pose proof (Nat2Z.is_nonneg (length execfn)).
    pose proof Hav0 as Hnz. unfold argv in *.
    destruct (in_argv inp) as [|a t] eqn:Ea; [cbn in Hnz; lia|].
    cbn [flatten_strings flat_map]. rewrite !length_app. cbn [length]. lia.
  Qed.

  (* argv[0] and its NUL are inside the string area *)
  Lemma s0_in_strings : L0 + 1 <= LSTR.
  Proof.
    unfold LSTR, launch_string_bytes, L0.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
    pose proof (Nat2Z.is_nonneg (length execfn)).
    pose proof Hav0 as Hnz. unfold argv in *.
    destruct (in_argv inp) as [|a t] eqn:Ea; [cbn in Hnz; lia|].
    cbn [flatten_strings flat_map nth]. rewrite !length_app. cbn [length]. lia.
  Qed.

  Lemma lstr_hi : LSTR + 8 * argc + 8 * envc <= 2097152.
  Proof.
    destruct Hlaunch as [_ Hb]. unfold launch_bytes, e2big_limit in Hb.
    unfold LSTR, argc, envc, argv, envp, execfn. lia.
  Qed.

  (* the pad [arch_align_stack] left: 0 .. 4110 *)
  Lemma pad_bounds_Z : 0 <= utop - 8 - LSTR - usp - CHEAD <= 4110.
  Proof.
    destruct Hlau as (_ & Hsw & _). destruct Hsw as (_ & Hslo & Hshi).
    unfold launch_sp_lo, launch_sp_hi, align_down16 in Hslo, Hshi.
    change (ed_top rdraw) with top in Hslo, Hshi.
    fold argv envp execfn rseq in Hslo, Hshi.
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

  (* WAS [8 * argc + 8 * envc + 514 <= ...], the [rseq = true] number
     (464 + 40 + 2 + 8).  Without CONFIG_RSEQ the head is 32 bytes shorter, so
     the bound for EVERY build is 482, which is what the model states
     ([theories/Common/AsanInit.v:387] at 75d69e00). *)
  Lemma bsb_ge : 8 * argc + 8 * envc + 482 <= Z.of_nat (length bsb).
  Proof.
    pose proof length_bsb_sum. pose proof chead_eq. pose proof lstr_lo. pose proof pad_range.
    pose proof gap_range. pose proof auxv_size_range. lia.
  Qed.

  Lemma str0_hi : STR0 + LSTR + 8 = utop.
  Proof. unfold STR0. pose proof pad_eq. lia. Qed.

  (* ----------------------------------------------------------------------- *)
  (* Denotations under [E0]                                                   *)
  (* ----------------------------------------------------------------------- *)

  Lemma brk_range : img_hi A <= bv_unsigned brk0 <= img_hi A + BRK_ASLR /\ bv_unsigned brk0 mod 4096 = 0.
  Proof.
    destruct Hbrk as (H1 & H2 & H3). unfold brk_aslr_max in H2. unfold page_size in H3.
    rewrite (if_top _ _ _ IMG) in H1, H2. unfold BRK_ASLR. lia.
  Qed.

  Lemma usp_hi : usp + 192 <= 2 ^ 47.
  Proof. pose proof usp_fit. pose proof bsb_ge. pose proof len_av. pose proof len_ev. lia. Qed.

  Lemma uE0 :
    uE E0 (EVar V_S1) = usp / 32768 /\ uE E0 (EVar V_S2) = (usp mod 32768) / 16
    /\ uE E0 (EVar V_ARGC) = argc /\ uE E0 (EVar V_ENVC) = envc /\ uE E0 (EVar V_L0) = L0
    /\ uE E0 (EVar V_W) = W /\ uE E0 (EVar V_BRK) = bv_unsigned brk0 / 4096
    /\ uE E0 (EVar V_G) = G + 4 * rseq_z rseq.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof gap_range. pose proof rz_range.
    pose proof (u64_range brk0) as [B1 B2].
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva ltac:(destruct Hva as [Hl _]; lia)). lia. }
    unfold uE. cbn [edenot E0 ev nth vals0 V_S1 V_S2 V_ARGC V_ENVC V_L0 V_W V_BRK V_G].
    rewrite !u64_lit by lia. repeat split; reflexivity.
  Qed.

  Lemma uE0_envc : uE E0 (EVar V_ENVC) = envc.
  Proof. destruct uE0 as (_ & _ & _ & H & _). exact H. Qed.

  Lemma uE0_argc : uE E0 (EVar V_ARGC) = argc.
  Proof. destruct uE0 as (_ & _ & H & _). exact H. Qed.

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

  (* the AT_RANDOM bytes sit [C - 16] above sp, at either flag: the plan's literal
     is [AUXSZ 0] = 432 and [V_G]'s value carries the other [32 * rseq_z rseq] bytes *)
  Lemma u_e_atrandom : uE E0 e_atrandom = usp + CHEAD - 16.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof gap_range. pose proof chead_eq. pose proof bsb_ge.
    pose proof auxv_size_rz. pose proof rz_range.
    destruct uE0 as (_ & _ & _ & _ & _ & _ & _ & U8).
    pose proof u_e_auxv as UA. unfold e_atrandom, AUXSZ, eadd, eaddz, escale, uE in *.
    rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UA, U8. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_str0 : uE E0 e_str0 = STR0.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof chead_eq. pose proof gap_range. pose proof bsb_ge. pose proof chead_range. pose proof auxv_size_range.
    pose proof length_bsb_sum. pose proof lstr_lo.
    destruct uE0 as (_ & _ & _ & _ & _ & U6 & _).
    pose proof u_e_atrandom as UA. unfold e_str0, eadd, eaddz, uE, STR0 in *.
    rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite UA, U6. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_str1 : uE E0 e_str1 = STR0 + L0 + 1.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof chead_eq. pose proof gap_range. pose proof bsb_ge. pose proof chead_range. pose proof auxv_size_range.
    pose proof length_bsb_sum. pose proof lstr_hi.
    destruct uE0 as (_ & _ & _ & _ & U5 & _).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    pose proof u_e_str0 as US. unfold e_str1, eadd, eaddz, uE, STR0 in *. rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite US, U5. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_atr8 : uE E0 e_atr8 = usp / 8 + argc + envc + G + 4 * rseq_z rseq.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof gap_range. pose proof rz_range.
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8). pose proof u_sp8 as U9.
    unfold e_atr8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia.
    rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit, !u_add64, !u_mul64, !u64_lit in U9 by lia.
    rewrite U1, U2, U3, U4, U8 in *. rewrite !Z.mod_small by lia. rewrite !Z.mod_small in U9 by lia. lia.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (* The initial configuration                                                *)
  (* ----------------------------------------------------------------------- *)

  Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.
  Definition FULL0 : word -> option byte := wrap_mem inp mbase ph entryw sp rdraw.
  (* [Run.init_config]'s model: [State.init_model] with the launch's vDSO draw *)
  Definition model0 : Model :=
    with_vdso (vdso_run_init (ed_vdso rdraw))
      (init_model (segments_reserved segs) brk0 mbase sp LIMIT inp).

  Let cs0 := init_acs_of (rseq_z rseq) A.
  Let cs0z := init_acs_of_zero (rseq_z rseq) A.
  Let hid0 := hid A argH0 E0 cs0 model0.
  Let Mr0 := Mr A argH0 E0 cs0 model0 FULL0.

  Lemma atop0 : alloc_top (m_vmmaps model0) = usp - 8388608.
  Proof. unfold alloc_top, stack_max_size. reflexivity. Qed.

  (* the launch's reserved ledger: the image's reservations AND the vDSO pair *)
  Let VTOP : Z :=
    page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)).
  Let RESX : list (word * word) := vdso_reserved (in_kernel inp) VTOP.

  Lemma model0_facts :
    m_halted model0 = None /\ m_fds model0 = fds_std /\ m_tid model0 = None
    /\ vm_reserved (m_vmmaps model0) = segments_reserved segs ++ RESX /\ vm_maps (m_vmmaps model0) = []
    /\ vm_noaccess (m_vmmaps model0) = [] /\ m_vm_lazy model0 = [] /\ m_vm_materialized model0 = []
    /\ vm_limit (m_vmmaps model0) = LIMIT /\ vm_brk (m_vmmaps model0) = brk0 /\ vm_start_brk (m_vmmaps model0) = brk0
    /\ vm_mmap_base (m_vmmaps model0) = mbase /\ eager_used model0 = 0.
  Proof.
    repeat split; reflexivity.
  Qed.

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

  (* the kernel of record's vDSO ([kb_vdso], fixed by [Run.recorded_kernel] at
     [State.default_kernel]'s value): four vvar pages, then two text pages *)
  Lemma resx_eq : RESX = [(Z_to_bv 64 (VTOP - 24576), Z_to_bv 64 16384);
                          (Z_to_bv 64 (VTOP - 24576 + 16384), Z_to_bv 64 8192)].
  Proof.
    pose proof vtop_range as [[T1 T2] T3].
    unfold RESX, vdso_reserved. rewrite Hrec. cbv zeta.
    replace (vdso_len (recorded_kernel (in_kernel inp))) with 24576 by (vm_compute; reflexivity).
    replace (vdso_vvar_pages * page_size)%Z with 16384 by (vm_compute; reflexivity).
    replace (vdso_text_pages (recorded_kernel (in_kernel inp)) * page_size)%Z with 8192 by (vm_compute; reflexivity).
    replace (VTOP - 24576 <? page_size)%Z with false
      by (symmetry; apply Z.ltb_ge; unfold page_size, mmap_base_min in *; lia).
    reflexivity.
  Qed.

  Lemma resx_len : (length RESX <= 2)%nat.
  Proof. rewrite resx_eq. cbn [length]. lia. Qed.

  Lemma resx_sum : sum_sizes RESX = 24576.
  Proof.
    pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
    rewrite resx_eq. cbn [sum_sizes fst snd].
    rewrite !u64_lit by (unfold mmap_base_min, mmap_base_max, sp_window_hi in *; lia). lia.
  Qed.

  Lemma resx_bytes_lo : 81920 <= resx_bytes A.
  Proof. unfold resx_bytes, p_resx. cbn. lia. Qed.

  (* the hidden set at start: the two argument-block regions; the hull and
     everything at/above the band floor are visible *)
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

  (* the zero window below sp: [StoreOk.stack_window_depth] = 6144513 bytes *)
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
  (* The knowledge [init_kn A] holds                                          *)
  (* ----------------------------------------------------------------------- *)

  Lemma argH0_range : forall a : word, argH0 E0 a = true ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 8 * envc + 24
    \/ STR0 <= bv_unsigned a < utop.
  Proof.
    intros a H. unfold argH0 in H.
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; [left|right]; lia.
  Qed.

  Lemma not_argH0 : forall a : word,
    (bv_unsigned a < usp + 8 * argc + 16 \/ (usp + 8 * argc + 8 * envc + 24 <= bv_unsigned a < STR0)
     \/ utop <= bv_unsigned a) -> argH0 E0 a = false.
  Proof.
    intros a H. destruct (argH0 E0 a) eqn:Ha; [|reflexivity]. apply argH0_range in Ha.
    pose proof len_av. pose proof len_ev. pose proof chead_eq. pose proof pad_range.
    pose proof gap_range. pose proof str0_hi. pose proof lstr_lo. pose proof auxv_size_range. unfold STR0 in *. lia.
  Qed.

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

  Let AUXW := auxv_words la ph entryw uid gid hw
                (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn).

  (* the 2 * (27 + 2r) auxv words (29 pairs under CONFIG_RSEQ, 27 without).  The
     bound WAS [j < 58], the CONFIG_RSEQ count, true only at [rseq = true]; it is
     now the run's own count, as the model's [RefLayout.read_auxv_word] states it. *)
  Lemma auxv_word_ok : forall (j : nat) v,
    (j < 2 * auxv_count rseq)%nat ->
    nth j AUXW (Z_to_bv 64 0) = edenot E0 v ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 v).
  Proof.
    intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum.
    pose proof lstr_lo. pose proof bsb_ge. pose proof chead_range.
    pose proof auxv_size_rz. pose proof rz_range. pose proof (auxv_count_rz rseq).
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
      pose proof (read_auxv_word segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi' j
                    ltac:(rewrite inp_rseq; exact Hj)) as RW.
      exact RW.
  Qed.

  Lemma auxw_ok : forall i ty v,
    (0 <= i <= 26 + 2 * rseq_z rseq) ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    nth (Z.to_nat (2 * i + 1)) AUXW (Z_to_bv 64 0) = edenot E0 v ->
    know_ok segs E0 Mr0 (auxw i ty v).
  Proof.
    intros i ty v Hi H1 H2. pose proof (auxv_count_rz rseq). pose proof rz_range. unfold auxw.
    constructor; [|constructor; [|constructor]].
    - replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia. apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
    - replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia. apply auxv_word_ok; [lia|]. exact H2.
  Qed.

  Lemma kr_ok : forall e lo hi, lo <= uE E0 e <= hi -> kentry_ok segs E0 Mr0 (KRange e lo hi).
  Proof. intros e lo hi H. cbn [kentry_ok]. unfold uE in H. exact H. Qed.

  Lemma Mr0_below : forall a : word, usp - 6144513 <= bv_unsigned a < usp -> Mr0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. pose proof usp_lo. pose proof len_av.
    rewrite Mr0_visible; [apply FULL0_below; exact Ha | unfold usp in *; lia | apply not_argH0; lia].
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
      rewrite <- Hv. apply RW. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
  Qed.

  (* argv[0] is at the bottom of the string area *)
  Lemma cat_argv0_eq :
    bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) = STR0.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof chead_range. pose proof auxv_size_range.
    rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0 Hav0).
    change (total_arg_bytes_nat (firstn 0 (in_argv inp))) with 0%nat.
    rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
    fold argv envp execfn rseq. change (ed_top rdraw) with top.
    unfold STR0, CHEAD, W, usp, cat_string_off in *.
    rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia.
  Qed.

  (* argv[1] follows argv[0] and its NUL *)
  Lemma cat_argv1_eq : (1 < length argv)%nat ->
    bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1) = STR0 + L0 + 1.
  Proof.
    intros Hav1.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof chead_range. pose proof auxv_size_range.
    pose proof s0_in_strings. pose proof lstr_hi.
    assert (TF : forall l : list (list byte), (0 < length l)%nat ->
                  Z.of_nat (total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1)
      by (intros [|x t] Hl; [cbn in Hl; lia|]; change (firstn 1 (x :: t)) with [x]; cbn -[Z.of_nat Z.add]; lia).
    pose proof (TF argv Hav0) as TF0.
    rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1 Hav1).
    rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
    fold argv envp execfn rseq. change (ed_top rdraw) with top.
    unfold STR0, CHEAD, W, usp, L0, cat_string_off in *.
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

  (* the word at sp0+16: argv[1] or the argv NULL *)
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
        { apply bv_eq. rewrite (cat_argv1_eq Hav1). pose proof u_e_str1 as U. unfold uE in U. rewrite U. reflexivity. }
        rewrite <- Hv. apply RW; [exact Hav1|]. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
      + apply Z.ltb_ge in Hc. assert (Hav1 : length argv = 1%nat) by (unfold argc in Hc; pose proof Hav0; lia).
        pose proof (read_argv_null segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as RW.
        fold argv in RW. rewrite Hav1 in RW.
        exact RW.
  Qed.

  (* THE DEFAULT: the AT_RANDOM block is byte string [K_RND] = the draw *)
  Lemma atrandom_ok : kentry_ok segs E0 Mr0 (KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof lstr_lo.
    pose proof chead_range. pose proof auxv_size_rz. pose proof rz_range.
    assert (Hab : split_lit e_atrandom = (fst e_atrb, snd e_atrb)) by (unfold e_atrb; destruct (split_lit e_atrandom); reflexivity).
    set (ab := fst e_atrb) in *. set (ak := snd e_atrb) in *.
    pose proof (split_u E0 e_atrandom ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    (* the literal part of [e_atrandom] is 24 + [AUXSZ 0], the same at either flag *)
    assert (Hak : ak = 456) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + CHEAD - 16) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl.
    assert (HE : eb E0 K_RND = at_random_bytes (ed_random rdraw)) by reflexivity.
    rewrite HE.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    split; [rewrite length_at_random_bytes; reflexivity|].
    intros i Hi.
    destruct (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as [off (Hp & Hoff & Hmod & Hrd)].
    fold argv envp rseq in Hp, Hoff, Hrd.
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

  (* ZERO DRAW: the zero entry, under the (false) zero-draw hypothesis *)
  Lemma atrandom_zero_ok : kentry_ok segs E0 Mr0 (KZero (SA (fst e_atrb) (snd e_atrb)) (ELit 16)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof lstr_lo.
    pose proof chead_range. pose proof auxv_size_rz. pose proof rz_range.
    assert (Hab : split_lit e_atrandom = (fst e_atrb, snd e_atrb)) by (unfold e_atrb; destruct (split_lit e_atrandom); reflexivity).
    set (ab := fst e_atrb) in *. set (ak := snd e_atrb) in *.
    pose proof (split_u E0 e_atrandom ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    (* the literal part of [e_atrandom] is 24 + [AUXSZ 0], the same at either flag *)
    assert (Hak : ak = 456) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + CHEAD - 16) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    intros i Hi.
    destruct (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as [off (Hp & Hoff & Hmod & Hrd)].
    fold argv envp rseq in Hp, Hoff, Hrd.
    assert (Hu : bv_unsigned (at_random_ptr sp rseq argv envp) = usp + CHEAD - 16).
    { rewrite Hp, word_add_nat, u64_lit by (unfold usp in *; lia). unfold CHEAD. lia. }
    specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold bsb in Hrd.
    pose proof Hzr as Hz0. unfold AsanCeil.zero_random_draw in Hz0.
    rewrite Hz0, AsanCeil.at_random_bytes_zero, repeat_firstn_skipn in Hrd by lia.
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
    pose proof (if_rw _ _ _ IMG) as ((R1 & R0 & R2) & R3).
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
    pose proof usp_lo. pose proof usp_fit. pose proof chead_eq. pose proof gap_range.
    pose proof len_av. pose proof len_ev. pose proof bsb_ge. pose proof chead_range. pose proof auxv_size_range.
    destruct (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as [off (Hp & Hoff & _ & _)].
    fold argv envp rseq in Hp, Hoff.
    apply bv_eq. rewrite Hp, word_add_nat, u64_lit by (unfold CHEAD, usp in *; lia).
    pose proof u_e_atrandom as U. unfold uE in U. rewrite U. unfold CHEAD, usp. lia.
  Qed.

  (* the launch words of byte string [K_LA] *)
  Lemma eb_LA : eb E0 K_LA = LAB.
  Proof. reflexivity. Qed.

  Lemma la_w0 : la_sysinfo_ehdr la = edenot E0 (la_word 0).
  Proof. symmetry. unfold la_word; cbn [edenot]. rewrite eb_LA. unfold LAB. change (8 * 0)%Z with 0%Z. apply blob0. Qed.
  Lemma la_w1 : la_minsigstksz la = edenot E0 (la_word 1).
  Proof. symmetry. unfold la_word; cbn [edenot]. rewrite eb_LA. unfold LAB. change (8 * 1)%Z with (8 + 0)%Z.
    rewrite blob_skip by (first [apply length_N_to_le_bytes | lia]). apply blob0. Qed.
  Lemma la_w2 : hw = edenot E0 (la_word 2).
  Proof. symmetry. unfold la_word; cbn [edenot]. rewrite eb_LA. unfold LAB. change (8 * 2)%Z with (8 + (8 + 0))%Z.
    rewrite blob_skip by (first [apply length_N_to_le_bytes | lia]).
    rewrite blob_skip by (first [apply length_N_to_le_bytes | lia]). apply blob0. Qed.
  Lemma la_w3 : gid = edenot E0 (la_word 3).
  Proof. symmetry. unfold la_word; cbn [edenot]. rewrite eb_LA. unfold LAB. change (8 * 3)%Z with (8 + (8 + (8 + 0)))%Z.
    rewrite blob_skip by (first [apply length_N_to_le_bytes | lia]).
    rewrite blob_skip by (first [apply length_N_to_le_bytes | lia]).
    rewrite blob_skip by (first [apply length_N_to_le_bytes | lia]). apply blob0. Qed.
  Lemma la_w4 : at_execfn_ptr top execfn = edenot E0 (la_word 4).
  Proof. symmetry. unfold la_word; cbn [edenot]. rewrite eb_LA. unfold LAB. change (8 * 4)%Z with (8 + (8 + (8 + (8 + 0))))%Z.
    rewrite blob_skip by (first [apply length_N_to_le_bytes | lia]).
    rewrite blob_skip by (first [apply length_N_to_le_bytes | lia]).
    rewrite blob_skip by (first [apply length_N_to_le_bytes | lia]).
    rewrite blob_skip by (first [apply length_N_to_le_bytes | lia]).
    rewrite <- (app_nil_r (word_to_le_bytes 8 (at_execfn_ptr top execfn))). apply blob0. Qed.

  (* the eight cache words of the kernel of record ([kb_cache], fixed by
     [Run.recorded_kernel] at [State.default_kernel]'s value) *)
  Lemma cw_ok : forall f : CacheWords -> word, f (la_cache la) = edenot E0 (ELit (cw_z f)).
  Proof.
    intros f. unfold la, launch_auxv. cbn [la_cache]. rewrite Hrec. unfold cw_z. rewrite edenot_lit.
    change (launch_cache_words (recorded_kernel (in_kernel inp))) with (launch_cache_words default_kernel).
    symmetry. apply Z_to_bv_bv_unsigned.
  Qed.

  Lemma entry_ok : entryw = edenot E0 (ELit (a_entry A)).
  Proof. unfold entryw. rewrite edenot_lit, Hapc. reflexivity. Qed.

  (* [Hla] is one branch of [rz_case]: [la_rseq la = true] or [= false] *)
  Ltac aux_nth Hla :=
    unfold AUXW, auxv_words, auxv_entries; rewrite Hla;
    cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul].

  Lemma init_kn_with_ok : forall atr, kentry_ok segs E0 Mr0 atr -> know_ok segs E0 Mr0 (init_kn_with (rseq_z rseq) atr A).
  Proof.
    intros atr Hatr.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof gap_range. pose proof chead_eq. pose proof length_bsb_sum. pose proof lstr_lo.
    pose proof brk_range as [B1 B2]. pose proof bsb_ge. pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    pose proof (if_ph _ _ _ IMG) as (P1 & P2 & P3). pose proof chead_range.
    pose proof auxv_size_rz. pose proof rz_range. pose proof usp_al.
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
      (* [Huid] and [u64_range uid] are stated over [uid]; unfolding it in the
         goal alone leaves [bv_unsigned (in_uid inp)] there, which [zify] reads
         as a second atom carrying no bound. *)
      apply Forall_cons; [apply kr_ok; rewrite uE0_uid; unfold valid_id in Huid; pose proof (u64_range uid); lia|].
      apply Forall_cons; [apply kr_ok; rewrite U8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U6; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U7; unfold BRK_ASLR in *; lia|].
      apply Forall_cons; [exact SW1|].
      apply Forall_cons; [exact SW2|].
      apply Forall_cons; [exact argc_word_ok|].
      apply Forall_cons; [exact argv0_word_ok|].
      apply Forall_cons; [exact argv1_word_ok|].
      apply Forall_nil. }
    (* the ONE split on rseq: each branch's claim list is concrete *)
    destruct rz_case as [[Hla Hr]|[Hla Hr]]; rewrite Hr; cbn [Z.eqb Pos.eqb].
    - (* CONFIG_RSEQ: 29 pairs, AT_NULL at pair 28 *)
      repeat (apply Forall_app; split).
      all: try (apply auxw_ok; [lia | aux_nth Hla; reflexivity | aux_nth Hla]).
      (* AT_SYSINFO_EHDR *) 1: exact la_w0.
      (* the eight cache words *) 1-8: apply cw_ok.
      (* AT_MINSIGSTKSZ, AT_HWCAP *) 1: exact la_w1. 1: exact la_w2.
      (* AT_PAGESZ, AT_CLKTCK *) 1-2: reflexivity.
      (* AT_PHDR, AT_PHENT, AT_PHNUM *)
      1: rewrite edenot_lit, P1; reflexivity.
      1: rewrite edenot_lit, P2; reflexivity.
      1: rewrite edenot_lit, P3; reflexivity.
      (* AT_BASE, AT_FLAGS *) 1-2: reflexivity.
      (* AT_ENTRY *) 1: exact entry_ok.
      (* AT_UID, AT_EUID *) 1-2: reflexivity.
      (* AT_GID, AT_EGID *) 1-2: exact la_w3.
      (* AT_SECURE *) 1: reflexivity.
      (* AT_RANDOM *) 1: exact atr_ptr_eq.
      (* AT_EXECFN *) 1: exact la_w4.
      (* AT_RSEQ_FEATURE_SIZE, AT_RSEQ_ALIGN, AT_NULL *) 1-3: reflexivity.
      apply Forall_cons; [exact Hatr|].
      apply Forall_cons; [exact kimg_ok|].
      apply Forall_cons; [exact rw_window_ok|].
      apply Forall_nil.
    - (* no CONFIG_RSEQ: 27 pairs, AT_NULL at pair 26; the empty rseq-pair list
         leaves a [[] ++ _] to drop first *)
      rewrite app_nil_l.
      repeat (apply Forall_app; split).
      all: try (apply auxw_ok; [lia | aux_nth Hla; reflexivity | aux_nth Hla]).
      (* AT_SYSINFO_EHDR *) 1: exact la_w0.
      (* the eight cache words *) 1-8: apply cw_ok.
      (* AT_MINSIGSTKSZ, AT_HWCAP *) 1: exact la_w1. 1: exact la_w2.
      (* AT_PAGESZ, AT_CLKTCK *) 1-2: reflexivity.
      (* AT_PHDR, AT_PHENT, AT_PHNUM *)
      1: rewrite edenot_lit, P1; reflexivity.
      1: rewrite edenot_lit, P2; reflexivity.
      1: rewrite edenot_lit, P3; reflexivity.
      (* AT_BASE, AT_FLAGS *) 1-2: reflexivity.
      (* AT_ENTRY *) 1: exact entry_ok.
      (* AT_UID, AT_EUID *) 1-2: reflexivity.
      (* AT_GID, AT_EGID *) 1-2: exact la_w3.
      (* AT_SECURE *) 1: reflexivity.
      (* AT_RANDOM *) 1: exact atr_ptr_eq.
      (* AT_EXECFN *) 1: exact la_w4.
      (* AT_NULL *) 1: reflexivity.
      apply Forall_cons; [exact Hatr|].
      apply Forall_cons; [exact kimg_ok|].
      apply Forall_cons; [exact rw_window_ok|].
      apply Forall_nil.
  Qed.

  Lemma init_kn_ok : know_ok segs E0 Mr0 (init_kn (rseq_z rseq) A).
  Proof. exact (init_kn_with_ok _ atrandom_ok). Qed.
  (* ZERO DRAW (under the zero-draw hypothesis) *)
  Lemma init_kn_zero_ok : know_ok segs E0 Mr0 (init_kn_zero (rseq_z rseq) A).
  Proof. exact (init_kn_with_ok _ atrandom_zero_ok). Qed.

  (* ----------------------------------------------------------------------- *)
  (* The initial [cs_ok] and the initial configuration                        *)
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

  (* the three ledger goals: [co_res] (packed), [co_totsz], [co_split] *)
  Lemma init_co_res :
    (exists rx : list (word * word),
       vm_reserved (m_vmmaps model0) = segments_reserved segs ++ rx
       /\ Forall (resx_entry_ok A) rx
       /\ (length rx <= n_resx A)%nat
       /\ sum_sizes rx <= resx_bytes A)
    /\ Forall (fun iv => Forall (iv_disjoint iv) (vm_reserved (m_vmmaps model0))) (vm_maps (m_vmmaps model0))
    /\ incl (vdso_reserved (m_kernel model0) (vdso_top (m_vmmaps model0))) (vm_reserved (m_vmmaps model0)).
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & _).
    pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
    pose proof (if_hull _ _ _ IMG) as (G1 & G2 & G3 & G4). pose proof resx_bytes_lo.
    split; [|split].
    - exists RESX. split; [exact M4|].
      split; [| split; [pose proof resx_len; unfold n_resx; lia | rewrite resx_sum; lia]].
      rewrite resx_eq. unfold resx_entry_ok. repeat constructor;
        cbn [fst snd];
        rewrite !u64_lit
          by (unfold mmap_base_min, mmap_base_max, sp_window_hi in *; lia);
        unfold KHI, mmap_base_min, mmap_base_max, sp_window_hi in *; lia.
    - rewrite M5. constructor.
    - replace (m_kernel model0) with (in_kernel inp) by reflexivity.
      replace (vdso_top (m_vmmaps model0)) with VTOP
        by (symmetry; exact (vdso_top_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp)).
      rewrite M4. apply incl_appr, incl_refl.
  Qed.

  Lemma init_co_totsz : sum_sizes (vm_reserved (m_vmmaps model0) ++ vm_maps (m_vmmaps model0)) <= img_hi A - img_lo A + resx_bytes A.
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & _). rewrite M4, M5.
    rewrite app_nil_r, sum_sizes_app, (if_sizes _ _ _ IMG), resx_sum.
    pose proof resx_bytes_lo. lia.
  Qed.

  (* [co_split]'s high mark is the vDSO pair's BASE *)
  Lemma init_co_split : exists Y, KHI <= Y /\ Y mod 4096 = 0 /\ Y <= bv_unsigned (vm_mmap_base (m_vmmaps model0))
                       /\ ledger_split (vm_reserved (m_vmmaps model0) ++ vm_maps (m_vmmaps model0)) kHighMemBeg Y.
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
    pose proof (if_hull _ _ _ IMG) as (G1 & G2 & G3 & G4).
    exists (VTOP - 24576). rewrite M12, M4, M5.
    unfold KHI, mmap_base_min, mmap_base_max, sp_window_hi in *.
    split; [lia|]. split; [lia|]. split; [lia|].
    rewrite app_nil_r. intros b sz Hin. apply in_app_or in Hin as [Hin|Hin].
    + pose proof (proj1 (Forall_forall _ _) (if_res _ _ _ IMG) _ Hin) as [R1 R2]. cbn [fst snd] in R1, R2.
      left. unfold kHighMemBeg. lia.
    + right. rewrite resx_eq in Hin. cbn [In] in Hin.
      destruct Hin as [E|[E|[]]]; inversion E; subst; cbn [fst];
        rewrite u64_lit by lia; lia.
  Qed.

  Theorem init_cs_ok : cs_ok segs A NX0 LIMIT SINV0 argH0 (in_fs inp) E0 cs0 R0 FULL0 model0.
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
    destruct abytes_init as [AB1 AB2].
    constructor; cbn [cs0 init_acs_of init_acs_of_with a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
      rewrite ?M1, ?M2, ?M3, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
    - exact init_regs_ok.
    - reflexivity.
    - exact init_kn_ok.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - (* co_res: the image's reservations, the vDSO pair, no tracked maps *)
      pose proof init_co_res as HR. rewrite ?M5 in HR. exact HR.
    - reflexivity.
    - reflexivity.
    - constructor.
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      exact (init_sp_ok_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp Hsp).
    - constructor.
    - constructor.
    - intros z Hz. exact Hz.
    - constructor.
    - constructor.
    - pose proof init_co_totsz as HT. rewrite M5 in HT. exact HT.
    - pose proof init_co_split as HS. rewrite M12, M5 in HS. exact HS.
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7 & _). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.
    - lia.
    - lia.
    - exact AB1.
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
    - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
    - split; [intros; reflexivity | intros; reflexivity].
    - intros E' Hag. change (vm_init_sp (m_vmmaps model0)) with sp.
      split; [|destruct Hsp as (_ & Hhi & _); exact Hhi].
      unfold uE. erewrite <- (APS.edenot_agree' NX0 E0 E' e_sp0 Hag); [rewrite edenot_e_sp0; reflexivity | reflexivity].
    - intros a Ha. rewrite atop0. unfold argH0 in Ha. pose proof len_av. pose proof len_ev.
      assert (HC : 0 <= CHEAD) by (unfold CHEAD; lia). assert (HW : 0 <= W) by (unfold W; lia).
      apply orb_prop in Ha as [Ha|Ha]; apply andb_prop in Ha as [Ha _]; apply Z.leb_le in Ha; unfold usp, argc, envc, STR0 in *; lia.
    - intros iv Hiv _. rewrite M7 in Hiv. destruct Hiv.
    - rewrite ?M6. apply Forall_nil.
    - exact Hcr.
  Qed.

  (* ZERO DRAW: the same configuration over [init_kn_zero] *)
  Theorem init_cs_ok_zero : cs_ok segs A NX0 LIMIT SINV0 argH0 (in_fs inp) E0 cs0z R0 FULL0 model0.
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
    destruct abytes_init as [AB1 AB2].
    change (allowA A E0 cs0) with (allowA A E0 (init_acs_of_zero (rseq_z rseq) A)) in AB1.
    constructor; unfold cs0z; cbn [init_acs_of_zero init_acs_of_with a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
      rewrite ?M1, ?M2, ?M3, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
    - exact init_regs_ok.
    - reflexivity.
    - exact init_kn_zero_ok.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - pose proof init_co_res as HR. rewrite ?M5 in HR. exact HR.
    - reflexivity.
    - reflexivity.
    - constructor.
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      exact (init_sp_ok_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp Hsp).
    - constructor.
    - constructor.
    - intros z Hz. exact Hz.
    - constructor.
    - constructor.
    - pose proof init_co_totsz as HT. rewrite M5 in HT. exact HT.
    - pose proof init_co_split as HS. rewrite M12, M5 in HS. exact HS.
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7 & _). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.
    - lia.
    - lia.
    - exact AB1.
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
    - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
    - split; [intros; reflexivity | intros; reflexivity].
    - intros E' Hag. change (vm_init_sp (m_vmmaps model0)) with sp.
      split; [|destruct Hsp as (_ & Hhi & _); exact Hhi].
      unfold uE. erewrite <- (APS.edenot_agree' NX0 E0 E' e_sp0 Hag); [rewrite edenot_e_sp0; reflexivity | reflexivity].
    - intros a Ha. rewrite atop0. unfold argH0 in Ha. pose proof len_av. pose proof len_ev.
      assert (HC : 0 <= CHEAD) by (unfold CHEAD; lia). assert (HW : 0 <= W) by (unfold W; lia).
      apply orb_prop in Ha as [Ha|Ha]; apply andb_prop in Ha as [Ha _]; apply Z.leb_le in Ha; unfold usp, argc, envc, STR0 in *; lia.
    - intros iv Hiv _. rewrite M7 in Hiv. destruct Hiv.
    - rewrite ?M6. apply Forall_nil.
    - exact Hcr.
  Qed.

  (* [Run.init_config] is the configuration [cs_ok] speaks about, over any
     segment list with the image's reservations (the run's list,
     [Run.run_segments], appends only the vDSO pair, which reserves nothing) *)
  Theorem init_cfg_eq_segs : forall rsegs, segments_reserved rsegs = segments_reserved segs ->
    init_config rsegs apc ph sp brk0 mbase rdraw LIMIT inp = cfg_of rsegs R0 (a_entry A) FULL0 model0.
  Proof.
    intros rsegs Hr. unfold init_config, cfg_of, FULL0, model0, entryw. rewrite init_mkst, Hapc, Hr. reflexivity.
  Qed.

  Theorem init_cfg_eq :
    init_config segs apc ph sp brk0 mbase rdraw LIMIT inp = cfg_of segs R0 (a_entry A) FULL0 model0.
  Proof. exact (init_cfg_eq_segs segs eq_refl). Qed.
End Init.
