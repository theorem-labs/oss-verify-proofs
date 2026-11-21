(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's vDSO pair; the stack window below sp; the 27- or 29-pair auxv; the launch's input, mmap base and entry draw; the CONFIG_RSEQ value; the start state's range of AT_RANDOM's masked ASan shadow index; the launch's reader of the standard channels); and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import
  PropExec CatExec CatSim SeqExec StoreOk StreamSim StepTac ShapeAlg AgentLib StartupAux RefLayout ArgvEnv
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan AsanPlanSound.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanCeil.

Unset Lia Cache.
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

(* the initial stack image runs from the entry stack pointer to the stack VMA's end *)
Definition stack_image_size (sp top : word) : Z :=
  (bv_unsigned top - bv_unsigned sp)%Z.

(* AT_NULL closes the vector: pair 28 with CONFIG_RSEQ, pair 26 without *)
Lemma auxv_words_null : forall la ph entry uid gid hw ar ae,
  nth (Z.to_nat (2 * (26 + 2 * rseq_z (la_rseq la))))
      (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0
  /\ nth (Z.to_nat (2 * (26 + 2 * rseq_z (la_rseq la)) + 1))
         (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. intros [ehdr c msz [|]] ph entry uid gid hw ar ae; split; reflexivity. Qed.

(* with CONFIG_RSEQ, pairs 26 and 27 are AT_RSEQ_FEATURE_SIZE = 28 and AT_RSEQ_ALIGN = 32 *)
Lemma auxv_words_rseq : forall la ph entry uid gid hw ar ae, la_rseq la = true ->
  nth 52 (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 27
  /\ nth 53 (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 28
  /\ nth 54 (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 28
  /\ nth 55 (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 32.
Proof.
  intros [ehdr c msz [|]] ph entry uid gid hw ar ae H; [repeat split; reflexivity | discriminate H].
Qed.

(* the AT_RANDOM block's literal offset from its base: the 24 bytes of argc and the two NULLs
   plus the auxv, under both layouts *)
Lemma e_atrb_off : forall b, snd (e_atrb (rseq_z b)) = 24 + AUXSZ (rseq_z b).
Proof. intros [|]; vm_compute; reflexivity. Qed.

Lemma sum_sizes_app : forall l1 l2, sum_sizes (l1 ++ l2) = sum_sizes l1 + sum_sizes l2.
Proof.
  induction l1 as [|iv l1 IH]; intro l2; cbn [app sum_sizes]; [lia|]. rewrite IH. lia.
Qed.

Section Init.
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  (* the image's ELF entry: [Run.init_config]'s pc, and the auxv's AT_ENTRY *)
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable inp : ProcInput.

  Hypothesis IMG : img_facts segs A ph.
  Hypothesis Hapc : Z.of_N apc = a_entry A.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hgid : valid_id (in_gid inp).
  Hypothesis Hhw : valid_hwcap (in_hwcap inp).
  (* [Run.valid_input]'s [valid_launch] and [Run.valid_entry]'s fifth conjunct: the start state is
     exactly a Linux launch, which pins the stack VMA's end, the entry stack pointer inside the
     [arch_align_stack] window and the mmap base *)
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  (* [Run.valid_input]'s last conjunct: the kernel build is a recorded one, so its vDSO is the
     default build's *)
  Hypothesis Hkern : in_kernel inp = recorded_kernel (in_kernel inp).
  (* the table's bounds on what the launch reserves beside the image (the vDSO pair) *)
  Hypothesis Hresx : (2 <= n_resx A)%nat /\ (20 <= p_resx A)%nat.
  (* [Run.valid_input]'s channel-reader fact (LPS 727298f3): the standard channels have a reader *)
  Hypothesis Hrdr : in_channel_reader inp = true.

  #[local] Notation argv := (in_argv inp).
  #[local] Notation envp := (in_envp inp).
  #[local] Notation uid := (in_uid inp).
  #[local] Notation gid := (in_gid inp).
  #[local] Notation hw := (in_hwcap inp).
  #[local] Notation execfn := (in_execfn inp).
  #[local] Notation rseq := (kb_rseq (in_kernel inp)).
  #[local] Notation entryw := (Z_to_bv 64 (Z.of_N apc)).
  #[local] Notation la := (launch_auxv inp sp mbase).
  #[local] Notation top := (ed_top rdraw).

  Let RZ : Z := rseq_z rseq.

  Lemma RZ_range : 0 <= RZ <= 1.
  Proof. exact (rseq_z_range rseq). Qed.

  (* the vector's length, the one case split on the flag that the layout arithmetic needs *)
  Lemma auxv_count_RZ : Z.of_nat (auxv_count rseq) = 27 + 2 * RZ.
  Proof. unfold RZ, rseq_z, auxv_count. destruct (kb_rseq (in_kernel inp)); reflexivity. Qed.

  Let bsb := entry_stack_image inp mbase ph entryw sp rdraw.
  Let usp := bv_unsigned sp.
  Let utop := bv_unsigned top.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let L0 := Z.of_nat (length (nth 0 argv [])).
  Let L1 := Z.of_nat (length (nth 1 argv [])).
  (* [StackLayout.block_items mod 2]: [STACK_ROUND]'s 8-byte gap, in words *)
  Let G := Z.of_nat (block_items argv envp mod 2).
  (* C, sp to the top of the AT_RANDOM bytes *)
  Let CHEAD := Z.of_nat (block_head_size rseq argv envp).
  (* L, the string bytes with their NULs, the exec file name included *)
  Let LSTR := Z.of_nat (launch_string_bytes argv envp execfn).
  (* the [arch_align_stack] pad between the AT_RANDOM bytes and argv[0] *)
  Let W := Z.of_nat (block_pad_len rseq sp top argv envp execfn).
  (* argv[0]'s first byte *)
  Let STR0 := usp + CHEAD + W.

  Definition vals0 : list word :=
    [Z_to_bv 64 (usp / 32768); Z_to_bv 64 argc; Z_to_bv 64 envc; Z_to_bv 64 L0; Z_to_bv 64 W;
     Z_to_bv 64 (bv_unsigned brk0 / 4096); Z_to_bv 64 ((usp mod 4096) / 16); Z_to_bv 64 L1; uid; hw;
     Z_to_bv 64 ((usp mod 32768) / 4096); Z_to_bv 64 G; gid].

  Definition E0 : env := Env (fun n => nth n vals0 (Z_to_bv 64 0))
                             (fun k => if Nat.eqb k K_RND then at_random_bytes (ed_random rdraw) else []).

  (* hidden argument bytes: the envp pointer array (with its NULL) and the string area, which
     runs from argv[0] to the stack VMA's end *)
  Definition argH0 (E : env) (a : word) : bool :=
    let z := bv_unsigned a in
    (((usp + 8 * argc + 16 <=? z) && (z <? usp + 8 * argc + 8 * envc + 24))
     || ((STR0 <=? z) && (z <? utop)))%bool.

  Definition FULL0 : word -> option byte := wrap_mem inp mbase ph entryw sp rdraw.

  Definition SINV0 (E : env) (M : word -> option byte) : Prop :=
    (forall n, (n < NX0)%nat -> ev E n = ev E0 n)
    /\ (forall a, argH0 E a = true -> M a = FULL0 a).

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

  (* C = 8*items + AUXSZ RZ + 8*g + 16, with items = argc + envc + 3 *)
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

  (* argv[0] and its NUL are inside the string area, and the exec name's NUL after them *)
  Lemma s0_in_strings : L0 + 2 <= LSTR.
  Proof.
    unfold LSTR, launch_string_bytes, L0.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
    pose proof (Nat2Z.is_nonneg (length execfn)).
    pose proof Hav0 as Hnz. revert Hnz.
    destruct (in_argv inp) as [|a t]; intros Hnz; [cbn in Hnz; lia|].
    cbn [flatten_strings flat_map nth]. rewrite !length_app. cbn [length]. lia.
  Qed.

  Lemma lstr_lo : 2 <= LSTR.
  Proof. pose proof s0_in_strings. unfold L0 in *. lia. Qed.

  (* [Run.valid_launch]'s E2BIG half *)
  Lemma lstr_hi : LSTR + 8 * argc + 8 * envc <= 2097152.
  Proof.
    destruct Hlaunch as [_ Hb]. unfold launch_bytes, e2big_limit in Hb.
    unfold LSTR, argc, envc. lia.
  Qed.

  (* the pad [arch_align_stack] left: [r] in 0..4095 plus the remainder the low-four-bit mask
     leaves *)
  Lemma pad_bounds_Z : 0 <= utop - 8 - LSTR - usp - CHEAD <= 4110.
  Proof.
    destruct Hlau as (_ & Hsw & _). destruct Hsw as (_ & Hslo & Hshi).
    unfold launch_sp_lo, launch_sp_hi, align_down16 in Hslo, Hshi.
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
    unfold entry_page_top, va_stack_top, sp_window_hi in H. fold utop in H. lia.
  Qed.

  (* the pointer vector, the auxv (at least 432 bytes), the gap, the random bytes, the pad, the
     strings (at least 2 bytes) and the eight-byte slot *)
  Lemma bsb_ge : 8 * argc + 8 * envc + 482 <= Z.of_nat (length bsb).
  Proof.
    pose proof length_bsb_sum. pose proof chead_eq. pose proof lstr_lo. pose proof pad_range.
    pose proof gap_range. pose proof RZ_range. lia.
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

  Lemma L0_range : 0 <= L0 <= 131071.
  Proof. unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. Qed.

  Lemma uE0 :
    uE E0 (EVar V_S1) = usp / 32768 /\ uE E0 (EVar V_S2) = (usp mod 4096) / 16
    /\ uE E0 (EVar V_ARGC) = argc /\ uE E0 (EVar V_ENVC) = envc /\ uE E0 (EVar V_L0) = L0
    /\ uE E0 (EVar V_W) = W /\ uE E0 (EVar V_BRK) = bv_unsigned brk0 / 4096
    /\ uE E0 (EVar V_G) = G.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof gap_range. pose proof L0_range.
    pose proof (u64_range brk0) as [B1 B2].
    unfold uE. cbn [edenot E0 ev nth vals0 V_S1 V_S2 V_ARGC V_ENVC V_L0 V_W V_BRK V_G].
    rewrite !u64_lit by lia. repeat split; reflexivity.
  Qed.

  Lemma uE0_envc : uE E0 (EVar V_ENVC) = envc.
  Proof. destruct uE0 as (_ & _ & _ & H & _). exact H. Qed.

  Lemma uE0_sp : uE E0 (EVar V_SP) = (usp mod 32768) / 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. unfold uE. cbn [edenot E0 ev nth vals0 V_SP]. rewrite u64_lit by lia. reflexivity.
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
  Lemma uE0_hw : uE E0 (EVar V_HW) = bv_unsigned hw.
  Proof. reflexivity. Qed.
  Lemma uE0_gid : uE E0 (EVar V_GID) = bv_unsigned gid.
  Proof. reflexivity. Qed.

  Lemma hw_range : 0 <= bv_unsigned hw <= 0x3FFFFF.
  Proof. destruct Hhw as [Eh | Eh]; rewrite Eh; (split; [apply bv_unsigned_in_range|]); vm_compute; intros H; discriminate H. Qed.

  Lemma u_e_sp0 : uE E0 e_sp0 = usp.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _). pose proof uE0_sp as U9.
    unfold e_sp0, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2, U9.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_pd : uE E0 e_pd = usp - usp mod 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & _). pose proof uE0_sp as U9.
    unfold e_pd, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U9.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma edenot_e_sp0 : edenot E0 e_sp0 = sp.
  Proof. apply bv_eq. exact u_e_sp0. Qed.

  Lemma argH0_high : forall E a, argH0 E a = true -> CEIL <= bv_unsigned a.
  Proof.
    intros E a H. unfold argH0 in H. pose proof usp_lo. unfold CEIL.
    assert (HC : 0 <= CHEAD) by (unfold CHEAD; lia).
    assert (HW : 0 <= W) by (unfold W; lia).
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H _]; apply Z.leb_le in H;
      unfold argc, envc, STR0 in H; lia.
  Qed.

  Lemma argH0_high2 : forall E M a, SINV0 E M -> argH0 E a = true -> uE E e_sp0 <= bv_unsigned a.
  Proof.
    intros E M a [HE _] H.
    assert (U : uE E e_sp0 = uE E0 e_sp0).
    { unfold e_sp0, uE. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot].
      rewrite !HE by (unfold NX0, V_S1, V_S2, V_SP; lia). reflexivity. }
    rewrite U, u_e_sp0. unfold argH0 in H.
    assert (HC : 0 <= CHEAD) by (unfold CHEAD; lia).
    assert (HW : 0 <= W) by (unfold W; lia).
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H _]; apply Z.leb_le in H;
      unfold argc, envc, STR0 in H; lia.
  Qed.

  Lemma u_sp8 : uE E0 (eadd (escale 4096 (EVar V_S1)) (eadd (escale 2 (EVar V_S2)) (escale 512 (EVar V_SP)))) = usp / 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _). pose proof uE0_sp as U9.
    unfold eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2, U9.
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

  (* the AT_RANDOM bytes sit [C - 16] above sp *)
  Lemma u_e_atrandom : uE E0 (e_atrandom RZ) = usp + CHEAD - 16.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof gap_range. pose proof chead_eq. pose proof bsb_ge. pose proof RZ_range.
    destruct uE0 as (_ & _ & _ & _ & _ & _ & _ & U8).
    pose proof u_e_auxv as UA. unfold e_atrandom, eadd, eaddz, escale, uE, AUXSZ in *.
    rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UA, U8. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_str0 : uE E0 (e_str0 RZ) = STR0.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof chead_eq. pose proof gap_range. pose proof bsb_ge. pose proof RZ_range.
    pose proof length_bsb_sum. pose proof lstr_lo.
    destruct uE0 as (_ & _ & _ & _ & _ & U6 & _).
    pose proof u_e_atrandom as UA. unfold e_str0, eadd, eaddz, uE, STR0 in *.
    rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite UA, U6. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_str1 : uE E0 (e_str1 RZ) = STR0 + L0 + 1.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof chead_eq. pose proof gap_range. pose proof bsb_ge. pose proof RZ_range.
    pose proof length_bsb_sum. pose proof lstr_hi. pose proof s0_in_strings. pose proof L0_range.
    destruct uE0 as (_ & _ & _ & _ & U5 & _).
    pose proof u_e_str0 as US. unfold e_str1, eadd, eaddz, uE, STR0 in *. rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite US, U5. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_atr8 : uE E0 e_atr8 = usp / 8 + argc + envc + G.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof gap_range.
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8). pose proof u_sp8 as U9.
    unfold e_atr8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia.
    rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit, !u_add64, !u_mul64, !u64_lit in U9 by lia.
    rewrite U1, U2, U3, U4, U8 in *. rewrite !Z.mod_small by lia. rewrite !Z.mod_small in U9 by lia. lia.
  Qed.

  (* the masked shadow index of AT_RANDOM + 8 ([e_atr8m RZ]), as openssl/punycode's [AsanInit]
     proves it, with this layout's offset [2 + 4 * RZ] *)
  Let Xsh : Z := argc + envc + 2 * ((usp mod 4096) / 16) + G.
  Lemma Xsh_range : 1 <= Xsh <= 1791.
  Proof.
    pose proof usp_lo. pose proof len_av. pose proof len_ev. pose proof gap_range.
    assert (Hu : 0 <= usp mod 4096 / 16 < 256).
    { pose proof (Z.mod_pos_bound usp 4096 ltac:(lia)) as B. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    unfold Xsh. lia.
  Qed.
  Lemma u_e_Xsh : uE E0 e_Xsh = Xsh.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof gap_range.
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8).
    assert (Hu : 0 <= usp mod 4096 / 16 < 256).
    { pose proof (Z.mod_pos_bound usp 4096 ltac:(lia)) as B. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    unfold e_Xsh, Xsh, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U2, U3, U4, U8.
    set (u := usp mod 4096 / 16) in *. clearbody u.
    rewrite !Z.mod_small by lia. lia.
  Qed.
  Lemma u_e_Xm : uE E0 (e_Xm RZ) = (Xsh + 2 + 4 * RZ) - (Xsh + 2 + 4 * RZ) mod 8.
  Proof.
    pose proof Xsh_range. pose proof RZ_range. pose proof u_e_Xsh as UX. unfold uE in *.
    unfold e_Xm, eaddz. rewrite !mkAlu_denot, !edenot_lit. rewrite u_and64.
    replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 2 ^ 3)%Z by reflexivity.
    rewrite u_add64, u64_lit by lia. rewrite UX. rewrite Z.mod_small by lia.
    rewrite land_highmask by lia. rewrite Z.add_assoc. reflexivity.
  Qed.
  Lemma u_e_atr8m : uE E0 (e_atr8m RZ)
    = 4096 * (usp / 32768) + 512 * ((usp mod 32768) / 4096) + ((Xsh + 2 + 4 * RZ) - (Xsh + 2 + 4 * RZ) mod 8).
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof Xsh_range. pose proof RZ_range.
    pose proof (Z.mod_pos_bound (Xsh + 2 + 4 * RZ) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound usp 32768 ltac:(lia)).
    assert (Hp : 0 <= (usp mod 32768) / 4096 < 8) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    assert (usp / 32768 <= 2 ^ 32) by (apply Z.div_le_upper_bound; lia). pose proof (Z.div_pos usp 32768 ltac:(lia) ltac:(lia)).
    destruct uE0 as (U1 & _). pose proof uE0_sp as UP. pose proof u_e_Xm as UM. unfold uE in *.
    unfold e_atr8m, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, UP, UM.
    rewrite !Z.mod_small by lia. lia.
  Qed.
  Lemma e_atr8m_range : 0xFFFF0000000 <= uE E0 (e_atr8m RZ) <= 0xFFFFFFFFFC0.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof usp_al. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof gap_range. pose proof chead_eq. pose proof length_bsb_sum. pose proof lstr_lo.
    pose proof bsb_ge. pose proof RZ_range. pose proof L0_range.
    (* the range of [e_atr8] that the start state claims ([init_kn_with]) *)
    assert (HA : 0xFFFF0000001 <= usp / 8 + argc + envc + G <= 0xFFFFFFFFFC5 - 4 * RZ) by lia.
    assert (HS : usp / 8 = 4096 * (usp / 32768) + 512 * ((usp mod 32768) / 4096) + 2 * ((usp mod 4096) / 16)) by lia.
    rewrite u_e_atr8m. unfold Xsh in *.
    set (s1 := usp / 32768) in *. set (p := (usp mod 32768) / 4096) in *. set (s2 := (usp mod 4096) / 16) in *.
    pose proof (Z.div_mod (argc + envc + 2 * s2 + G + 2 + 4 * RZ) 8 ltac:(lia)) as D6.
    pose proof (Z.mod_pos_bound (argc + envc + 2 * s2 + G + 2 + 4 * RZ) 8 ltac:(lia)) as M6.
    set (m := (argc + envc + 2 * s2 + G + 2 + 4 * RZ) mod 8) in *.
    set (xq := (argc + envc + 2 * s2 + G + 2 + 4 * RZ) / 8) in *.
    clearbody s1 p s2 m xq. lia.
  Qed.

  (* the word at sp0+16: argv[1]'s address, or the argv NULL *)
  Lemma u_e_argv1w : uE E0 (e_argv1w RZ) = Z.b2z (1 <? argc) * (STR0 + L0 + 1).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge.
    pose proof L0_range as HL0.
    assert (Hw1 : edenot E0 (e_argv1w RZ) = if (1 <? argc) then edenot E0 (e_str1 RZ) else Z_to_bv 64 0).
    { unfold e_argv1w. cbn [edenot]. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. cbn [edenot] in U3.
      apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit, U3 by lia.
      pose proof (u64_range (edenot E0 (e_str1 RZ))).
      destruct (1 <? argc); [rewrite Z.mul_1_l, Z.mod_small by lia; reflexivity | rewrite u64_lit by lia; reflexivity]. }
    pose proof u_e_str1 as U. unfold uE in U |- *. rewrite Hw1.
    destruct (1 <? argc); cbn [Z.b2z]; [rewrite U; lia | rewrite u64_lit by lia; lia].
  Qed.

  (* the launch values the main phase's entry reads ([MainEntry], [MainEntryBoth]): the eleven
     pinned plan variables, the stack pointer's bounds, argv[0]'s and argv[1]'s addresses.
     [Proof using All] fixes their arguments to every section variable and hypothesis. *)
  Lemma main_pins :
    uE E0 (EVar V_S1) = usp / 32768 /\ uE E0 (EVar V_S2) = (usp mod 4096) / 16
    /\ uE E0 (EVar V_SP) = (usp mod 32768) / 4096
    /\ uE E0 (EVar V_ARGC) = argc /\ uE E0 (EVar V_ENVC) = envc /\ uE E0 (EVar V_L0) = L0
    /\ uE E0 (EVar V_L1) = L1 /\ uE E0 (EVar V_W) = W /\ uE E0 (EVar V_BRK) = bv_unsigned brk0 / 4096
    /\ uE E0 (EVar V_UID) = bv_unsigned uid /\ uE E0 (EVar V_HW) = bv_unsigned hw.
  Proof using All.
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & _).
    split; [exact U1|]. split; [exact U2|]. split; [exact uE0_sp|].
    split; [exact U3|]. split; [exact U4|]. split; [exact U5|]. split; [exact uE0_L1|].
    split; [exact U6|]. split; [exact U7|]. split; [exact uE0_uid| exact uE0_hw].
  Qed.

  Lemma main_launch :
    0x7fff80000000 <= usp /\ usp + 192 <= 2 ^ 47 /\ usp mod 16 = 0
    /\ 1 <= argc <= 1024 /\ 0 <= envc <= 256
    /\ uE E0 (e_str0 RZ) = STR0 /\ uE E0 (e_argv1w RZ) = Z.b2z (1 <? argc) * (STR0 + L0 + 1).
  Proof using All.
    split; [exact usp_lo|]. split; [exact usp_hi|]. split; [exact usp_al|].
    split; [exact len_av|]. split; [exact len_ev|]. split; [exact u_e_str0| exact u_e_argv1w].
  Qed.

  (* ----------------------------------------------------------------------- *)
  (* The initial configuration                                                *)
  (* ----------------------------------------------------------------------- *)

  Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.
  (* [Run.init_config]'s model: [State.init_model] at the run stack pointer, with the launch's
     vDSO draw copied in by [State.with_vdso] *)
  Definition model0 : Model :=
    with_vdso (vdso_run_init (ed_vdso rdraw))
      (init_model (segments_reserved segs) brk0 mbase sp LIMIT inp).

  Let cs0 := init_acs_of RZ A.
  Let hid0 := hid A argH0 E0 cs0 model0.
  Let Mr0 := Mr A argH0 E0 cs0 model0 FULL0.

  (* the launch's reserved ledger is the image's reservations and the vDSO pair
     ([State.init_reserved]), which ends at [State.vdso_top] of the initial ledger *)
  Let VTOP : Z :=
    page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)).
  Let RESX : list (word * word) := vdso_reserved (in_kernel inp) VTOP.

  Lemma model0_facts :
    m_halted model0 = None /\ m_fds model0 = fds_std /\ m_tid model0 = None
    /\ vm_reserved (m_vmmaps model0) = segments_reserved segs ++ RESX /\ vm_maps (m_vmmaps model0) = []
    /\ vm_noaccess (m_vmmaps model0) = [] /\ m_vm_lazy model0 = [] /\ m_vm_materialized model0 = []
    /\ vm_limit (m_vmmaps model0) = LIMIT /\ vm_brk (m_vmmaps model0) = brk0 /\ vm_start_brk (m_vmmaps model0) = brk0
    /\ vm_mmap_base (m_vmmaps model0) = mbase /\ eager_used model0 = 0.
  Proof. repeat split; reflexivity. Qed.

  Lemma atop0 : atop model0 = usp - 8388608.
  Proof. reflexivity. Qed.

  Lemma mb_range : mmap_base_min <= bv_unsigned mbase <= mmap_base_max
                   /\ bv_unsigned mbase mod page_size = 0.
  Proof. destruct Hmb as (Y1 & Y2 & Y3). repeat split; assumption. Qed.

  (* the pair ends at [VTOP], at most the mmap base and at most one page below
     [State.mmap_base_min] *)
  Lemma vtop_range : mmap_base_min - 4095 <= VTOP <= bv_unsigned mbase
                     /\ VTOP mod 4096 = 0.
  Proof.
    pose proof mb_range as ((Y1 & Y2) & Y3). pose proof usp_lo.
    unfold VTOP, page_round_down_Z, page_size, stack_max_size,
           mmap_base_min, mmap_base_max, sp_window_hi, usp in *.
    split; [split|]; lia.
  Qed.

  (* [Run.recorded_kernel] carries [State.default_kernel]'s [kb_vdso = 1], so the text is two
     pages and the pair is four vvar pages below them: 16384 and 8192 bytes *)
  Lemma resx_eq : RESX = [(Z_to_bv 64 (VTOP - 24576), Z_to_bv 64 16384);
                          (Z_to_bv 64 (VTOP - 24576 + 16384), Z_to_bv 64 8192)].
  Proof.
    pose proof vtop_range as [[T1 T2] T3].
    unfold RESX, vdso_reserved. cbv zeta. rewrite Hkern.
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
  Proof. destruct Hresx as [RX1 RX2]. unfold resx_bytes. lia. Qed.

  (* the hidden set at start: the two argument-block regions; the hull and everything at or above
     [atop] are visible *)
  Lemma hid0_eq : forall a : word, hid0 a = (argH0 E0 a || negb (APS.in_hull A (bv_unsigned a) || (usp - 8388608 <=? bv_unsigned a)))%bool.
  Proof.
    intros a. unfold hid0, hid, vis. rewrite atop0. destruct model0_facts as (_&_&_&_&Hm&Hn&Hl&_). rewrite Hm. cbn [in_ivs existsb andb].
    rewrite orb_false_r. reflexivity.
  Qed.

  Lemma Mr0_visible : forall a : word, usp - 8388608 <= bv_unsigned a -> argH0 E0 a = false -> Mr0 a = FULL0 a.
  Proof.
    intros a Hc Ha. unfold Mr0, Mr, mrestrict. fold hid0. rewrite hid0_eq, Ha.
    replace (usp - 8388608 <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; exact Hc). rewrite orb_true_r. reflexivity.
  Qed.

  (* 6144513 is [StoreOk.stack_window_depth]: what the 8 MiB leave below sp for the largest entry
     image [StoreOk.stack_window_reach] bounds ([Run.stack_window_lo]) *)
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
  (* The knowledge [init_kn RZ A] holds                                       *)
  (* ----------------------------------------------------------------------- *)

  Lemma argH0_range : forall a : word, argH0 E0 a = true ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 8 * envc + 24
    \/ STR0 <= bv_unsigned a < utop.
  Proof.
    intros a H. unfold argH0 in H.
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; [left|right]; lia.
  Qed.

  (* the visible part of the block: the pointer vector below the envp array, the auxv, the gap,
     the random bytes and the pad; and everything above the stack VMA's end *)
  Lemma not_argH0 : forall a : word,
    (bv_unsigned a < usp + 8 * argc + 16 \/ (usp + 8 * argc + 8 * envc + 24 <= bv_unsigned a < STR0)
     \/ utop <= bv_unsigned a) -> argH0 E0 a = false.
  Proof.
    intros a H. destruct (argH0 E0 a) eqn:Ha; [|reflexivity]. apply argH0_range in Ha.
    pose proof len_av. pose proof len_ev. pose proof chead_eq. pose proof pad_range.
    pose proof gap_range. pose proof str0_hi. pose proof lstr_lo. pose proof RZ_range. unfold STR0 in *. lia.
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

  Let AUXW := auxv_words la ph entryw uid gid hw
                (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn).

  (* the auxv words: 58 (29 pairs) with CONFIG_RSEQ, 54 (27 pairs) without *)
  Lemma auxv_word_ok : forall (j : nat) v,
    (j < 2 * auxv_count rseq)%nat ->
    nth j AUXW (Z_to_bv 64 0) = edenot E0 v ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 v).
  Proof.
    intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum.
    pose proof lstr_lo. pose proof bsb_ge. pose proof RZ_range. pose proof auxv_count_RZ.
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
      exact (read_auxv_word segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi' j Hj).
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

  Lemma auxt_ok : forall i ty,
    (0 <= i < Z.of_nat (auxv_count rseq)) ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    kentry_ok segs E0 Mr0 (auxt i ty).
  Proof.
    intros i ty Hi H1. unfold auxt.
    replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia.
    apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
  Qed.

  Lemma kr_ok : forall e lo hi, lo <= uE E0 e <= hi -> kentry_ok segs E0 Mr0 (KRange e lo hi).
  Proof. intros e lo hi H. cbn [kentry_ok]. unfold uE in H. exact H. Qed.

  (* bytes of the zero window below sp, through [Mr0] *)
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
        unfold len_word, argc in *. rewrite u64_lit by lia. reflexivity. }
      rewrite <- Hv. apply RW. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
  Qed.

  (* argv[0] is at the bottom of the string area, [CatExec.cat_string_off] above sp *)
  Lemma cat_argv0_eq :
    bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) = STR0.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof RZ_range.
    rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0 Hav0).
    change (total_arg_bytes_nat (firstn 0 (in_argv inp))) with 0%nat.
    rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
    unfold STR0, CHEAD, W, usp, cat_string_off in *.
    rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia.
  Qed.

  Lemma argv0_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 8) 8 (e_str0 RZ)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge.
    apply (kword_stack e_sp0 8 (e_str0 RZ) (sp + nat_to_word (8 + 8 * 0))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
    - pose proof (read_argv_ptr_k segs inp mbase ph entryw sp rdraw 0) as RW.
      assert (Hv : cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0
                   = edenot E0 (e_str0 RZ)).
      { apply bv_eq. rewrite cat_argv0_eq. pose proof u_e_str0 as U. unfold uE in U. rewrite U. reflexivity. }
      rewrite <- Hv. apply RW; [exact Hav0|]. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
  Qed.

  (* the word at sp0+16: argv[1] or the argv NULL *)
  Lemma argv1_word_ok : kentry_ok segs E0 Mr0 (kw_argv1 (e_argv1w RZ)).
  Proof.
    unfold kw_argv1.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge.
    pose proof L0_range as HL0.
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
          rewrite U. unfold STR0, CHEAD, W, usp, L0, cat_string_off in *.
          rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia. }
        rewrite <- Hv. apply RW; [exact Hav1|]. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
      + apply Z.ltb_ge in Hc. assert (Hav1 : length argv = 1%nat) by (unfold argc in Hc; pose proof Hav0; lia).
        pose proof (read_argv_null segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as RW.
        rewrite Hav1 in RW.
        exact RW.
  Qed.

  (* the AT_RANDOM block is byte string [K_RND] = the draw *)
  Lemma atrandom_ok : kentry_ok segs E0 Mr0 (KBlob (SA (fst (e_atrb RZ)) (snd (e_atrb RZ))) (ELit 16) K_RND).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge.
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
    destruct (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as [off (Hp & Hoff & Hmod & Hrd)].
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

  Lemma kimg_ok : kentry_ok segs E0 Mr0 (KImg (img_lo A) (img_hi A)).
  Proof.
    pose proof usp_lo. pose proof (if_hull _ _ _ IMG) as (H1 & H2 & H3 & H4). cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    unfold Mr0, Mr, mrestrict. destruct (hid A argH0 E0 cs0 model0 (Z_to_bv 64 i)); [reflexivity|].
    apply FULL0_low. rewrite u64_lit; lia.
  Qed.

  Lemma rw_window_ok : kentry_ok segs E0 Mr0 (KWr (SA (ELit 0) (rw_lo A)) (ELit (rw_len A))).
  Proof.
    pose proof (if_rw _ _ _ IMG) as ((R1 & R2 & R3) & R4).
    assert (Hst : estart E0 (SA (ELit 0) (rw_lo A)) = rw_lo A) by (unfold estart; cbn [a_base a_off]; rewrite edenot_lit, u64_lit; lia).
    assert (Hl : elenZ E0 (ELit (rw_len A)) = rw_len A) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. split; [unfold flat; rewrite Hst; lia|].
    intros d m Hd Hdm. destruct m as [|m']; [reflexivity|].
    assert (Hu : bv_unsigned (Z_to_bv 64 (rw_lo A + d)) = rw_lo A + d) by (apply u_small; rewrite Nat2Z.inj_succ in Hdm; lia).
    apply store_ok_of_all; rewrite Hu; [lia|].
    intros x Hx. apply R4. lia.
  Qed.

  Lemma atr_ptr_eq : at_random_ptr sp rseq argv envp = edenot E0 (e_atrandom RZ).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof chead_eq. pose proof gap_range.
    pose proof len_av. pose proof len_ev. pose proof bsb_ge. pose proof RZ_range.
    destruct (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as [off (Hp & Hoff & _ & _)].
    apply bv_eq. rewrite Hp, word_add_nat, u64_lit by (unfold CHEAD, usp in *; lia).
    pose proof u_e_atrandom as U. unfold uE in U. rewrite U. unfold CHEAD, usp. lia.
  Qed.

  (* AT_NULL, the one named pair whose index moves with the flag: pair [26 + 2 * RZ] *)
  Lemma auxv_null_ok : know_ok segs E0 Mr0 (auxw (26 + 2 * RZ) 0 (ELit 0)).
  Proof.
    pose proof auxv_count_RZ. pose proof RZ_range.
    destruct (auxv_words_null la ph entryw uid gid hw
                (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn)) as [N1 N2].
    apply auxw_ok; [lia | exact N1 | rewrite edenot_lit; exact N2].
  Qed.

  (* the whole vector is readable stack bytes *)
  Lemma auxv_unk_ok : kentry_ok segs E0 Mr0 (KUnk (SA (fst e_auxb) (snd e_auxb)) (ELit (AUXSZ RZ))).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof chead_eq.
    pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof lstr_lo. pose proof RZ_range.
    assert (Hab : split_lit e_auxv = (fst e_auxb, snd e_auxb)) by (unfold e_auxb; destruct (split_lit e_auxv); reflexivity).
    set (ab := fst e_auxb) in *. set (ak := snd e_auxb) in *.
    pose proof (split_u E0 e_auxv ab ak Hab) as Hs. rewrite u_e_auxv in Hs.
    assert (Hak : ak = 24) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + 8 * argc + 8 * envc + 24) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit (AUXSZ RZ)) = AUXSZ RZ) by (apply elenZ_lit; unfold AUXSZ; lia).
    cbn [kentry_ok]. rewrite Hst, Hl.
    split; [unfold flat; rewrite Hst; unfold AUXSZ, usp in *; lia|].
    intros i Hi. unfold AUXSZ in Hi.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold STR0, usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw) by (rewrite u64_lit; unfold usp in *; lia). fold bsb.
    unfold stack_to_mem. fold usp. rewrite u64_lit by (unfold usp in *; lia).
    replace (usp <=? usp + 8 * argc + 8 * envc + 24 + i) with true by (symmetry; apply Z.leb_le; lia).
    cbv zeta.
    replace (usp + 8 * argc + 8 * envc + 24 + i - usp <? Z.of_nat (length bsb)) with true by (symmetry; apply Z.ltb_lt; lia).
    intros Hn. apply nth_error_None in Hn. lia.
  Qed.

  (* the claims of [AsanPlanCore.auxv_rest]: every other type word, the values the launch fixes,
     the gid pair, the CONFIG_RSEQ pair and the readable vector *)
  Lemma auxv_rest_ok : know_ok segs E0 Mr0 (auxv_rest RZ A).
  Proof.
    pose proof auxv_count_RZ. pose proof RZ_range.
    unfold auxv_rest.
    repeat (apply Forall_app; split).
    - repeat (apply Forall_cons;
              [apply auxt_ok;
                 [lia | unfold AUXW, auxv_words, auxv_entries;
                        cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
                        reflexivity] |]).
      apply Forall_nil.
    - apply auxw_ok; [lia | unfold AUXW, auxv_words, auxv_entries;
                            cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
                            reflexivity ..].
    - apply auxw_ok; [lia | unfold AUXW, auxv_words, auxv_entries;
                            cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
                            reflexivity ..].
    - apply auxw_ok; [lia | unfold AUXW, auxv_words, auxv_entries;
                            cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
                            reflexivity ..].
    - apply auxw_ok; [lia | unfold AUXW, auxv_words, auxv_entries;
                            cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
                            reflexivity
                          | unfold AUXW, auxv_words, auxv_entries;
                            cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
                            rewrite edenot_lit, <- Hapc; reflexivity].
    - apply auxw_ok; [lia | unfold AUXW, auxv_words, auxv_entries;
                            cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
                            reflexivity ..].
    - apply auxw_ok; [lia | unfold AUXW, auxv_words, auxv_entries;
                            cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
                            reflexivity ..].
    - apply Forall_cons; [|apply Forall_nil].
      apply auxt_ok; [lia | unfold AUXW, auxv_words, auxv_entries;
                            cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
                            reflexivity].
    - destruct (Z.eqb_spec RZ 1) as [E1|E1]; [|apply Forall_nil].
      assert (Er : la_rseq la = true).
      { cbn [launch_auxv la_rseq]. unfold RZ, rseq_z in E1.
        destruct (Bool.bool_dec (kb_rseq (in_kernel inp)) true) as [Ek|Ek]; [exact Ek|].
        apply Bool.not_true_is_false in Ek. rewrite Ek in E1. discriminate E1. }
      destruct (auxv_words_rseq la ph entryw uid gid hw (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn) Er)
        as (Q1 & Q2 & Q3 & Q4).
      apply Forall_app; split; (apply auxw_ok; [lia | |]).
      + exact Q1.
      + exact Q2.
      + exact Q3.
      + exact Q4.
    - apply Forall_cons; [exact auxv_unk_ok | apply Forall_nil].
  Qed.

  Lemma init_kn_with_ok : forall atr, kentry_ok segs E0 Mr0 atr -> know_ok segs E0 Mr0 (init_kn_with RZ atr A).
  Proof.
    intros atr Hatr.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof usp_al. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof gap_range. pose proof chead_eq. pose proof length_bsb_sum. pose proof lstr_lo.
    pose proof brk_range as [B1 B2]. pose proof bsb_ge. pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    pose proof (if_ph _ _ _ IMG) as (P1 & P2 & P3). pose proof RZ_range. pose proof auxv_count_RZ.
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8).
    pose proof L0_range as HL0.
    pose proof auxv_rest_ok as HR.
    unfold init_kn_with. revert HR. generalize (auxv_rest RZ A). intros LR HLR.
    destruct stack_window_ok as [SW1 SW2].
    apply Forall_app; split.
    { apply Forall_cons; [apply kr_ok; rewrite U1; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U2; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_sp; lia|].
      apply Forall_cons; [apply kr_ok; unfold eaddz, uE; rewrite mkAlu_denot, edenot_lit, u_add64, u64_lit by lia;
                          pose proof u_e_atrandom as U; unfold uE in U; rewrite U; rewrite Z.mod_small by lia; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_atr8; lia|].
      apply Forall_cons; [apply kr_ok; exact e_atr8m_range|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_sp0; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_pd; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_sp8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U3; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U4; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U5; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_L1; pose proof L1_range; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_uid; unfold valid_id in Huid; pose proof (u64_range uid); lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_hw; pose proof hw_range; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_gid; unfold valid_id in Hgid; pose proof (u64_range gid); lia|].
      apply Forall_cons; [apply kr_ok; rewrite U6; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U7; unfold BRK_ASLR in *; lia|].
      apply Forall_cons; [exact SW1|].
      apply Forall_cons; [exact SW2|].
      apply Forall_cons; [exact argc_word_ok|].
      apply Forall_cons; [exact argv0_word_ok|].
      apply Forall_cons; [exact argv1_word_ok|].
      apply Forall_nil. }
    repeat (apply Forall_app; split).
    (* AT_NULL *)
    10: exact auxv_null_ok.
    (* AT_RANDOM (pair 24): its value is the plan's [e_atrandom RZ] *)
    9: apply auxw_ok;
         [ lia
         | unfold AUXW, auxv_words, auxv_entries;
           cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
           reflexivity
         | unfold AUXW, auxv_words, auxv_entries;
           cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
           exact atr_ptr_eq ].
    (* pairs 13, 14, 15, 10, 11, 19, 20, 23: below the CONFIG_RSEQ pair *)
    1-8: apply auxw_ok;
         [ lia
         | unfold AUXW, auxv_words, auxv_entries;
           cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
           try reflexivity .. ].
    all: try (rewrite edenot_lit; reflexivity).
    1: rewrite edenot_lit, P1; reflexivity.
    1: rewrite edenot_lit, P2; reflexivity.
    1: rewrite edenot_lit, P3; reflexivity.
    - apply Forall_cons; [exact Hatr|].
      apply Forall_cons; [exact kimg_ok|].
      apply Forall_cons; [exact rw_window_ok|].
      apply Forall_nil.
    - exact HLR.
  Qed.

  Lemma init_kn_ok : know_ok segs E0 Mr0 (init_kn RZ A).
  Proof. exact (init_kn_with_ok _ atrandom_ok). Qed.

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

  Let pdu := usp - usp mod 4096.
  Lemma u_stkwin : uE E0 (eaddz e_pd STK_OFF) = pdu - 8388608.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof u_e_pd as U.
    unfold eaddz, uE in *. rewrite mkAlu_denot, edenot_lit, u_add64, U. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2^64)%Z. unfold STK_OFF, pdu. rewrite Zplus_mod_idemp_r, Z.mod_small by lia. lia.
  Qed.
  Lemma u_stkwlen : uE E0 e_stkwlen = STK_WTOP - pdu.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof u_e_pd as U.
    unfold e_stkwlen, esub, uE in *. rewrite mkAlu_denot, edenot_lit, u_sub64, U. unfold STK_WTOP, STK_OFF, pdu.
    rewrite u64_lit by lia. rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma allowA_init : allowA A E0 cs0 =
    [(pagedown (img_lo A), pageup (img_lo A + (img_hi A - img_lo A)));
     (pagedown (shadow_off A + img_lo A / 8), pageup (shadow_off A + (img_lo A + (img_hi A - img_lo A)) / 8));
     (pagedown (pdu - 8388608), pageup (pdu - 8388608 + (STK_WTOP - pdu)));
     (pagedown (shadow_off A + (pdu - 8388608) / 8), pageup (shadow_off A + (pdu - 8388608 + (STK_WTOP - pdu)) / 8))].
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    unfold allowA, cs0, init_acs_of, init_acs_of_with, init_vis. cbn [a_vis a_ghost app flat_map allow1 fst snd].
    unfold sh_lo, sh_hi. cbn [fst snd]. rewrite u_stkwin, u_stkwlen.
    unfold uE. rewrite !edenot_lit, !u64_lit by lia. reflexivity.
  Qed.

  Lemma abytes_init : A_bytes (allowA A E0 cs0) <= vis_cost (img_hi A - img_lo A) + vis_cost STK_WMAX
                      /\ vis_cost (img_hi A - img_lo A) + vis_cost STK_WMAX <= LIMIT.
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof (if_shadow _ _ _ IMG) as S1. pose proof usp_lo. pose proof usp_hi.
    rewrite allowA_init. cbn [A_bytes fst snd].
    replace (img_lo A + (img_hi A - img_lo A)) with (img_hi A) by lia.
    replace (pdu - 8388608 + (STK_WTOP - pdu)) with (STK_WTOP - 8388608) by lia.
    assert (Hpdu : 0x7fff80000000 <= pdu <= usp /\ pdu mod 4096 = 0) by (unfold pdu; lia).
    unfold vis_cost, STK_WMAX, STK_WTOP, STK_OFF, LIMIT, target_alloc_limit in *.
    assert (P1 : forall z, z mod 4096 = 0 -> pagedown z = z) by (intros z Hz; unfold pagedown; lia).
    assert (P2 : forall z, z mod 4096 = 0 -> pageup z = z) by (intros z Hz; unfold pageup; lia).
    rewrite (P1 (img_lo A) I3), (P2 (img_hi A) I4).
    pose proof (pageup_minus_pagedown (shadow_off A + img_lo A / 8) (shadow_off A + img_hi A / 8) ltac:(lia)).
    pose proof (pageup_minus_pagedown (pdu - 8388608) (0x800000000000 - - 0x800000 - 8388608) ltac:(lia)).
    pose proof (pageup_minus_pagedown (shadow_off A + (pdu - 8388608) / 8) (shadow_off A + (0x800000000000 - - 0x800000 - 8388608) / 8) ltac:(lia)).
    split; lia.
  Qed.

  Theorem init_cs_ok_s : cs_ok segs A LIMIT SINV0 argH0 (in_fs inp) E0 cs0 R0 FULL0 model0.
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
      pose proof (if_hull _ _ _ IMG) as (G1 & G2 & G3 & G4).
      destruct Hresx as [RX1 RX2]. pose proof resx_bytes_lo.
      exists RESX. split; [reflexivity|].
      split; [| split; [pose proof resx_len; lia | rewrite resx_sum; lia]].
      rewrite resx_eq. repeat constructor;
        cbn [fst snd];
        rewrite !u64_lit
          by (unfold mmap_base_min, mmap_base_max, sp_window_hi in *; lia);
        unfold KHI, mmap_base_min, mmap_base_max, sp_window_hi in *; lia.
    - reflexivity.
    - reflexivity.
    - constructor.
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      exact (init_sp_ok_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp Hsp).
    - constructor.
    - constructor.
    - rewrite u_e_sp0. reflexivity.
    - rewrite u_e_sp0. pose proof usp_lo. pose proof usp_hi. unfold CEIL, TOPMAX. lia.
    - intros z Hz. exact Hz.
    - constructor.
    - constructor.
    - (* co_totsz: the image's reservations and the vDSO pair *)
      rewrite app_nil_r, sum_sizes_app, (if_sizes _ _ _ IMG), resx_sum.
      pose proof resx_bytes_lo. lia.
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7 & _). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.
    - lia.
    - lia.
    - exact AB1.
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
    - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
    - split; [intros; reflexivity | intros; reflexivity].
    - constructor.
    - split; [intros X; discriminate X | intros t X; discriminate X].
    - constructor.
    - (* co_mres: no tracked mappings yet *) constructor.
    - (* co_vdso: the ledger ends with the launch's own pair *)
      replace (m_kernel model0) with (in_kernel inp) by reflexivity.
      replace (vdso_top (m_vmmaps model0)) with VTOP
        by (symmetry; exact (vdso_top_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp)).
      apply incl_appr, incl_refl.
    - (* co_rdr: [init_model] copies [in_channel_reader inp] and [with_vdso] keeps it *)
      exact Hrdr.
  Qed.

  (* [Run.init_config] is the configuration [cs_ok] speaks about; [Hapc] lands both in the
     machine's initial pc and in the auxv's AT_ENTRY *)
  Theorem init_cfg_eq_s :
    init_config segs apc ph sp brk0 mbase rdraw LIMIT inp = cfg_of segs R0 (a_entry A) FULL0 model0.
  Proof.
    unfold init_config, cfg_of, FULL0. rewrite init_mkst, Hapc. reflexivity.
  Qed.
End Init.

(* ------------------------------------------------------------------------- *)
(* The interface: every launch fact the start-up chain reads, in one record   *)
(* ------------------------------------------------------------------------- *)

(* The launch's facts, each proved from [Run.valid_input] and [Run.valid_entry] where the chain
   starts ([valid_input] gives the argv/envp/credential/hwcap/launch/kernel facts,
   [valid_entry_sv48] the sp/brk/mmap-base facts and [entry_launch_ok_va]); [lo_img],
   [lo_apc] and [lo_resx] are facts of the image and its table. *)
Record launch_ok (segs : list Segment) (A : atable) (ph : PhdrInfo) (apc : N)
       (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput) : Prop := LAUNCH_OK {
  lo_img : img_facts segs A ph;
  lo_apc : Z.of_N apc = a_entry A;
  lo_sp : valid_sp sp;
  lo_brk : valid_brk segs brk0;
  lo_mb : valid_mmap_base mbase;
  lo_va : valid_argv (in_argv inp);
  lo_ve : valid_envp (in_envp inp);
  lo_uid : valid_id (in_uid inp);
  lo_gid : valid_id (in_gid inp);
  lo_hw : valid_hwcap (in_hwcap inp);
  lo_vl : valid_launch inp;
  lo_lau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp;
  lo_kern : in_kernel inp = recorded_kernel (in_kernel inp);
  lo_resx : (2 <= n_resx A)%nat /\ (20 <= p_resx A)%nat;
  lo_rdr : in_channel_reader inp = true
}.

Ltac lo_destruct HL := destruct HL as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ?].

(* [SINV0_agree] with exactly the arguments [SINV0] takes (the section lemma also takes the section
   hypotheses its proof's [lia] read) *)
Lemma SINV0_agree_g : forall ph apc sp rdraw brk0 mbase inp E E' M,
  env_agree NX0 E E' -> SINV0 ph apc sp rdraw brk0 mbase inp E M -> SINV0 ph apc sp rdraw brk0 mbase inp E' M.
Proof.
  intros ph apc sp rdraw brk0 mbase inp E E' M [Hag _] [H1 H2]. split; [|exact H2].
  intros n Hn. rewrite <- (Hag n) by (unfold NX0 in *; lia). apply H1. exact Hn.
Qed.

(* every launch fact of [launch_ok], from the published statement's premises *)
Theorem launch_ok_of_valid : forall segs A ph apc sp rdraw brk0 mbase inp,
  img_facts segs A ph -> Z.of_N apc = a_entry A -> (2 <= n_resx A)%nat /\ (20 <= p_resx A)%nat ->
  valid_input inp -> valid_entry (mkImage segs apc ph) (mkEntry sp brk0 mbase rdraw) inp ->
  launch_ok segs A ph apc sp rdraw brk0 mbase inp.
Proof.
  intros segs A ph apc sp rdraw brk0 mbase inp IMG Hapc Hresx Hi Hv.
  pose proof (valid_input_channel_reader _ Hi) as Hrdr.
  destruct Hi as (Hva & Hve & _ & _ & _ & [Huid Hgid] & _ & _ & Hhw & _ & Hvasz & _ & Hvl & _ & _ & Hkern).
  apply (proj1 (valid_entry_sv48 _ _ _ Hvasz)) in Hv. destruct Hv as (Hsp & Hbrk & Hmb & _ & Hlau).
  constructor; assumption.
Qed.

Theorem init_cs_ok : forall segs A ph apc sp rdraw brk0 mbase inp,
  launch_ok segs A ph apc sp rdraw brk0 mbase inp ->
  cs_ok segs A LIMIT (SINV0 ph apc sp rdraw brk0 mbase inp) (argH0 sp rdraw inp) (in_fs inp)
        (E0 sp rdraw brk0 inp) (init_acs_of (rseq_z (kb_rseq (in_kernel inp))) A) (R0 sp)
        (FULL0 ph apc sp rdraw mbase inp) (model0 segs sp rdraw brk0 mbase inp).
Proof. intros segs A ph apc sp rdraw brk0 mbase inp HL. lo_destruct HL. eapply init_cs_ok_s; eassumption. Unshelve. all: assumption. Qed.

Theorem init_cfg_eq : forall segs A ph apc sp rdraw brk0 mbase inp,
  launch_ok segs A ph apc sp rdraw brk0 mbase inp ->
  init_config segs apc ph sp brk0 mbase rdraw LIMIT inp
  = cfg_of segs (R0 sp) (a_entry A) (FULL0 ph apc sp rdraw mbase inp) (model0 segs sp rdraw brk0 mbase inp).
Proof. intros segs A ph apc sp rdraw brk0 mbase inp HL. lo_destruct HL. eapply init_cfg_eq_s; eassumption. Unshelve. all: assumption. Qed.

Theorem argH0_high_l : forall segs A ph apc sp rdraw brk0 mbase inp,
  launch_ok segs A ph apc sp rdraw brk0 mbase inp ->
  forall E a, argH0 sp rdraw inp E a = true -> CEIL <= bv_unsigned a.
Proof. intros segs A ph apc sp rdraw brk0 mbase inp HL E a H. lo_destruct HL. eapply argH0_high; eassumption. Unshelve. all: assumption. Qed.

Theorem argH0_high2_l : forall segs A ph apc sp rdraw brk0 mbase inp,
  launch_ok segs A ph apc sp rdraw brk0 mbase inp ->
  forall E M a, SINV0 ph apc sp rdraw brk0 mbase inp E M -> argH0 sp rdraw inp E a = true -> uE E e_sp0 <= bv_unsigned a.
Proof. intros segs A ph apc sp rdraw brk0 mbase inp HL E M a HS H. lo_destruct HL. eapply argH0_high2; eassumption. Unshelve. all: assumption. Qed.

(* the values of the launch expressions the start-up nodes read *)
Theorem u_e_sp0_l : forall segs A ph apc sp rdraw brk0 mbase inp,
  launch_ok segs A ph apc sp rdraw brk0 mbase inp ->
  uE (E0 sp rdraw brk0 inp) e_sp0 = bv_unsigned sp.
Proof. intros segs A ph apc sp rdraw brk0 mbase inp HL. lo_destruct HL. eapply u_e_sp0; eassumption. Unshelve. all: assumption. Qed.

Theorem u_e_envp_l : forall segs A ph apc sp rdraw brk0 mbase inp,
  launch_ok segs A ph apc sp rdraw brk0 mbase inp ->
  uE (E0 sp rdraw brk0 inp) e_envp = bv_unsigned sp + 8 * Z.of_nat (length (in_argv inp)) + 16.
Proof. intros segs A ph apc sp rdraw brk0 mbase inp HL. lo_destruct HL. eapply u_e_envp; eassumption. Unshelve. all: assumption. Qed.

Theorem uE0_envc_l : forall segs A ph apc sp rdraw brk0 mbase inp,
  launch_ok segs A ph apc sp rdraw brk0 mbase inp ->
  uE (E0 sp rdraw brk0 inp) (EVar V_ENVC) = Z.of_nat (length (in_envp inp)).
Proof. intros segs A ph apc sp rdraw brk0 mbase inp HL. lo_destruct HL. eapply uE0_envc; eassumption. Unshelve. all: assumption. Qed.

Theorem u_e_str0_l : forall segs A ph apc sp rdraw brk0 mbase inp,
  launch_ok segs A ph apc sp rdraw brk0 mbase inp ->
  uE (E0 sp rdraw brk0 inp) (e_str0 (rseq_z (kb_rseq (in_kernel inp))))
  = bv_unsigned sp + Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
    + Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) sp (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp)).
Proof. intros segs A ph apc sp rdraw brk0 mbase inp HL. lo_destruct HL. eapply u_e_str0; eassumption. Unshelve. all: assumption. Qed.

Theorem s0_in_strings_l : forall segs A ph apc sp rdraw brk0 mbase inp,
  launch_ok segs A ph apc sp rdraw brk0 mbase inp ->
  Z.of_nat (length (nth 0 (in_argv inp) [])) + 2
  <= Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp)).
Proof. intros segs A ph apc sp rdraw brk0 mbase inp HL. lo_destruct HL. eapply s0_in_strings; eassumption. Unshelve. all: assumption. Qed.

(* the string area runs from argv[0] to the stack VMA's end *)
Theorem str0_hi_l : forall segs A ph apc sp rdraw brk0 mbase inp,
  launch_ok segs A ph apc sp rdraw brk0 mbase inp ->
  bv_unsigned sp + Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
  + Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) sp (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp))
  + Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp)) + 8
  = bv_unsigned (ed_top rdraw).
Proof. intros segs A ph apc sp rdraw brk0 mbase inp HL. lo_destruct HL. eapply str0_hi; eassumption. Unshelve. all: assumption. Qed.

(* the main phase's entry: the pinned plan variables and the launch's argv words, at the launch
   ([main_pins], [main_launch] take every section variable and hypothesis, in order) *)
Theorem main_pins_l : forall segs A ph apc sp rdraw brk0 mbase inp,
  launch_ok segs A ph apc sp rdraw brk0 mbase inp ->
  uE (E0 sp rdraw brk0 inp) (EVar V_S1) = bv_unsigned sp / 32768
  /\ uE (E0 sp rdraw brk0 inp) (EVar V_S2) = (bv_unsigned sp mod 4096) / 16
  /\ uE (E0 sp rdraw brk0 inp) (EVar V_SP) = (bv_unsigned sp mod 32768) / 4096
  /\ uE (E0 sp rdraw brk0 inp) (EVar V_ARGC) = Z.of_nat (length (in_argv inp))
  /\ uE (E0 sp rdraw brk0 inp) (EVar V_ENVC) = Z.of_nat (length (in_envp inp))
  /\ uE (E0 sp rdraw brk0 inp) (EVar V_L0) = Z.of_nat (length (nth 0 (in_argv inp) []))
  /\ uE (E0 sp rdraw brk0 inp) (EVar V_L1) = Z.of_nat (length (nth 1 (in_argv inp) []))
  /\ uE (E0 sp rdraw brk0 inp) (EVar V_W)
     = Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) sp (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp))
  /\ uE (E0 sp rdraw brk0 inp) (EVar V_BRK) = bv_unsigned brk0 / 4096
  /\ uE (E0 sp rdraw brk0 inp) (EVar V_UID) = bv_unsigned (in_uid inp)
  /\ uE (E0 sp rdraw brk0 inp) (EVar V_HW) = bv_unsigned (in_hwcap inp).
Proof.
  intros segs A ph apc sp rdraw brk0 mbase inp HL.
  destruct HL as [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15].
  exact (main_pins segs A ph apc sp rdraw brk0 mbase inp H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15).
Qed.

Theorem main_launch_l : forall segs A ph apc sp rdraw brk0 mbase inp,
  launch_ok segs A ph apc sp rdraw brk0 mbase inp ->
  0x7fff80000000 <= bv_unsigned sp /\ bv_unsigned sp + 192 <= 2 ^ 47 /\ bv_unsigned sp mod 16 = 0
  /\ 1 <= Z.of_nat (length (in_argv inp)) <= 1024 /\ 0 <= Z.of_nat (length (in_envp inp)) <= 256
  /\ uE (E0 sp rdraw brk0 inp) (e_str0 (rseq_z (kb_rseq (in_kernel inp))))
     = bv_unsigned sp + Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
       + Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) sp (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp))
  /\ uE (E0 sp rdraw brk0 inp) (e_argv1w (rseq_z (kb_rseq (in_kernel inp))))
     = Z.b2z (1 <? Z.of_nat (length (in_argv inp)))
       * (bv_unsigned sp + Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
          + Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) sp (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp))
          + Z.of_nat (length (nth 0 (in_argv inp) [])) + 1).
Proof.
  intros segs A ph apc sp rdraw brk0 mbase inp HL.
  destruct HL as [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15].
  exact (main_launch segs A ph apc sp rdraw brk0 mbase inp H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15).
Qed.
