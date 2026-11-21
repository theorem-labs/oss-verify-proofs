(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start state is the launch's: its stack window, string block, execfn, rseq area, gid and the vDSO/vvar reserved pair). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk StreamSim StepTac ShapeAlg AgentLib StartupAux RefLayoutC ArgvEnvC
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan AsanPlanSound.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AsanCeil.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.


(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition LIMIT : Z := 17179869184.
Lemma LIMIT_val : LIMIT = 2 ^ 34.
Proof. reflexivity. Qed.

Record InStreams := mkInStreams { is_stdin : InputStream; is_urandom : InputStream }.

(* [comment removed for export] *)
Record LaunchX := mkLaunchX {
  lx_apc : N; lx_mbase : word; lx_fs : Fs.Fs; lx_stdin : InStreams; lx_gid : word;
  lx_groups : list word; lx_net : NetQueue; lx_nofile : word; lx_sigmask : word;
  lx_kb : KernelBuild; lx_execfn : list byte; lx_crd : bool; lx_sgd : bool; lx_sgt : bool }.

(* [comment removed for export] *)
Record img_facts (segs : list Segment) (A : atable) (ph : PhdrInfo) : Prop := IMG_FACTS {
  if_ph    : ph_addr_z A = Z.of_N (ph_addr ph) /\ ph_ent_z A = Z.of_N (ph_ent ph) /\ ph_num_z A = Z.of_N (ph_num ph);
  if_hull  : 0 <= img_lo A <= img_hi A /\ img_hi A <= 2 ^ 32 /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0;
  if_top   : reserved_top (segments_reserved segs) = img_hi A;
  if_res   : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                    (segments_reserved segs);
  if_sizes : sum_sizes (segments_reserved segs) = img_hi A - img_lo A;
  if_rw    : (0 <= rw_lo A /\ 0 <= rw_len A /\ rw_lo A + rw_len A < 2 ^ 64)
             /\ forall m (x : word), rw_lo A <= bv_unsigned x < rw_lo A + rw_len A -> wview segs m x <> None;
  if_shadow : 0 <= shadow_off A <= 2 ^ 47;
  (* [comment removed for export] *)
  if_resx  : (2 <= n_resx A)%nat /\ (20 <= p_resx A)%nat
}.

(* [comment removed for export] *)
Definition stack_image_size (sp top : word) : Z :=
  (bv_unsigned top - bv_unsigned sp)%Z.

(** the string area holds argv[0] and argv[1] with their NULs, and at least the exec name's NUL
    (openssl/pem's Common/AsanInit.v) *)
Lemma launch_strings_argv01 : forall (av ev : list (list byte)) (ex : list byte), (0 < length av)%nat ->
  (length (nth 0 av []) + length (nth 1 av []) + 2 <= launch_string_bytes av ev ex)%nat.
Proof.
  intros [|a [|b t]] ev ex H; [cbn in H; lia| |];
    unfold launch_string_bytes; cbn [flatten_strings flat_map nth]; rewrite !length_app; cbn [length]; lia.
Qed.

Section Init.
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  (* [comment removed for export] *)
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable lim : Z.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InStreams.
  Variable uid gid : word.
  Variable hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variable nofile : word.
  Variable sigmask : word.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variables crd sgd sgt : bool.

  Hypothesis IMG : img_facts segs A ph.
  Hypothesis Hapc : Z.of_N apc = a_entry A.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hlim : LIMIT <= lim.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  (* [comment removed for export] *)
  Hypothesis Huid : valid_id uid.
  (* [comment removed for export] *)
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).
  (* [comment removed for export] *)
  Definition inp : ProcInput :=
    mkProcInput_full argv envp fs (is_stdin stdin) uid gid groups net nofile sigmask hw false Sv48
      (is_urandom stdin) [] (recorded_kernel kb) execfn crd sgd sgt.
  (* [comment removed for export] *)
  Hypothesis Hrdr : crd = true.

  (* [comment removed for export] *)
  Hypothesis Hlaunch : valid_launch inp.
  (* [comment removed for export] *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.

  (* [comment removed for export] *)
  Let rseq : bool := kb_rseq kb.
  Let entryw : word := Z_to_bv 64 (Z.of_N apc).
  Let la : LaunchAuxv := launch_auxv inp sp mbase.
  Let top : word := ed_top rdraw.

  Lemma inp_argv : in_argv inp = argv.        Proof. reflexivity. Qed.
  Lemma inp_envp : in_envp inp = envp.        Proof. reflexivity. Qed.
  Lemma inp_uid : in_uid inp = uid.           Proof. reflexivity. Qed.
  Lemma inp_gid : in_gid inp = gid.           Proof. reflexivity. Qed.
  Lemma inp_hwcap : in_hwcap inp = hw.        Proof. reflexivity. Qed.
  Lemma inp_kernel : in_kernel inp = recorded_kernel kb. Proof. reflexivity. Qed.
  Lemma inp_execfn : in_execfn inp = execfn.  Proof. reflexivity. Qed.
  Lemma inp_rseq : kb_rseq (in_kernel inp) = rseq. Proof. reflexivity. Qed.
  Lemma la_rseq_eq : la_rseq la = rseq.       Proof. reflexivity. Qed.
  (** LPS 727298f3: [rseq] is free (the launch leaves [kb_rseq] free, [Run.recorded_kernel]);
      [rz] is its 0/1 image and the value the plan variable [V_R] carries in [E0], so one plan
      covers both auxv layouts (27 and 29 pairs). *)
  Let rz : Z := rseq_z rseq.
  Lemma rz_is_range : 0 <= rz <= 1. Proof. unfold rz. apply rseq_z_range. Qed.
  Lemma auxsz_rz : AUXSZ rz = Z.of_nat (auxv_size rseq). Proof. unfold rz. apply AUXSZ_of. Qed.
  Lemma auxv_count_rz : Z.of_nat (auxv_count rseq) = 27 + 2 * rz.
  Proof. unfold rz, rseq, rseq_z, auxv_count. destruct (kb_rseq kb); reflexivity. Qed.

  Let bsb := entry_stack_image inp mbase ph entryw sp rdraw.   (* [comment removed for export] *)
  Let usp := bv_unsigned sp.
  Let utop := bv_unsigned top.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let L0 := Z.of_nat (length (nth 0 argv [])).
  Let L1 := Z.of_nat (length (nth 1 argv [])).
  (* [comment removed for export] *)
  Let G := Z.of_nat (block_items argv envp mod 2).
  (* [comment removed for export] *)
  Let CHEAD := Z.of_nat (block_head_size rseq argv envp).
  (* [comment removed for export] *)
  Let LSTR := Z.of_nat (launch_string_bytes argv envp execfn).
  (* [comment removed for export] *)
  Let W := Z.of_nat (block_pad_len rseq sp top argv envp execfn).
  (* [comment removed for export] *)
  Let STR0 := usp + CHEAD + W.
  (* [comment removed for export] *)
  Let PGSP := pgdown usp.
  Let Q := (utop - PGSP) / 4096.

  Definition vals0 : list word :=
    [Z_to_bv 64 (usp / 32768); Z_to_bv 64 argc; Z_to_bv 64 envc; Z_to_bv 64 L0; Z_to_bv 64 W;
     Z_to_bv 64 (bv_unsigned brk0 / 4096); Z_to_bv 64 ((usp mod 4096) / 16); Z_to_bv 64 L1; uid; hw;
     Z_to_bv 64 ((usp mod 32768) / 4096); Z_to_bv 64 Q; Z_to_bv 64 G; Z_to_bv 64 rz; gid].
  (* [comment removed for export] *)
  Definition E0 : env := Env (fun n => nth n vals0 (Z_to_bv 64 0))
                             (fun k => if Nat.eqb k K_RND then at_random_bytes (ed_random rdraw) else []).

  (* [comment removed for export] *)
  Definition argH0 (E : env) (a : word) : bool :=
    let z := bv_unsigned a in
    (((usp + 8 * argc + 16 <=? z) && (z <? usp + 8 * argc + 8 * envc + 24))
     || ((STR0 <=? z) && (z <? utop)))%bool.

  (* The launch's own validity facts ride along in the start invariant: every consumer that holds
     an SINV0 state reads them off it ([SINV0_launch]), and [init_cs_ok] proves them from the
     launch premises [Hlaunch] and [Hlau]. *)
  Definition SINV0 (E : env) (M : word -> option byte) : Prop :=
    (forall n, (n < NX0)%nat -> ev E n = ev E0 n)
    /\ (forall a, argH0 E a = true -> M a = wrap_mem inp mbase ph entryw sp rdraw a)
    /\ (valid_launch inp /\ entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp).

  Lemma SINV0_launch : forall E M, SINV0 E M ->
    valid_launch inp /\ entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  Proof. intros E M (_ & _ & H). exact H. Qed.

  (* [comment removed for export] *)
  Lemma argH0_high_s : forall E a, argH0 E a = true -> CEIL <= bv_unsigned a /\ usp <= bv_unsigned a.
  Proof.
    intros E a H. unfold argH0 in H. destruct Hsp as [Hlo _]. unfold sp_window_lo in Hlo. unfold CEIL.
    pose proof (valid_argv_len argv Hva).
    assert (HC : 0 <= CHEAD) by (unfold CHEAD; lia).
    assert (HW : 0 <= W) by (unfold W; lia).
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H _]; apply Z.leb_le in H;
      unfold usp, argc, envc, STR0 in H; lia.
  Qed.

  Lemma NX0_spw : AP.expr_vars_lt NX0 e_spw = true.
  Proof. reflexivity. Qed.

  Lemma argH0_agree : forall E E' a, env_agree NX0 E E' -> argH0 E a = argH0 E' a.
  Proof. reflexivity. Qed.

  Lemma SINV0_frame : forall E M M', (forall a, argH0 E a = true -> M' a = M a) -> SINV0 E M -> SINV0 E M'.
  Proof.
    intros E M M' Hf (H1 & H2 & H3). split; [exact H1|]. split; [|exact H3].
    intros a Ha. rewrite (Hf a Ha). apply H2. exact Ha.
  Qed.

  Lemma SINV0_agree : forall E E' M, env_agree NX0 E E' -> SINV0 E M -> SINV0 E' M.
  Proof.
    intros E E' M [Hag _] [H1 H2]. split; [|exact H2]. intros n Hn. rewrite <- (Hag n) by (unfold NX0 in *; lia). apply H1. exact Hn.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

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

  (* [comment removed for export] *)
  Lemma chead_eq : CHEAD = 8 * argc + 8 * envc + 472 + 32 * rz + 8 * G.
  Proof.
    pose proof auxsz_rz as HA. unfold AUXSZ in HA.
    unfold CHEAD, G, argc, envc, block_head_size, block_items. lia.
  Qed.

  Lemma chead_range : 480 <= CHEAD <= 10752.
  Proof. pose proof chead_eq. pose proof len_av. pose proof len_ev. pose proof gap_range. pose proof rz_is_range. lia. Qed.

  (* [comment removed for export] *)
  Lemma lstr_lo : 2 <= LSTR.
  Proof.
    unfold LSTR, launch_string_bytes.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
    pose proof (Nat2Z.is_nonneg (length execfn)).
    pose proof Hav0 as Hnz.
    destruct argv as [|a t] eqn:Ea; [cbn in Hnz; lia|].
    cbn [flatten_strings flat_map]. rewrite !length_app. cbn [length]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma s0_in_strings : L0 + 1 <= LSTR.
  Proof.
    unfold LSTR, launch_string_bytes, L0.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
    pose proof (Nat2Z.is_nonneg (length execfn)).
    pose proof Hav0 as Hnz.
    destruct argv as [|a t] eqn:Ea; [cbn in Hnz; lia|].
    cbn [flatten_strings flat_map nth]. rewrite !length_app. cbn [length]. lia.
  Qed.

  Lemma s01_in_strings : L0 + L1 + 2 <= LSTR.
  Proof. unfold LSTR, L0, L1. pose proof (launch_strings_argv01 argv envp execfn Hav0). lia. Qed.

  (* [comment removed for export] *)
  Lemma lstr_hi : LSTR + 8 * argc + 8 * envc <= 2097152.
  Proof.
    destruct Hlaunch as [_ Hb]. unfold launch_bytes, e2big_limit in Hb.
    rewrite inp_argv, inp_envp, inp_execfn in Hb. unfold LSTR, argc, envc. lia.
  Qed.

  (* [comment removed for export] *)
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

  Lemma pad_range : 0 <= W <= 4110.
  Proof. pose proof pad_bounds_Z. pose proof pad_eq. lia. Qed.

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Lemma bsb_ge : 8 * argc + 8 * envc + 482 + 32 * rz <= Z.of_nat (length bsb).
  Proof.
    pose proof length_bsb_sum. pose proof chead_eq. pose proof lstr_lo. pose proof pad_range. pose proof rz_is_range.
    pose proof gap_range. lia.
  Qed.

  Lemma str0_hi : STR0 + LSTR + 8 = utop.
  Proof. unfold STR0. pose proof pad_eq. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma brk_range : img_hi A <= bv_unsigned brk0 <= img_hi A + BRK_ASLR /\ bv_unsigned brk0 mod 4096 = 0.
  Proof.
    destruct Hbrk as (H1 & H2 & H3). unfold brk_aslr_max in H2. unfold page_size in H3.
    rewrite (if_top _ _ _ IMG) in H1, H2. unfold BRK_ASLR. lia.
  Qed.

  Lemma usp_hi : usp + 192 <= 2 ^ 47.
  Proof. pose proof usp_fit. pose proof bsb_ge. pose proof len_av. pose proof len_ev. pose proof rz_is_range. lia. Qed.

  (** rewrite [Z.mod_small] at the innermost [mod]s first (openssl/pem's Common/AsanInit.v) *)
  Ltac mod_small_inner :=
    repeat match goal with
      |- context [ (?a mod ?m) ] =>
        lazymatch a with context [ _ mod _ ] => fail | _ => rewrite (Z.mod_small a m) by lia end
    end.

  (** make the section's page lets opaque to [lia] (openssl/pem's Common/AsanInit.v) *)
  Ltac hide_lets := first [clearbody Q | idtac]; first [clearbody PGSP | idtac].

  (* [comment removed for export] *)
  Lemma uE0 :
    uE E0 (EVar V_S1) = usp / 32768 /\ uE E0 (EVar V_S2) = (usp mod 4096) / 16
    /\ uE E0 (EVar V_ARGC) = argc /\ uE E0 (EVar V_ENVC) = envc /\ uE E0 (EVar V_L0) = L0
    /\ uE E0 (EVar V_W) = W /\ uE E0 (EVar V_BRK) = bv_unsigned brk0 / 4096
    /\ uE E0 (EVar V_G) = G.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof gap_range.
    pose proof (u64_range brk0) as [B1 B2].
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva ltac:(destruct Hva as [Hl _]; lia)). lia. }
    unfold uE. cbn [edenot E0 ev nth vals0 V_S1 V_S2 V_ARGC V_ENVC V_L0 V_W V_BRK V_G].
    rewrite !u64_lit by lia. repeat split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma uE0_envc : uE E0 (EVar V_ENVC) = envc.
  Proof. destruct uE0 as (_ & _ & _ & H & _). exact H. Qed.

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

  (* LPS 727298f3: the flag's plan variable and the gid's *)
  Lemma uE0_r : uE E0 (EVar V_R) = rz.
  Proof. pose proof rz_is_range. unfold uE. cbn [edenot E0 ev nth vals0 V_R]. rewrite u64_lit by lia. reflexivity. Qed.
  Lemma edenot_gid : gid = edenot E0 (EVar V_GID).
  Proof. reflexivity. Qed.
  Lemma uE0_GR : uE E0 (EVar V_G) = G /\ uE E0 (EVar V_R) = rz.
  Proof. destruct uE0 as (_ & _ & _ & _ & _ & _ & _ & U8). split; [exact U8 | exact uE0_r]. Qed.

  Lemma usp_decomp :
    usp = 32768 * (usp / 32768) + 4096 * ((usp mod 32768) / 4096) + 16 * ((usp mod 4096) / 16)
    /\ 0 <= (usp mod 32768) / 4096 <= 7 /\ 0 <= (usp mod 4096) / 16 <= 255 /\ usp mod 4096 = 16 * ((usp mod 4096) / 16)
    /\ usp mod 32768 = 4096 * ((usp mod 32768) / 4096) + usp mod 4096.
  Proof.
    pose proof usp_lo. pose proof usp_al.
    pose proof (Z.div_mod usp 32768 ltac:(lia)). pose proof (Z.mod_pos_bound usp 32768 ltac:(lia)).
    pose proof (Z.div_mod (usp mod 32768) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (usp mod 32768) 4096 ltac:(lia)).
    pose proof (Z.div_mod usp 4096 ltac:(lia)). pose proof (Z.mod_pos_bound usp 4096 ltac:(lia)).
    pose proof (Z.div_mod (usp mod 4096) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (usp mod 4096) 16 ltac:(lia)).
    pose proof (Z.div_mod usp 16 ltac:(lia)).
    assert (E1 : (usp mod 32768) mod 4096 = usp mod 4096).
    { apply Z.mod_mod_divide. exists 8. reflexivity. }
    pose proof (Z.div_mod (usp mod 32768) 4096 ltac:(lia)) as D2. rewrite E1 in D2.
    assert (E2 : (usp mod 4096) mod 16 = 0).
    { rewrite Z.mod_mod_divide by (exists 256; reflexivity). exact usp_al. }
    assert ((usp mod 32768) / 4096 < 8) by (apply Z.div_lt_upper_bound; lia).
    assert ((usp mod 4096) / 16 < 256) by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_pos (usp mod 32768) 4096 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos (usp mod 4096) 16 ltac:(lia) ltac:(lia)).
    lia.
  Qed.

  Lemma top_al : utop mod 4096 = 0.
  Proof. destruct Hlau as (Ht & _ & _). destruct Ht as (H & _). unfold page_size in H. exact H. Qed.

  Lemma PG_range : PGSP <= usp < PGSP + 4096 /\ PGSP mod 4096 = 0 /\ utop = PGSP + 4096 * Q /\ 1 <= Q <= 600
                   /\ usp + Z.of_nat (length bsb) = utop /\ utop <= 2 ^ 47.
  Proof.
    pose proof top_al. pose proof length_bsb_eq as LB. unfold stack_image_size in LB. fold utop usp in LB.
    pose proof bsb_ge. pose proof bsb_len_hi. pose proof usp_fit. pose proof usp_lo. pose proof len_av. pose proof len_ev. pose proof rz_is_range.
    unfold Q, PGSP, pgdown. lia.
  Qed.

  Lemma uE0_PQ : uE E0 (EVar V_P) = (usp mod 32768) / 4096 /\ uE E0 (EVar V_Q) = Q.
  Proof.
    pose proof usp_decomp as (_ & D2 & _). pose proof PG_range as (_ & _ & _ & QR & _).
    unfold uE. cbn [edenot E0 ev nth vals0 V_P V_Q]. rewrite !u64_lit by lia. split; reflexivity.
  Qed.

Lemma u_e_pgsp : uE E0 e_pgsp = usp - usp mod 4096.
  Proof.
    pose proof usp_lo. pose proof usp_al.
    assert (Hh47 : usp <= 2 ^ 47) by (unfold usp; destruct Hsp as (_ & Hsph & _); unfold sp_window_hi in Hsph; lia).
    pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5).
    assert (U1 : uE E0 (EVar V_S1) = usp / 32768)
      by (unfold uE; cbn [edenot E0 ev nth vals0 V_S1]; rewrite u64_lit by lia; reflexivity).
    assert (UP : uE E0 (EVar V_P) = (usp mod 32768) / 4096)
      by (unfold uE; cbn [edenot E0 ev nth vals0 V_P]; rewrite u64_lit by lia; reflexivity).
    unfold e_pgsp, eadd, escale, uE in *. unfold V_S1, V_P in U1, UP. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, UP.
    rewrite !Z.mod_small by lia. lia.
  Qed.
  Lemma u_e_sp0 : uE E0 e_sp0 = usp.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). destruct uE0 as (U1 & U2 & _). destruct uE0_PQ as [UP _].
    unfold e_sp0, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2, UP.
    rewrite !Z.mod_small by lia. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma u_e_spw : uE E0 e_spw = usp.
  Proof. replace e_spw with e_sp0 by (vm_compute; reflexivity). exact u_e_sp0. Qed.
  (* [comment removed for export] *)
  Lemma SINV0_pgsp : forall E M, SINV0 E M -> uE E e_pgsp = pgdown usp.
  Proof.
    intros E M [H1 _]. unfold pgdown. rewrite <- u_e_pgsp. unfold uE, e_pgsp, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    cbn [edenot]. rewrite (H1 0%nat), (H1 10%nat) by (unfold NX0; lia). reflexivity.
  Qed.

  Lemma edenot_e_sp0 : edenot E0 e_sp0 = sp.
  Proof. apply bv_eq. exact u_e_sp0. Qed.

  Lemma u_sp8 : uE E0 e_sp8 = usp / 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). destruct uE0 as (U1 & U2 & _). destruct uE0_PQ as [UP _].
    unfold e_sp8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2, UP.
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

  (* [comment removed for export] *)
  Lemma u_e_atrandom : uE E0 e_atrandom = usp + CHEAD - 16.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof gap_range. pose proof chead_eq. pose proof bsb_ge. pose proof rz_is_range. pose proof uE0_r as UR.
    destruct uE0 as (_ & _ & _ & _ & _ & _ & _ & U8).
    pose proof u_e_auxv as UA. unfold e_atrandom, eadd, eaddz, escale, uE in *.
    rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UA, U8, UR. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_str0 : uE E0 e_str0 = STR0.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof chead_eq. pose proof gap_range. pose proof bsb_ge. pose proof rz_is_range.
    destruct uE0 as (_ & _ & _ & _ & _ & U6 & _).
    pose proof u_e_atrandom as UA. unfold e_str0, eadd, eaddz, uE, STR0 in *.
    rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite UA, U6. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_str1 : uE E0 e_str1 = STR0 + L0 + 1.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof chead_eq. pose proof gap_range. pose proof bsb_ge. pose proof rz_is_range.
    pose proof length_bsb_sum. pose proof lstr_hi.
    destruct uE0 as (_ & _ & _ & _ & U5 & _).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    pose proof u_e_str0 as US. unfold e_str1, eadd, eaddz, uE, STR0 in *. rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite US, U5. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_atr8 : uE E0 e_atr8 = usp / 8 + argc + envc + 4 * rz + G.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof gap_range. pose proof rz_is_range.
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & _). destruct uE0_GR as [U8 U9]. pose proof u_sp8 as US.
    unfold e_atr8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia.
    rewrite US, U3, U4, U8, U9.
    assert (usp / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). pose proof (Z.div_pos usp 8 ltac:(lia) ltac:(lia)).
    rewrite !Z.mod_small by lia. lia.
  Qed.

  (** the shift [e_atr8 - 4096*s1 - 512*p] and its 8-aligned part (openssl/pem's Common/AsanInit.v) *)
  Definition Xsh : Z := argc + envc + 4 * rz + G + 2 * ((usp mod 4096) / 16).
  Lemma Xsh_range : 1 <= Xsh <= 1024 + 256 + 4 + 1 + 510.
  Proof. pose proof len_av. pose proof len_ev. pose proof gap_range. pose proof rz_is_range. unfold Xsh. pose proof usp_decomp as (_ & _ & D3 & _). lia. Qed.
  Lemma u_e_Xsh : uE E0 e_Xsh = Xsh.
  Proof.
    pose proof Xsh_range. pose proof len_av. pose proof len_ev. pose proof gap_range. pose proof rz_is_range. pose proof usp_decomp as (_ & _ & D3 & _).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & _). destruct uE0_GR as [U8 U9]. unfold uE in *.
    unfold e_Xsh, Xsh, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot]. cbn [edenot] in U2, U3, U4, U8, U9.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U2, U3, U4, U8, U9.
    assert (Hu : 0 <= usp mod 4096 / 16 < 256).
    { pose proof (Z.mod_pos_bound usp 4096 ltac:(lia)) as B. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    set (u := usp mod 4096 / 16) in *. clearbody u.
    rewrite !Z.mod_small by lia. lia.
  Qed.
  Lemma u_e_Xm : uE E0 e_Xm = Xsh - Xsh mod 8.
  Proof.
    pose proof Xsh_range. pose proof u_e_Xsh as UX. unfold uE in *.
    unfold e_Xm. rewrite mkAlu_denot, edenot_lit. rewrite u_and64. rewrite UX.
    replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 2 ^ 3)%Z by reflexivity. rewrite land_highmask by lia. reflexivity.
  Qed.
  Lemma u_e_atr8m : uE E0 e_atr8m = 4096 * (usp / 32768) + 512 * ((usp mod 32768) / 4096) + (Xsh - Xsh mod 8).
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof Xsh_range. pose proof (Z.mod_pos_bound Xsh 8 ltac:(lia)). pose proof usp_decomp as (_ & D2 & _).
    destruct uE0 as (U1 & _). destruct uE0_PQ as [UP _]. pose proof u_e_Xm as UM. unfold uE in *.
    unfold e_atr8m, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot]. cbn [edenot] in U1, UP, UM. rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, UP, UM.
    assert (usp / 32768 <= 2 ^ 32) by (apply Z.div_le_upper_bound; lia). pose proof (Z.div_pos usp 32768 ltac:(lia) ltac:(lia)).
    rewrite !Z.mod_small by lia. reflexivity.
  Qed.
  Lemma e_atr8m_range : 0xFFFF0000000 <= uE E0 e_atr8m <= 0xFFFFFFFFFC0.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof gap_range. pose proof rz_is_range. pose proof chead_eq. pose proof length_bsb_sum. pose proof pad_range. pose proof lstr_lo.
    pose proof Xsh_range as XR. pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5).
    rewrite u_e_atr8m.
    set (s1 := usp / 32768) in *. set (p := (usp mod 32768) / 4096) in *. set (s2 := (usp mod 4096) / 16) in *.
    pose proof (Z.div_mod Xsh 8 ltac:(lia)) as D6. pose proof (Z.mod_pos_bound Xsh 8 ltac:(lia)) as M6.
    set (m := Xsh mod 8) in *. set (xq := Xsh / 8) in *. unfold Xsh in *.
    assert (U8 : usp = 8 * (4096 * s1 + 512 * p + 2 * s2)) by lia.
    nia.
  Qed.
  (* the aligned shadow word of AT_RANDOM + 8 (AsanPlanCore.e_atr8m2) *)
  Lemma u_e_Xm2 : uE E0 e_Xm2 = (Xsh + 2) - (Xsh + 2) mod 8.
  Proof.
    pose proof Xsh_range. pose proof u_e_Xsh as UX. unfold uE in *.
    unfold e_Xm2, eaddz. rewrite !mkAlu_denot, !edenot_lit. rewrite u_and64, u_add64. rewrite UX.
    change (bv_unsigned (Z_to_bv 64 2)) with 2%Z.
    rewrite (Z.mod_small (Xsh + 2)) by lia.
    replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 2 ^ 3)%Z by reflexivity. rewrite land_highmask by lia. reflexivity.
  Qed.
  Lemma u_e_atr8m2 : uE E0 e_atr8m2 = 4096 * (usp / 32768) + 512 * ((usp mod 32768) / 4096) + ((Xsh + 2) - (Xsh + 2) mod 8).
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof Xsh_range. pose proof (Z.mod_pos_bound (Xsh + 2) 8 ltac:(lia)). pose proof usp_decomp as (_ & D2 & _).
    destruct uE0 as (U1 & _). destruct uE0_PQ as [UP _]. pose proof u_e_Xm2 as UM. unfold uE in *.
    unfold e_atr8m2, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot]. cbn [edenot] in U1, UP, UM. rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, UP, UM.
    assert (usp / 32768 <= 2 ^ 32) by (apply Z.div_le_upper_bound; lia). pose proof (Z.div_pos usp 32768 ltac:(lia) ltac:(lia)).
    rewrite !Z.mod_small by lia. reflexivity.
  Qed.
  Lemma e_atr8m2_range : 0xFFFF0000000 <= uE E0 e_atr8m2 <= 0xFFFFFFFFFC0.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof gap_range. pose proof rz_is_range. pose proof chead_eq. pose proof length_bsb_sum. pose proof pad_range. pose proof lstr_lo.
    pose proof Xsh_range as XR. pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5).
    rewrite u_e_atr8m2.
    set (s1 := usp / 32768) in *. set (p := (usp mod 32768) / 4096) in *. set (s2 := (usp mod 4096) / 16) in *.
    pose proof (Z.div_mod (Xsh + 2) 8 ltac:(lia)) as D6. pose proof (Z.mod_pos_bound (Xsh + 2) 8 ltac:(lia)) as M6.
    set (m := (Xsh + 2) mod 8) in *. set (xq := (Xsh + 2) / 8) in *. unfold Xsh in *.
    assert (U8 : usp = 8 * (4096 * s1 + 512 * p + 2 * s2)) by lia.
    nia.
  Qed.

  Lemma u_e_vis3b : uE E0 e_vis3b = 32768 * (usp / 32768).
  Proof.
    pose proof usp_lo. pose proof usp_hi. destruct uE0 as (U1 & _). unfold uE in *.
    unfold e_vis3b, escale. rewrite mkMd_denot, edenot_lit, u_mul64, u64_lit by lia. rewrite U1.
    assert (usp / 32768 <= 2 ^ 32) by (apply Z.div_le_upper_bound; lia). pose proof (Z.div_pos usp 32768 ltac:(lia) ltac:(lia)).
    rewrite Z.mod_small by lia. reflexivity.
  Qed.

  (** distances from the pointer arrays to the stack VMA's end (openssl/pem's Common/AsanInit.v) *)
  Lemma u_e_blk : uE E0 e_blk0 = utop - (usp + 8 * argc + 8 * envc)
                  /\ uE E0 e_blkL0 = utop - (usp + 8 * argc + 8 * envc) - L0
                  /\ uE E0 e_blkL01 = utop - (usp + 8 * argc + 8 * envc) - L0 - L1
                  /\ uE E0 e_blk08 = (utop - (usp + 8 * argc + 8 * envc)) / 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof pad_range. pose proof bsb_ge.
    pose proof gap_range. pose proof rz_is_range. pose proof chead_eq. pose proof length_bsb_sum. pose proof s01_in_strings. pose proof lstr_hi.
    pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). pose proof PG_range as (P1 & P4 & P6 & QR & P2 & P3). pose proof top_al as P5.
    pose proof L1_range.
    assert (HL0 : 0 <= L0 <= 131071) by (unfold L0; pose proof (valid_argv_str_len argv 0 Hva Hav0); lia).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & _). destruct uE0_PQ as [UP UQ]. pose proof uE0_L1 as UL1. unfold uE in *.
    unfold PGSP, pgdown in P1, P6.
    set (s1 := usp / 32768) in *. set (pp := (usp mod 32768) / 4096) in *. set (s2 := (usp mod 4096) / 16) in *.
    clearbody s1 pp s2. hide_lets.
    assert (HB : utop = usp - 16 * s2 + 4096 * Q) by lia.
    assert (HC : 8 * argc + 8 * envc + L0 + L1 + 2 <= utop - usp) by lia.
    unfold e_blkL0, e_blkL01, e_blk0, e_blk08, esub, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, ?mkAlu_denot, !edenot_lit.
    cbn [edenot]. cbn [edenot] in U2, U3, U4, U5, UQ, UL1.
    rewrite ?u_sub64, ?u_mul64, ?u_add64, ?u_mul64, ?u_add64. rewrite !u64_lit by lia. rewrite ?U2, ?U3, ?U4, ?U5, ?UQ, ?UL1.
    clear P4 P5 D5. mod_small_inner.
    assert (E8 : (utop - (usp + 8 * argc + 8 * envc)) / 8 = 512 * Q - 2 * s2 - (argc + envc)) by lia.
    repeat split; lia.
  Qed.

  Lemma u_e_vis3n : uE E0 e_vis3n = 4096 * ((usp mod 32768) / 4096) + 4096 * Q.
  Proof.
    pose proof usp_decomp as (_ & D2 & _). pose proof PG_range as (_ & _ & _ & QR & _). destruct uE0_PQ as [UP UQ]. unfold uE in *.
    unfold e_vis3n, eadd, escale. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit, u_add64, !u_mul64, !u64_lit by lia. rewrite UP, UQ.
    assert (HQ : 0 <= 4096 * Q < 2 ^ 64) by lia. assert (HP : 0 <= 4096 * (usp mod 32768 / 4096) < 2 ^ 64) by lia.
    rewrite (Z.mod_small _ _ HQ), (Z.mod_small _ _ HP). rewrite Z.mod_small by lia. reflexivity.
  Qed.

  Lemma u_e_top : uE E0 e_top = utop /\ uE E0 e_top8 = utop / 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_decomp as (D1 & D2 & _). pose proof PG_range as (P1 & P2 & P3 & QR & P5 & P6).
    destruct uE0 as (U1 & _). destruct uE0_PQ as [UP UQ]. unfold uE in *.
    unfold e_top, e_top8, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot]. cbn [edenot] in U1, UP, UQ.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, UP, UQ.
    assert (usp / 32768 <= 2 ^ 32) by (apply Z.div_le_upper_bound; lia). pose proof (Z.div_pos usp 32768 ltac:(lia) ltac:(lia)).
    rewrite !Z.mod_small by lia. rewrite P3. unfold PGSP, pgdown in *. split; lia.
  Qed.

  (** the bytes above the AT_RANDOM block and the string area beyond argv[0] / argv[1]
      (openssl/pem's Common/AsanInit.v) *)
  Lemma u_e_pgslack : uE E0 e_pgslack = utop - (usp + CHEAD)
                      /\ uE E0 e_pgslack8 = (utop - (usp + CHEAD)) / 8
                      /\ uE E0 e_strW0 = LSTR - L0
                      /\ uE E0 e_strW01 = LSTR - L0 - L1.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof pad_range. pose proof bsb_ge.
    pose proof gap_range. pose proof rz_is_range. pose proof chead_eq. pose proof length_bsb_sum. pose proof s01_in_strings. pose proof lstr_hi.
    pose proof pad_eq. pose proof L1_range.
    pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). pose proof PG_range as (P1 & P4 & P6 & QR & P2 & P3). pose proof top_al as P5.
    assert (HL0 : 0 <= L0 <= 131071) by (unfold L0; pose proof (valid_argv_str_len argv 0 Hva Hav0); lia).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & _). destruct uE0_PQ as [UP UQ]. destruct uE0_GR as [U8 U9].
    pose proof uE0_L1 as UL1. unfold uE in *.
    unfold PGSP, pgdown in P1, P6.
    set (s1 := usp / 32768) in *. set (pp := (usp mod 32768) / 4096) in *. set (s2 := (usp mod 4096) / 16) in *.
    clearbody s1 pp s2. hide_lets.
    unfold e_strW01, e_strW0, e_pgslack, e_pgslack8, esub, eadd, eaddz, escale. rewrite !mkAlu_denot, !mkMd_denot, ?mkAlu_denot, !edenot_lit.
    rewrite ?mkMd_denot, ?mkAlu_denot, ?edenot_lit.
    cbn [edenot]. cbn [edenot] in U2, U3, U4, U5, U6, UQ, U8, U9, UL1.
    repeat progress rewrite ?u_sub64, ?u_mul64, ?u_add64. rewrite !u64_lit by lia. rewrite ?U2, ?U3, ?U4, ?U5, ?U6, ?UQ, ?U8, ?U9, ?UL1.
    assert (HB : utop = usp - 16 * s2 + 4096 * Q) by lia.
    clear P4 P5 D5. mod_small_inner.
    repeat split; lia.
  Qed.

  (** LPS c0dd863a: argv[0]'s distance to the stack VMA's end, [top - str0] *)
  Lemma u_e_strW : uE E0 e_strW = LSTR + 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof pad_range. pose proof bsb_ge.
    pose proof gap_range. pose proof rz_is_range. pose proof chead_eq. pose proof length_bsb_sum. pose proof s01_in_strings. pose proof lstr_hi.
    pose proof pad_eq. pose proof L1_range.
    pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). pose proof PG_range as (P1 & P4 & P6 & QR & P2 & P3). pose proof top_al as P5.
    assert (HL0 : 0 <= L0 <= 131071) by (unfold L0; pose proof (valid_argv_str_len argv 0 Hva Hav0); lia).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & _). destruct uE0_PQ as [UP UQ]. destruct uE0_GR as [U8 U9].
    pose proof uE0_L1 as UL1. unfold uE in *.
    unfold PGSP, pgdown in P1, P6.
    set (s1 := usp / 32768) in *. set (pp := (usp mod 32768) / 4096) in *. set (s2 := (usp mod 4096) / 16) in *.
    clearbody s1 pp s2. hide_lets.
    unfold e_strW, e_pgslack, esub, eadd, eaddz, escale. rewrite !mkAlu_denot, !mkMd_denot, ?mkAlu_denot, !edenot_lit.
    rewrite ?mkMd_denot, ?mkAlu_denot, ?edenot_lit.
    cbn [edenot]. cbn [edenot] in U2, U3, U4, U5, U6, UQ, U8, U9, UL1.
    repeat progress rewrite ?u_sub64, ?u_mul64, ?u_add64. rewrite !u64_lit by lia. rewrite ?U2, ?U3, ?U4, ?U5, ?U6, ?UQ, ?U8, ?U9, ?UL1.
    assert (HB : utop = usp - 16 * s2 + 4096 * Q) by lia.
    clear P4 P5 D5. mod_small_inner.
    lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.
  Definition FULL0 : word -> option byte := wrap_mem inp mbase ph entryw sp rdraw.
  (* [comment removed for export] *)
  Definition model0 : Model :=
    with_vdso (vdso_run_init (ed_vdso rdraw))
      (init_model (segments_reserved segs) brk0 mbase sp lim inp).

  (* LPS 727298f3: the start state at the run's own CONFIG_RSEQ value *)
  Let cs0 := init_acs_r rz A.
  Let cs0z := init_acs_r_zero rz A.
  Let hid0 := hid A argH0 E0 cs0 model0.
  Let Mr0 := Mr A argH0 E0 cs0 model0 FULL0.

  Lemma alloc_top0 : alloc_top (m_vmmaps model0) = usp - 8388608.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let VTOP : Z :=
    page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)).
  Let RESX : list (word * word) := vdso_reserved (in_kernel inp) VTOP.

  Lemma model0_facts :
    m_halted model0 = None /\ m_fds model0 = fds_std /\ m_tid model0 = None
    /\ vm_reserved (m_vmmaps model0) = segments_reserved segs ++ RESX /\ vm_maps (m_vmmaps model0) = []
    /\ vm_noaccess (m_vmmaps model0) = [] /\ m_vm_lazy model0 = [] /\ m_vm_materialized model0 = []
    /\ vm_limit (m_vmmaps model0) = lim /\ vm_brk (m_vmmaps model0) = brk0 /\ vm_start_brk (m_vmmaps model0) = brk0
    /\ vm_mmap_base (m_vmmaps model0) = mbase /\ eager_used model0 = 0.
  Proof. repeat split; reflexivity. Qed.

  Lemma sum_sizes_app : forall l1 l2, sum_sizes (l1 ++ l2) = sum_sizes l1 + sum_sizes l2.
  Proof.
    induction l1 as [|iv l1 IH]; intro l2; cbn [app sum_sizes]; [lia|]. rewrite IH. lia.
  Qed.

  Lemma mb_range : mmap_base_min <= bv_unsigned mbase <= mmap_base_max
                   /\ bv_unsigned mbase mod page_size = 0.
  Proof. destruct Hmb as (Y1 & Y2 & Y3). repeat split; assumption. Qed.

  (* [comment removed for export] *)
  Lemma vtop_range : mmap_base_min - 4095 <= VTOP <= bv_unsigned mbase
                     /\ VTOP mod 4096 = 0.
  Proof.
    pose proof mb_range as ((Y1 & Y2) & Y3). pose proof usp_lo.
    unfold VTOP, page_round_down_Z, page_size, stack_max_size,
           mmap_base_min, mmap_base_max, sp_window_hi, usp in *.
    split; [split|]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma resx_eq : RESX = [(Z_to_bv 64 (VTOP - 24576), Z_to_bv 64 16384);
                          (Z_to_bv 64 (VTOP - 24576 + 16384), Z_to_bv 64 8192)].
  Proof.
    pose proof vtop_range as [[T1 T2] T3].
    unfold RESX, vdso_reserved. cbv zeta.
    replace (vdso_len (in_kernel inp)) with 24576 by (vm_compute; reflexivity).
    replace (vdso_vvar_pages * page_size)%Z with 16384 by (vm_compute; reflexivity).
    replace (vdso_text_pages (in_kernel inp) * page_size)%Z with 8192 by (vm_compute; reflexivity).
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
  Proof.
    pose proof (if_resx _ _ _ IMG) as [RX1 RX2]. unfold resx_bytes. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hid0_eq : forall a : word, hid0 a = (argH0 E0 a || negb (APS.in_hull A (bv_unsigned a) || (usp - 8388608 <=? bv_unsigned a)))%bool.
  Proof.
    intros a. unfold hid0, hid, vis. rewrite alloc_top0. destruct model0_facts as (_&_&_&_&Hm&Hn&Hl&_). rewrite Hm. cbn [in_ivs existsb andb].
    rewrite orb_false_r. reflexivity.
  Qed.

  Lemma Mr0_visible : forall a : word, usp - 8388608 <= bv_unsigned a -> argH0 E0 a = false -> Mr0 a = FULL0 a.
  Proof.
    intros a Hc Ha. unfold Mr0, Mr, mrestrict. fold hid0. rewrite hid0_eq, Ha.
    replace (usp - 8388608 <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; exact Hc). rewrite orb_true_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma argH0_range : forall a : word, argH0 E0 a = true ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 8 * envc + 24
    \/ STR0 <= bv_unsigned a < utop.
  Proof.
    intros a H. unfold argH0 in H.
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; [left|right]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma not_argH0 : forall a : word,
    (bv_unsigned a < usp + 8 * argc + 16 \/ (usp + 8 * argc + 8 * envc + 24 <= bv_unsigned a < STR0)
     \/ utop <= bv_unsigned a) -> argH0 E0 a = false.
  Proof.
    intros a H. destruct (argH0 E0 a) eqn:Ha; [|reflexivity]. apply argH0_range in Ha.
    pose proof len_av. pose proof len_ev. pose proof chead_eq. pose proof pad_range. pose proof rz_is_range.
    pose proof gap_range. pose proof str0_hi. pose proof lstr_lo. unfold STR0 in *. lia.
  Qed.

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Lemma auxv_word_ok : forall (j : nat) v,
    (Z.of_nat j < 54 + 4 * rz) ->
    nth j AUXW (Z_to_bv 64 0) = edenot E0 v ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 v).
  Proof.
    intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum.
    pose proof lstr_lo. pose proof bsb_ge. pose proof rz_is_range.
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
      assert (Hcnt : (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat).
      { rewrite inp_rseq. pose proof auxv_count_rz. lia. }
      pose proof (read_auxv_word segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi' j Hcnt) as RW.
      exact RW.
  Qed.

  Lemma auxw_ok : forall i ty v,
    (0 <= i < 27 + 2 * rz) ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    nth (Z.to_nat (2 * i + 1)) AUXW (Z_to_bv 64 0) = edenot E0 v ->
    know_ok segs E0 Mr0 (auxw i ty v).
  Proof.
    intros i ty v Hi H1 H2. unfold auxw.
    constructor; [|constructor; [|constructor]].
    - replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia. apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
    - replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia. apply auxv_word_ok; [lia|]. exact H2.
  Qed.

  Lemma kr_ok : forall e lo hi, lo <= uE E0 e <= hi -> kentry_ok segs E0 Mr0 (KRange e lo hi).
  Proof. intros e lo hi H. cbn [kentry_ok]. unfold uE in H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma Mr0_below : forall a : word, usp - 6144513 <= bv_unsigned a < usp -> Mr0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. pose proof usp_lo. pose proof len_av.
    rewrite Mr0_visible; [apply FULL0_below; exact Ha | unfold usp in *; lia | apply not_argH0; lia].
  Qed.

  (* LPS c0dd863a: the window the start-up knowledge claims is [Mr0_below]'s, cut at its low end so that it starts
     a whole number of pages above the FX stack region's base [usp - 8388608] (8388608 - 6144000 = 548 * 4096;
     6144000 = 6144513 - 6144513 mod 4096): an FX stack region claims whole pages from its low bound up *)
  Lemma stack_window_ok :
    kentry_ok segs E0 Mr0 (KWr (SA e_sp0 (-6144000)) (ELit 6144000))
    /\ kentry_ok segs E0 Mr0 (KZero (SA e_sp0 (-6144000)) (ELit 6144000)).
  Proof.
    pose proof usp_lo. pose proof usp_hi.
    assert (Hst : estart E0 (SA e_sp0 (-6144000)) = usp - 6144000).
    { unfold estart. cbn [a_base a_off]. pose proof u_e_sp0 as U. unfold uE in U. rewrite U. lia. }
    assert (Hl : elenZ E0 (ELit 6144000) = 6144000) by (apply elenZ_lit; lia).
    assert (Hfl : flat E0 (SA e_sp0 (-6144000)) (elenZ E0 (ELit 6144000))).
    { unfold flat. rewrite Hst, Hl. lia. }
    split; cbn [kentry_ok]; (split; [exact Hfl|]); rewrite Hst, ?Hl.
    - intros d m Hd Hdm. apply store_ok_of_all; rewrite u_small by lia; [lia|].
      intros x Hx. unfold wview. rewrite (Mr0_below x) by lia. discriminate.
    - intros i Hi. apply Mr0_below. rewrite u_small by lia. lia.
  Qed.

  Lemma argc_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 0) 8 (EVar V_ARGC)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge. pose proof rz_is_range.
    apply (kword_stack e_sp0 0 (EVar V_ARGC) sp).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. unfold usp. lia.
    - unfold usp. lia.
    - unfold usp in *. lia.
    - intros x Hx. apply not_argH0. unfold usp in *. lia.
    - pose proof (read_argc inp mbase ph entryw segs sp rdraw) as RW.
      assert (Hv : len_word argv = edenot E0 (EVar V_ARGC)).
      { apply bv_eq. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. rewrite U3.
        pose proof len_av. unfold len_word, argc in *. rewrite u64_lit by lia. reflexivity. }
      rewrite inp_argv in RW. rewrite <- Hv. apply RW. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cat_argv0_eq :
    bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) = STR0.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof rz_is_range.
    rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0 Hav0).
    change (total_arg_bytes_nat (firstn 0 (in_argv inp))) with 0%nat.
    rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
    change (kb_rseq (in_kernel inp)) with rseq. change (in_execfn inp) with execfn.
    change (in_argv inp) with argv. change (in_envp inp) with envp.
    unfold STR0, CHEAD, W, usp, rseq, top, cat_string_off in *.
    rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia.
  Qed.

  Lemma argv0_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 8) 8 e_str0).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge. pose proof rz_is_range.
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

  (* [comment removed for export] *)
  Lemma argv1_word_ok : kentry_ok segs E0 Mr0 (kw_argv1 e_argv1w).
  Proof.
    unfold kw_argv1.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge. pose proof rz_is_range.
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
        { apply bv_eq.
          pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof rz_is_range.
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
        rewrite <- Hv. apply RW; [exact Hav1|]. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
      + apply Z.ltb_ge in Hc. assert (Hav1 : length argv = 1%nat) by (unfold argc in Hc; pose proof Hav0; lia).
        pose proof (read_argv_null segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as RW.
        rewrite inp_argv in RW. rewrite Hav1 in RW.
        exact RW.
  Qed.

  (* [comment removed for export] *)
  Lemma atrandom_ok : kentry_ok segs E0 Mr0 (KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge. pose proof rz_is_range.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof lstr_lo.
    assert (Hab : split_lit e_atrandom = (fst e_atrb, snd e_atrb)) by (unfold e_atrb; destruct (split_lit e_atrandom); reflexivity).
    set (ab := fst e_atrb) in *. set (ak := snd e_atrb) in *.
    pose proof (split_u E0 e_atrandom ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    assert (Hak : ak = 456) by (subst ak; vm_compute; reflexivity).
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
    rewrite inp_argv, inp_envp, inp_rseq in Hp, Hoff, Hrd.
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

  (* [comment removed for export] *)
  Lemma atrandom_zero_ok : kentry_ok segs E0 Mr0 (KZero (SA (fst e_atrb) (snd e_atrb)) (ELit 16)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge. pose proof rz_is_range.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof lstr_lo.
    assert (Hab : split_lit e_atrandom = (fst e_atrb, snd e_atrb)) by (unfold e_atrb; destruct (split_lit e_atrandom); reflexivity).
    set (ab := fst e_atrb) in *. set (ak := snd e_atrb) in *.
    pose proof (split_u E0 e_atrandom ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    assert (Hak : ak = 456) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + CHEAD - 16) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    intros i Hi.
    destruct (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as [off (Hp & Hoff & Hmod & Hrd)].
    rewrite inp_argv, inp_envp, inp_rseq in Hp, Hoff, Hrd.
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
    pose proof len_av. pose proof len_ev. pose proof bsb_ge. pose proof rz_is_range.
    destruct (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as [off (Hp & Hoff & _ & _)].
    rewrite inp_argv, inp_envp, inp_rseq in Hp, Hoff.
    apply bv_eq. rewrite Hp, word_add_nat, u64_lit by (unfold CHEAD, usp in *; lia).
    pose proof u_e_atrandom as U. unfold uE in U. rewrite U. unfold CHEAD, usp. lia.
  Qed.

  Lemma init_kn_with_ok : forall atr, kentry_ok segs E0 Mr0 atr -> know_ok segs E0 Mr0 (init_kn_with atr A).
  Proof.
    intros atr Hatr.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof gap_range. pose proof chead_eq. pose proof length_bsb_sum. pose proof lstr_lo.
    pose proof brk_range as [B1 B2]. pose proof bsb_ge. pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof rz_is_range.
    pose proof (if_ph _ _ _ IMG) as (P1 & P2 & P3).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    unfold init_kn_with.
    destruct stack_window_ok as [SW1 SW2].
    apply Forall_app; split.
    { pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). pose proof PG_range as (G1 & G2 & G3 & QR & G5 & G6).
      destruct uE0_PQ as [UP UQ]. destruct u_e_top as [UT UT8].
      pose proof u_e_blk as (UB1 & UB2 & UB3 & UB4). pose proof u_e_pgslack as (US1 & US2 & US3 & US4).
      pose proof e_atr8m_range as AR. pose proof s01_in_strings. pose proof s0_in_strings. pose proof lstr_hi. pose proof L1_range.
      apply Forall_cons; [apply kr_ok; rewrite U1; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U2; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UP; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UQ; lia|].
      apply Forall_cons; [apply kr_ok; unfold eaddz, uE; rewrite mkAlu_denot, edenot_lit, u_add64, u64_lit by lia;
                          pose proof u_e_atrandom as U; unfold uE in U; rewrite U; rewrite Z.mod_small by lia; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_atr8; lia|].
      apply Forall_cons; [apply kr_ok; lia|].
      apply Forall_cons; [apply kr_ok; exact e_atr8m2_range|].
      apply Forall_cons; [apply kr_ok; rewrite US1; lia|].
      apply Forall_cons; [apply kr_ok; rewrite US2; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UT8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UT; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UB3; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UB2; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UB1; lia|].
      apply Forall_cons; [apply kr_ok; rewrite UB4; lia|].
      apply Forall_cons; [apply kr_ok; rewrite US4; lia|].
      apply Forall_cons; [apply kr_ok; rewrite US3; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_sp0; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_sp8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U3; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U4; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U5; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_L1; pose proof L1_range; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_uid; unfold valid_id in Huid; pose proof (u64_range uid); lia|].
      apply Forall_cons; [apply kr_ok; change (uE E0 (EVar V_HW)) with (bv_unsigned hw); pose proof (u64_range hw); lia|].
      apply Forall_cons; [apply kr_ok; rewrite U8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_r; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U6; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U7; unfold BRK_ASLR in *; lia|].
      apply Forall_cons; [exact SW1|].
      apply Forall_cons; [exact SW2|].
      apply Forall_cons; [exact argc_word_ok|].
      apply Forall_cons; [exact argv0_word_ok|].
      apply Forall_cons; [exact argv1_word_ok|].
      apply Forall_nil. }
    repeat (apply Forall_app; split).
    1-9: apply auxw_ok;
         [ lia
         | unfold AUXW, auxv_words, auxv_entries;
           cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
           try reflexivity .. ].
    all: try (rewrite edenot_lit; reflexivity).
    1: rewrite edenot_lit, P1; reflexivity.
    1: rewrite edenot_lit, P2; reflexivity.
    1: rewrite edenot_lit, P3; reflexivity.
    1: exact atr_ptr_eq.
    apply Forall_cons; [exact Hatr|].
    apply Forall_cons; [exact kimg_ok|].
    apply Forall_cons; [exact rw_window_ok|].
    apply Forall_nil.
  Qed.

  Lemma init_kn_ok : know_ok segs E0 Mr0 (init_kn A).
  Proof. exact (init_kn_with_ok _ atrandom_ok). Qed.
  (* [comment removed for export] *)
  Lemma init_kn_zero_ok : know_ok segs E0 Mr0 (init_kn_zero A).
  Proof. exact (init_kn_with_ok _ atrandom_zero_ok). Qed.

  (** LPS 727298f3: the rest of the vector, [AsanPlanCore.auxv_rest rz], as
      double-conversion/string_to_double_fuzzer's port proves it. *)
  (* a type word alone (the pairs whose value stays unknown) *)
  Lemma auxt_ok : forall i ty,
    (0 <= i < 27 + 2 * rz) ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    kentry_ok segs E0 Mr0 (auxt i ty).
  Proof.
    intros i ty Hi H1. unfold auxt.
    replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia.
    apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
  Qed.

  (* the whole vector is readable ([KUnk]): it is visible block memory below argv[0] *)
  Lemma auxv_unk_ok : kentry_ok segs E0 Mr0 (KUnk (SA (fst e_auxb) (snd e_auxb)) (ELit (AUXSZ rz))).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof chead_range. pose proof pad_range. pose proof gap_range.
    pose proof length_bsb_sum. pose proof lstr_lo. pose proof bsb_ge. pose proof rz_is_range.
    pose proof str0_hi. pose proof pad_eq.
    assert (Hab : split_lit e_auxv = (fst e_auxb, snd e_auxb)) by (unfold e_auxb; destruct (split_lit e_auxv); reflexivity).
    set (ab := fst e_auxb) in *. set (ak := snd e_auxb) in *.
    pose proof (split_u E0 e_auxv ab ak Hab) as Hs. rewrite u_e_auxv in Hs.
    assert (Hak : ak = 24) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + 8 * argc + 8 * envc + 24) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit (AUXSZ rz)) = AUXSZ rz)
      by (first [ apply elenZ_lit; unfold AUXSZ; lia | rewrite elenZ_lit; apply Z.mod_small; unfold AUXSZ; lia ]).
    cbn [kentry_ok]. rewrite Hst, Hl. unfold AUXSZ in *.
    split; [unfold flat; unfold usp in *; lia|].
    intros i Hi.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold usp, STR0 in *; lia].
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw _) by (rewrite u64_lit; unfold usp in *; lia). fold bsb.
    unfold stack_to_mem. fold usp. rewrite u64_lit by (unfold usp in *; lia).
    replace (usp <=? usp + 8 * argc + 8 * envc + 24 + i) with true by (symmetry; apply Z.leb_le; lia).
    cbv zeta.
    replace (usp + 8 * argc + 8 * envc + 24 + i - usp <? Z.of_nat (length bsb)) with true by (symmetry; apply Z.ltb_lt; lia).
    intros Hn. apply nth_error_None in Hn. lia.
  Qed.

  (* the CONFIG_RSEQ pair (26, 27), claimed only at [rz = 1], where it is in the vector *)
  Lemma auxv_rseq_ok :
    know_ok segs E0 Mr0 (if Z.eqb rz 1 then auxw 26 27 (ELit 28) ++ auxw 27 28 (ELit 32) else []).
  Proof.
    pose proof rz_is_range.
    assert (Hz : rz = rseq_z rseq) by reflexivity.
    destruct (Bool.bool_dec rseq true) as [Hrs|Hrs]; [|apply Bool.not_true_is_false in Hrs];
      rewrite Hrs in Hz; cbn in Hz; rewrite Hz; cbn [Z.eqb Pos.eqb]; [|constructor].
    apply Forall_app; split; apply auxw_ok;
      first [ lia
            | (unfold AUXW, auxv_words, auxv_entries; rewrite la_rseq_eq, Hrs;
               cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
               first [reflexivity | (rewrite edenot_lit; reflexivity)]) ].
  Qed.

  (* AT_NULL, at pair [26 + 2 rz] *)
  Lemma auxv_null_ok : know_ok segs E0 Mr0 (auxw (26 + 2 * rz) 0 (ELit 0)).
  Proof.
    pose proof rz_is_range.
    assert (Hz : rz = rseq_z rseq) by reflexivity.
    destruct (Bool.bool_dec rseq true) as [Hrs|Hrs]; [|apply Bool.not_true_is_false in Hrs];
      rewrite Hrs in Hz; cbn in Hz; rewrite Hz; cbn [Z.mul Z.add Pos.mul Pos.add];
      apply auxw_ok;
      first [ lia
            | (unfold AUXW, auxv_words, auxv_entries; rewrite la_rseq_eq, Hrs;
               cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
               first [reflexivity | (rewrite edenot_lit; reflexivity)]) ].
  Qed.

  Lemma auxv_rest_ok : know_ok segs E0 Mr0 (auxv_rest rz A).
  Proof.
    pose proof rz_is_range.
    unfold auxv_rest.
    (* AT_CLKTCK, AT_BASE, AT_FLAGS, AT_ENTRY, AT_GID, AT_EGID: below the CONFIG_RSEQ pair, so
       the same words under both layouts; AT_ENTRY from [Hapc], AT_GID/AT_EGID from [V_GID] *)
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
                | (rewrite edenot_lit; unfold entryw; rewrite Hapc; reflexivity) ] ]
      | ]).
    apply Forall_app; split; [exact auxv_rseq_ok|].
    apply Forall_app; split; [exact auxv_null_ok|].
    apply Forall_cons; [exact auxv_unk_ok|].
    (* the eleven type words *)
    do 11 (apply Forall_cons;
      [ apply auxt_ok;
        [ lia
        | unfold AUXW, auxv_words, auxv_entries;
          cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
          reflexivity ]
      | ]).
    apply Forall_cons; [apply kr_ok; rewrite uE0_r; lia|].
    apply Forall_nil.
  Qed.

  (* the launch knowledge with its [V_R] range pinned to [rz] in place ([AsanPlanCore.pin_r]) *)
  Lemma pin_kn_ok : know_ok segs E0 Mr0 (map (pin_r rz) (init_kn A)).
  Proof.
    pose proof rz_is_range. pose proof init_kn_ok as Hkn. unfold know_ok in *.
    apply Forall_map. eapply Forall_impl; [|exact Hkn]. intros K HK. unfold pin_r.
    destruct (kentry_eqb K (KRange (EVar V_R) 0 1)); [|exact HK].
    apply kr_ok; rewrite uE0_r; lia.
  Qed.
  (* LPS c0dd863a: argv[0]'s distance to the stack VMA's end, from the launch's string-area bounds *)
  Lemma strW_ok : kentry_ok segs E0 Mr0 (KRange e_strW 10 2097160).
  Proof.
    pose proof lstr_lo. pose proof lstr_hi. pose proof len_av. pose proof len_ev.
    apply kr_ok. rewrite u_e_strW. lia.
  Qed.
  Lemma init_r_kn_ok : know_ok segs E0 Mr0 (init_kn_r rz A).
  Proof.
    pose proof rz_is_range. unfold init_kn_r. apply Forall_app; split; [exact pin_kn_ok|].
    apply Forall_app; split; [exact auxv_rest_ok|].
    apply Forall_cons; [apply kr_ok; rewrite uE0_r; lia|].
    apply Forall_cons; [exact strW_ok | apply Forall_nil].
  Qed.
  Lemma pin_kn_zero_ok : know_ok segs E0 Mr0 (map (pin_r rz) (init_kn_zero A)).
  Proof.
    pose proof rz_is_range. pose proof init_kn_zero_ok as Hkn. unfold know_ok in *.
    apply Forall_map. eapply Forall_impl; [|exact Hkn]. intros K HK. unfold pin_r.
    destruct (kentry_eqb K (KRange (EVar V_R) 0 1)); [|exact HK].
    apply kr_ok; rewrite uE0_r; lia.
  Qed.
  Lemma init_r_kn_zero_ok : know_ok segs E0 Mr0 (init_kn_r_zero rz A).
  Proof.
    pose proof rz_is_range. unfold init_kn_r_zero. apply Forall_app; split; [exact pin_kn_zero_ok|].
    apply Forall_app; split; [exact auxv_rest_ok|].
    apply Forall_cons; [apply kr_ok; rewrite uE0_r; lia|].
    apply Forall_cons; [exact strW_ok | apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

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

  (* [comment removed for export] *)
  Lemma u_e_stkw : uE E0 (eaddz e_pgsp (-8388608)) = PGSP - 8388608
                   /\ uE E0 (eadd (ELit 8388608) (escale 16 (EVar V_S2))) = 8388608 + usp mod 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). pose proof u_e_pgsp as U. destruct uE0 as (_ & U2 & _).
    unfold uE in U, U2 |- *. unfold PGSP, pgdown. split.
    - unfold eaddz. rewrite mkAlu_denot, edenot_lit, u_add64.
      rewrite U. rewrite u_lit64. change ((-8388608) mod two64) with (two64 - 8388608). unfold two64.
      pose proof (Z.mod_pos_bound usp 4096 ltac:(lia)). lia.
    - unfold eadd, escale. rewrite mkAlu_denot, mkMd_denot, !edenot_lit, u_add64, u_mul64, !u64_lit by lia. rewrite U2.
      rewrite !Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Definition N2 : Z := 8388608 + usp mod 4096.
  Definition P3 : Z := 32768 * (usp / 32768).
  Definition N3 : Z := 4096 * ((usp mod 32768) / 4096) + 4096 * Q.
  Lemma PN3_range : usp - 32768 < P3 <= usp /\ P3 + N3 = utop /\ 4096 <= N3 <= 32768 + 4096 * 600 /\ 8388608 <= N2 < 8388608 + 4096
                    /\ PGSP - 8388608 + N2 = usp.
  Proof.
    pose proof usp_lo. pose proof usp_decomp as (D1 & D2 & D3 & D4 & D5). pose proof PG_range as (P1 & P2 & P3' & QR & _). unfold P3, N3, N2.
    pose proof (Z.div_mod usp 32768 ltac:(lia)). pose proof (Z.mod_pos_bound usp 32768 ltac:(lia)). pose proof (Z.mod_pos_bound usp 4096 ltac:(lia)).
    unfold PGSP, pgdown in *. lia.
  Qed.
  Lemma allowA_init : allowA A E0 cs0 =
    [(pagedown (img_lo A), pageup (img_lo A + (img_hi A - img_lo A)));
     (pagedown (shadow_off A + img_lo A / 8), pageup (shadow_off A + (img_lo A + (img_hi A - img_lo A)) / 8));
     (pagedown (PGSP - 8388608), pageup (PGSP - 8388608 + N2));
     (pagedown (shadow_off A + (PGSP - 8388608) / 8), pageup (shadow_off A + (PGSP - 8388608 + N2) / 8));
     (pagedown P3, pageup (P3 + N3));
     (pagedown (shadow_off A + P3 / 8), pageup (shadow_off A + (P3 + N3) / 8))].
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof u_e_stkw as [US UN2]. pose proof u_e_vis3b as UB. pose proof u_e_vis3n as UN. pose proof u_e_sp0 as USP.
    unfold allowA, cs0, init_acs_r, init_acs_of_with, init_vis. cbn [a_vis a_ghost app flat_map allow1 fst snd].
    unfold sh_lo, sh_hi. cbn [fst snd]. rewrite US, UN2. rewrite UB, UN. fold N2. fold P3. fold N3.
    unfold uE. rewrite !edenot_lit, !u64_lit by lia. unfold N2. reflexivity.
  Qed.

  Lemma abytes_init : A_bytes (allowA A E0 cs0) <= vis_cost (img_hi A - img_lo A) + vis_cost 8392704 + vis_cost 4194304
                      /\ vis_cost (img_hi A - img_lo A) + vis_cost 8392704 + vis_cost 4194304 <= LIMIT.
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof (if_shadow _ _ _ IMG) as S1. pose proof usp_lo as UL.
    pose proof PG_range as (Q1 & Q2 & Q3' & QR & Q5 & Q3). pose proof PN3_range as (PR & PE & NR & NR2 & NE).
    rewrite allowA_init. cbn [A_bytes fst snd]. unfold vis_cost, LIMIT.
    replace (img_lo A + (img_hi A - img_lo A)) with (img_hi A) by lia.
    assert (P1 : forall z, z mod 4096 = 0 -> pagedown z = z) by (intros z Hz; unfold pagedown; lia).
    assert (P2 : forall z, z mod 4096 = 0 -> pageup z = z) by (intros z Hz; unfold pageup; lia).
    rewrite (P1 (img_lo A) I3), (P2 (img_hi A) I4). clear P1 P2.
    (* [comment removed for export] *)
    first [clearbody Q | idtac]. first [clearbody W | idtac]. first [clearbody PGSP | idtac].
    clear - I1 I2 I3 I4 S1 UL Q3 PR PE NR NR2 NE.
    pose proof (pageup_minus_pagedown (shadow_off A + img_lo A / 8) (shadow_off A + img_hi A / 8) ltac:(lia)) as M1.
    pose proof (pageup_minus_pagedown (PGSP - 8388608) (PGSP - 8388608 + N2) ltac:(lia)) as M2.
    pose proof (pageup_minus_pagedown (shadow_off A + (PGSP - 8388608) / 8) (shadow_off A + (PGSP - 8388608 + N2) / 8) ltac:(lia)) as M3.
    pose proof (pageup_minus_pagedown P3 (P3 + N3) ltac:(lia)) as M4.
    pose proof (pageup_minus_pagedown (shadow_off A + P3 / 8) (shadow_off A + (P3 + N3) / 8) ltac:(lia)) as M5.
    split; lia.
  Qed.

  (* [comment removed for export] *)
  Theorem init_cs_ok : cs_ok segs A LIMIT SINV0 argH0 usp fs E0 cs0 R0 FULL0 model0.
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
    destruct abytes_init as [AB1 AB2].
    constructor; cbn [cs0 init_acs_r init_acs_of_with a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
      rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
    - exact init_regs_ok.
    - reflexivity.
    - exact init_r_kn_ok.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - split; [|split; [|split]].
      + pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
        pose proof (if_hull _ _ _ IMG) as (G1 & G2 & G3 & G4).
        pose proof (if_resx _ _ _ IMG) as [RX1 RX2]. pose proof resx_bytes_lo.
        exists RESX. split; [reflexivity|].
        split; [| split; [pose proof resx_len; lia | rewrite resx_sum; lia]].
        rewrite resx_eq. repeat constructor;
          cbn [fst snd];
          rewrite !u64_lit
            by (unfold mmap_base_min, mmap_base_max, sp_window_hi in *; lia);
          unfold KHI, mmap_base_min, mmap_base_max, sp_window_hi in *; lia.
      + constructor.
      + replace (m_kernel model0) with (in_kernel inp) by reflexivity.
        replace (vdso_top (m_vmmaps model0)) with VTOP
          by (symmetry; exact (vdso_top_init_model (segments_reserved segs) brk0 mbase sp lim inp)).
        apply incl_appr, incl_refl.
      + exact Hrdr.
    - exact Hlim.   (* [comment removed for export] *)
    - reflexivity.
    - constructor.   (* [comment removed for export] *)
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      exact (init_sp_ok_init_model (segments_reserved segs) brk0 mbase sp lim inp Hsp).
    - constructor.
    - constructor.
    - intros z Hz. exact Hz.
    - constructor.
    - constructor.
    - rewrite app_nil_r, sum_sizes_app, (if_sizes _ _ _ IMG), resx_sum. pose proof resx_bytes_lo. lia.
    - exact I.   (* [comment removed for export] *)
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7 & _). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.
    - lia.
    - lia.
    - exact AB1.
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
    - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
    - split; [intros; reflexivity | split; [intros; reflexivity | exact (conj Hlaunch Hlau)]].
    - (* [comment removed for export] *) split; [reflexivity | exact u_e_spw].
    - (* [comment removed for export] *) pose proof usp_lo. pose proof usp_fit. rewrite alloc_top0. unfold CEIL, TOPMAX. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem init_cs_ok_zero : cs_ok segs A LIMIT SINV0 argH0 usp fs E0 cs0z R0 FULL0 model0.
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
    destruct abytes_init as [AB1 AB2].
    change (allowA A E0 cs0) with (allowA A E0 (init_acs_r_zero rz A)) in AB1.   (* [comment removed for export] *)
    constructor; unfold cs0z; cbn [init_acs_r_zero init_acs_of_with a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
      rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
    - exact init_regs_ok.
    - reflexivity.
    - exact init_r_kn_zero_ok.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - split; [|split; [|split]].
      + pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
        pose proof (if_hull _ _ _ IMG) as (G1 & G2 & G3 & G4).
        pose proof (if_resx _ _ _ IMG) as [RX1 RX2]. pose proof resx_bytes_lo.
        exists RESX. split; [reflexivity|].
        split; [| split; [pose proof resx_len; lia | rewrite resx_sum; lia]].
        rewrite resx_eq. repeat constructor;
          cbn [fst snd];
          rewrite !u64_lit
            by (unfold mmap_base_min, mmap_base_max, sp_window_hi in *; lia);
          unfold KHI, mmap_base_min, mmap_base_max, sp_window_hi in *; lia.
      + constructor.
      + replace (m_kernel model0) with (in_kernel inp) by reflexivity.
        replace (vdso_top (m_vmmaps model0)) with VTOP
          by (symmetry; exact (vdso_top_init_model (segments_reserved segs) brk0 mbase sp lim inp)).
        apply incl_appr, incl_refl.
      + exact Hrdr.
    - exact Hlim.   (* [comment removed for export] *)
    - reflexivity.
    - constructor.   (* [comment removed for export] *)
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      exact (init_sp_ok_init_model (segments_reserved segs) brk0 mbase sp lim inp Hsp).
    - constructor.
    - constructor.
    - intros z Hz. exact Hz.
    - constructor.
    - constructor.
    - rewrite app_nil_r, sum_sizes_app, (if_sizes _ _ _ IMG), resx_sum. pose proof resx_bytes_lo. lia.
    - exact I.   (* [comment removed for export] *)
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7 & _). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.
    - lia.
    - lia.
    - exact AB1.
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
    - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
    - split; [intros; reflexivity | split; [intros; reflexivity | exact (conj Hlaunch Hlau)]].
    - (* [comment removed for export] *) split; [reflexivity | exact u_e_spw].
    - (* [comment removed for export] *) pose proof usp_lo. pose proof usp_fit. rewrite alloc_top0. unfold CEIL, TOPMAX. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem init_cfg_eq :
    init_config segs apc ph sp brk0 mbase rdraw lim inp = cfg_of segs R0 (a_entry A) FULL0 model0.
  Proof.
    (* [comment removed for export] *)
    unfold init_config, cfg_of, FULL0, entryw. rewrite init_mkst, Hapc. reflexivity.
  Qed.
End Init.

(* [argH0_high_s] as the consumers call it: its statement reads only [sp rdraw argv envp kb execfn]
   and the two premises, whatever else the section's discharge put in front of it. *)
Lemma argH0_high : forall sp rdraw argv envp kb execfn, valid_sp sp -> valid_argv argv ->
  forall E a, argH0 sp rdraw argv envp kb execfn E a = true -> CEIL <= bv_unsigned a /\ bv_unsigned sp <= bv_unsigned a.
Proof. intros sp rdraw argv envp kb execfn Hsp Hva E a H. exact (argH0_high_s 0%N sp rdraw argv envp kb execfn Hsp Hva E a H). Qed.

(* [comment removed for export] *)
Definition SINVL (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte))
    (uid hw : word) (L : LaunchX) : env -> (word -> option byte) -> Prop :=
  SINV0 ph (lx_apc L) sp rdraw brk0 (lx_mbase L) argv envp (lx_fs L) (lx_stdin L) uid (lx_gid L) hw
    (lx_groups L) (lx_net L) (lx_nofile L) (lx_sigmask L) (lx_kb L) (lx_execfn L) (lx_crd L) (lx_sgd L) (lx_sgt L).

Lemma SINVL_frame : forall ph sp rdraw brk0 argv envp uid hw L E M M',
  (forall a, argH0 sp rdraw argv envp (lx_kb L) (lx_execfn L) E a = true -> M' a = M a) ->
  SINVL ph sp rdraw brk0 argv envp uid hw L E M -> SINVL ph sp rdraw brk0 argv envp uid hw L E M'.
Proof.
  intros ph sp rdraw brk0 argv envp uid hw L E M M' Hf HS. unfold SINVL, SINV0 in *.
  destruct HS as (H1 & H2 & H3). split; [exact H1|]. split; [|exact H3].
  intros a Ha. rewrite (Hf a Ha). exact (H2 a Ha).
Qed.

Lemma SINVL_agree : forall ph sp rdraw brk0 argv envp uid hw L E E' M,
  env_agree NX0 E E' ->
  SINVL ph sp rdraw brk0 argv envp uid hw L E M -> SINVL ph sp rdraw brk0 argv envp uid hw L E' M.
Proof.
  intros ph sp rdraw brk0 argv envp uid hw L E E' M [Hag _] HS. unfold SINVL, SINV0 in *.
  destruct HS as [H1 H2]. split; [|exact H2].
  intros n Hn. rewrite <- (Hag n) by (unfold NX0 in *; lia). apply H1. exact Hn.
Qed.

Lemma SINVL_pgsp : forall ph sp rdraw brk0 argv envp uid hw L, valid_sp sp ->
  forall E M, SINVL ph sp rdraw brk0 argv envp uid hw L E M -> uE E e_pgsp = pgdown (bv_unsigned sp).
Proof. intros ph sp rdraw brk0 argv envp uid hw L Hsp E M HS. unfold SINVL in HS. eapply SINV0_pgsp; eassumption. Qed.

(* The launch's process input, mapping base and validity facts in terms of a [LaunchX]. *)
Definition inpL (argv envp : list (list byte)) (uid hw : word) (L : LaunchX) : ProcInput :=
  inp argv envp (lx_fs L) (lx_stdin L) uid (lx_gid L) hw (lx_groups L) (lx_net L) (lx_nofile L) (lx_sigmask L)
    (lx_kb L) (lx_execfn L) (lx_crd L) (lx_sgd L) (lx_sgt L).

Lemma SINVL_launch : forall ph sp rdraw brk0 argv envp uid hw L E M,
  SINVL ph sp rdraw brk0 argv envp uid hw L E M ->
  valid_launch (inpL argv envp uid hw L) /\ entry_launch_ok_va Sv48 (mkEntry sp brk0 (lx_mbase L) rdraw) (inpL argv envp uid hw L).
Proof. intros ph sp rdraw brk0 argv envp uid hw L E M HS. unfold SINVL, SINV0 in HS. destruct HS as (_ & _ & H). exact H. Qed.

(* What the launch gives a start-up proof, beyond the separate [valid_*] premises. *)
Definition launchL (A : atable) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte))
    (uid hw : word) (L : LaunchX) : Prop :=
  Z.of_N (lx_apc L) = a_entry A /\ valid_mmap_base (lx_mbase L) /\ lx_crd L = true
  /\ valid_launch (inpL argv envp uid hw L)
  /\ entry_launch_ok_va Sv48 (mkEntry sp brk0 (lx_mbase L) rdraw) (inpL argv envp uid hw L).

Definition INITL (segs : list Segment) (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 : word) (lim : Z)
    (argv envp : list (list byte)) (uid hw : word) (L : LaunchX) :=
  init_config segs (lx_apc L) ph sp brk0 (lx_mbase L) rdraw lim (inpL argv envp uid hw L).

Definition E0L (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word)
    (L : LaunchX) : env :=
  E0 sp rdraw brk0 argv envp uid (lx_gid L) hw (lx_kb L) (lx_execfn L).

Definition FULL0L (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (argv envp : list (list byte)) (uid hw : word)
    (L : LaunchX) : word -> option byte :=
  FULL0 ph (lx_apc L) sp rdraw (lx_mbase L) argv envp (lx_fs L) (lx_stdin L) uid (lx_gid L) hw (lx_groups L)
    (lx_net L) (lx_nofile L) (lx_sigmask L) (lx_kb L) (lx_execfn L) (lx_crd L) (lx_sgd L) (lx_sgt L).

Definition model0L (segs : list Segment) (sp : word) (rdraw : EntryDraw) (brk0 : word) (lim : Z)
    (argv envp : list (list byte)) (uid hw : word) (L : LaunchX) : Model :=
  model0 segs sp rdraw brk0 (lx_mbase L) lim argv envp (lx_fs L) (lx_stdin L) uid (lx_gid L) hw (lx_groups L)
    (lx_net L) (lx_nofile L) (lx_sigmask L) (lx_kb L) (lx_execfn L) (lx_crd L) (lx_sgd L) (lx_sgt L).

Theorem init_cs_okL : forall segs A ph sp rdraw brk0 lim argv envp uid hw L,
  img_facts segs A ph -> valid_sp sp -> valid_brk segs brk0 -> LIMIT <= lim -> valid_argv argv -> valid_envp envp ->
  entry_stack_fits sp argv envp -> valid_id uid -> launchL A sp rdraw brk0 argv envp uid hw L ->
  cs_ok segs A LIMIT (SINVL ph sp rdraw brk0 argv envp uid hw L) (argH0 sp rdraw argv envp (lx_kb L) (lx_execfn L))
    (bv_unsigned sp) (lx_fs L) (E0L sp rdraw brk0 argv envp uid hw L) (init_acs_r (rseq_z (kb_rseq (lx_kb L))) A)
    (R0 sp) (FULL0L ph sp rdraw argv envp uid hw L) (model0L segs sp rdraw brk0 lim argv envp uid hw L).
Proof.
  intros segs A ph sp rdraw brk0 lim argv envp uid hw L IMG Hsp Hbrk Hlim Hva Hve Hfit Huid (Hapc & Hmb & Hrdr & Hlaunch & Hlau).
  exact (init_cs_ok segs A ph (lx_apc L) sp rdraw brk0 (lx_mbase L) lim argv envp (lx_fs L) (lx_stdin L) uid (lx_gid L) hw
           (lx_groups L) (lx_net L) (lx_nofile L) (lx_sigmask L) (lx_kb L) (lx_execfn L) (lx_crd L) (lx_sgd L) (lx_sgt L)
           IMG Hapc Hsp Hbrk Hmb Hlim Hva Hve Hfit Huid Hrdr Hlaunch Hlau).
Qed.

Theorem init_cfg_eqL : forall segs A ph sp rdraw brk0 lim argv envp uid hw L,
  Z.of_N (lx_apc L) = a_entry A ->
  INITL segs ph sp rdraw brk0 lim argv envp uid hw L
  = cfg_of segs (R0 sp) (a_entry A) (FULL0L ph sp rdraw argv envp uid hw L) (model0L segs sp rdraw brk0 lim argv envp uid hw L).
Proof.
  intros segs A ph sp rdraw brk0 lim argv envp uid hw L Hapc.
  exact (init_cfg_eq segs A ph (lx_apc L) sp rdraw brk0 (lx_mbase L) lim argv envp (lx_fs L) (lx_stdin L) uid (lx_gid L) hw
           (lx_groups L) (lx_net L) (lx_nofile L) (lx_sigmask L) (lx_kb L) (lx_execfn L) (lx_crd L) (lx_sgd L) (lx_sgt L) Hapc).
Qed.

(* [comment removed for export] *)
(* Any launch input is the section's [inp] over its own fields: the image and the declared /tmp
   enter the run only through [in_fs] (State.v: [in_fs] seeds the image with [in_tmp], and the
   empty declaration gives back the image by computation). *)
Lemma init_config_inp_of : forall segs apc ph sp rdraw brk0 mbase lim (i : ProcInput),
  in_abort_terminal i = false -> in_va_size i = Sv48 ->
  in_kernel i = recorded_kernel (in_kernel i) ->
  init_config segs apc ph sp brk0 mbase rdraw lim i
  = init_config segs apc ph sp brk0 mbase rdraw lim
      (inp (in_argv i) (in_envp i) (in_fs i) (mkInStreams (in_stdin i) (in_urandom i))
           (in_uid i) (in_gid i) (in_hwcap i) (in_groups i) (in_net i) (in_nofile i) (in_sigmask i)
           (in_kernel i) (in_execfn i) (in_channel_reader i) (in_sigpipe_default i) (in_sigpipe_terminal i)).
Proof.
  intros segs apc ph sp rdraw brk0 mbase lim i Hab Hva Hrk.
  unfold inp. rewrite <- Hrk.
  destruct i. simpl in Hab, Hva. subst. reflexivity.
Qed.

(* The launch record of an input, at entry pc [apc] and mapping base [mbase]. *)
Definition LX_of (apc : N) (mbase : word) (i : ProcInput) : LaunchX :=
  mkLaunchX apc mbase (in_fs i) (mkInStreams (in_stdin i) (in_urandom i)) (in_gid i) (in_groups i) (in_net i)
    (in_nofile i) (in_sigmask i) (in_kernel i) (in_execfn i) (in_channel_reader i) (in_sigpipe_default i)
    (in_sigpipe_terminal i).

Lemma init_config_LX : forall segs apc ph sp rdraw brk0 mbase lim (i : ProcInput),
  in_abort_terminal i = false -> in_va_size i = Sv48 ->
  in_kernel i = recorded_kernel (in_kernel i) ->
  init_config segs apc ph sp brk0 mbase rdraw lim i
  = INITL segs ph sp rdraw brk0 lim (in_argv i) (in_envp i) (in_uid i) (in_hwcap i) (LX_of apc mbase i).
Proof. intros. rewrite init_config_inp_of by assumption. reflexivity. Qed.

(* What the launch gives, read off a valid input and a valid entry. *)
Lemma launchL_of_input : forall A apc sp rdraw brk0 mbase (i : ProcInput),
  Z.of_N apc = a_entry A -> valid_mmap_base mbase -> valid_input i ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) i ->
  launchL A sp rdraw brk0 (in_argv i) (in_envp i) (in_uid i) (in_hwcap i) (LX_of apc mbase i).
Proof.
  intros A apc sp rdraw brk0 mbase i Hapc Hmb Hvi Hlau.
  pose proof (valid_input_channel_reader _ Hvi) as Hrdr. pose proof (valid_input_launch _ Hvi) as Hvl.
  pose proof (valid_input_abort_terminal _ Hvi) as Hab. pose proof (valid_input_va_size _ Hvi) as Hva.
  assert (Hrk : in_kernel i = recorded_kernel (in_kernel i)) by (unfold valid_input in Hvi; tauto).
  unfold launchL, inpL. change (lx_kb (LX_of apc mbase i)) with (in_kernel i).
  unfold inp. rewrite <- Hrk.
  destruct i. simpl in Hab, Hva. subst.
  split; [exact Hapc|]. split; [exact Hmb|]. split; [exact Hrdr|]. split; [exact Hvl | exact Hlau].
Qed.
