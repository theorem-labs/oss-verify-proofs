(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch premises entry_launch_ok_va and valid_input; the run's CONFIG_RSEQ flag; the start-up stack anchored at its top; AT_EXECFN; the launch's group id; the vDSO's mappings and steps; the channel-reader flag that fdchan asks for; the launch's channel-reader and SIGPIPE fields; the launch's SIGPIPE disposition left free): changed img_facts, stack_image_size, inp, bsb, W, vals0, argH0, SINV0 and 42 more; added apc, kb, execfn, sdef, Hapc, Hlaunch, Hlau, Hvi and 55 more; removed SIMG, W_range; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1d YK1a YK15 YK00 YK19 YK12 YK03 YK04 YK05 YK08 YK0g.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK0c YK0e YK0f.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YA0c YA0e.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK06.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
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
if_shadow : 0 <= shadow_off A <= 2 ^ 47;
if_resx  : (2 <= n_resx A)%nat /\ (20 <= p_resx A)%nat
}.
Definition stack_image_size (sp top : word) : Z :=
(bv_unsigned top - bv_unsigned sp)%Z.
Section c.
Variable segs : list Segment.
Variable A : atable.
Variable ph : PhdrInfo.
Variable apc : N.
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
Variable kb : KernelBuild.
Variable execfn : list byte.
(* The SIGPIPE disposition the launcher leaves: LPS 727298f3's [Run.valid_input] leaves
   [in_sigpipe_default] FREE, so it is a variable here; the input used to pin it [true]. *)
Variable sdef : bool.
Hypothesis IMG : img_facts segs A ph.
Hypothesis Hapc : Z.of_N apc = a_entry A.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk segs brk0.
Hypothesis Hmb : valid_mmap_base mbase.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Huid : valid_id uid.
Hypothesis Hhw : valid_hwcap hw.
Hypothesis Hzr : YK06.zero_random_draw (ed_random rdraw).
Definition inp : ProcInput := mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp kb execfn true sdef false.
Hypothesis Hnof : valid_nofile nofile.
Hypothesis Hsig : valid_sigmask inp.
Hypothesis Hlaunch : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
(* The whole-record pin [kb = default_kernel] is REPLACED by [valid_input] ALONE.  Its conjunct
   17 fixes only the nine fields [Run.recorded_kernel] copies and leaves [kb_thp], [kb_aslr],
   [kb_guard], [kb_rnd_bits] and [kb_rseq] FREE
   (75d69e00:theories/LinuxProcessSem/Run.v:4596).
   [Hypothesis Hrseq : kb_rseq kb = true] stood here beside it and is DELETED 2026-11-06.  It
   was a pin on one of the five FREE fields, so no caller could ever discharge it and it
   narrowed the published theorem to rseq-on kernels; a one-field pin on a free field is still
   a pin.  What it paid for was [YK09.AUXSZ] (then the closed 464) and [YK09.AUXV_NULL_IX]
   (then the closed 28) sitting as literals inside the ASAN plan term [init_acs_of_g], which
   this section's [atr_ptr_eq] and [auxw_ok] ladder reduce through.  Both now take the flag,
   so the plan this section proves sound is the plan for the run's OWN kernel, at [RZ] below.
   Thirteen of the thirteen fields are free. *)
Hypothesis Hvi : valid_input inp.
Let rseq : bool := kb_rseq kb.
Let entryw : word := Z_to_bv 64 (Z.of_N apc).
Let la : LaunchAuxv := launch_auxv inp sp mbase.
Let top : word := ed_top rdraw.
Lemma inp_argv : in_argv inp = argv.        Proof. reflexivity. Qed.
Lemma inp_envp : in_envp inp = envp.        Proof. reflexivity. Qed.
Lemma inp_uid : in_uid inp = uid.           Proof. reflexivity. Qed.
Lemma inp_gid : in_gid inp = gid.           Proof. reflexivity. Qed.
Lemma inp_hwcap : in_hwcap inp = hw.        Proof. reflexivity. Qed.
Lemma inp_kernel : in_kernel inp = kb.      Proof. reflexivity. Qed.
Lemma inp_execfn : in_execfn inp = execfn.  Proof. reflexivity. Qed.
Lemma inp_rseq : kb_rseq (in_kernel inp) = rseq. Proof. reflexivity. Qed.
Lemma la_rseq_eq : la_rseq la = rseq.       Proof. reflexivity. Qed.
(* [rseq_true : rseq = true] and [la_rseq_true : la_rseq la = true] are DELETED: with [rseq]
   meaning the run's own [kb_rseq kb] they are FALSE for an rseq-off build.  [inp_rseq] and
   [la_rseq_eq] above SURVIVE -- those are the equations the consumers actually need, and the
   model proves the second outright ([YK11.la_rseq_launch_auxv], the same fact as
   75d69e00:theories/Common/PropExec.v:2506).
   [RZ] is that flag as the PLAN spells it, [YK09.rseq_z]'s 0 or 1; it is what instantiates
   the [r] of [AUXSZ], [AUXV_NULL_IX], [e_atrandom], [e_str0], [e_str1], [e_argv1w],
   [e_atrb], [init_kn_with], [init_kn], [init_acs_of] and [init_acs_of_g]. *)
Let RZ : Z := rseq_z rseq.
Lemma rz_range : 0 <= RZ <= 1.
Proof. unfold RZ. apply rseq_z_range. Qed.
(* The plan's smart constructors only reduce on CLOSED literals -- [mkAlu ALU_ADD] ends in
   [unlin]'s [if Z.eqb (fst x) 0 ...] (YK0c.v:252-256) over a constant [snorm] built with
   [Z.leb (2 ^ 63) m] (YK0c.v:93-95) -- so [e_atrandom RZ] is a stuck match until [RZ] is a
   literal.  This is the case analysis that supplies one, and the pair [(rseq, RZ)] is split
   together because the vector's SHAPE needs the boolean and its INDICES need the integer. *)
Lemma rseq_cases : (rseq = true /\ RZ = 1) \/ (rseq = false /\ RZ = 0).
Proof. unfold RZ, rseq_z, rseq. destruct (kb_rseq kb); [left | right]; split; reflexivity. Qed.
Lemma auxsz_rz : AUXSZ RZ = Z.of_nat (auxv_size rseq).
Proof. unfold RZ. apply AUXSZ_of. Qed.
Lemma auxv_count_rz : Z.of_nat (auxv_count rseq) = 27 + 2 * RZ.
Proof. unfold RZ, rseq_z, rseq. destruct (kb_rseq kb); vm_compute; reflexivity. Qed.
Let bsb := entry_stack_image inp mbase ph entryw sp rdraw.
Let usp := bv_unsigned sp.
Definition TOP : Z := bv_unsigned sp - 8388608.
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
Definition vals0 : list word :=
[Z_to_bv 64 (usp / 32768); Z_to_bv 64 argc; Z_to_bv 64 envc; Z_to_bv 64 L0; Z_to_bv 64 W;
Z_to_bv 64 (bv_unsigned brk0 / 4096); Z_to_bv 64 ((usp mod 32768) / 16); Z_to_bv 64 L1; uid;
Z_to_bv 64 G; hw; gid].
Definition E0 : env := Env (fun n => nth n vals0 (Z_to_bv 64 0))
(fun k => if Nat.eqb k K_RND then at_random_bytes (ed_random rdraw) else []).
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
intros E a H. unfold argH0 in H. unfold TOP.
pose proof (valid_argv_len argv Hva).
assert (HC : 0 <= CHEAD) by (unfold CHEAD; lia).
assert (HW : 0 <= W) by (unfold W; lia).
apply orb_prop in H as [H|H]; apply andb_prop in H as [H _]; apply Z.leb_le in H;
(* rz_range: CHEAD carries 472 + 32*RZ since the parameterisation, so every lia whose goal
   unfolds STR0 or CHEAD needs RZ bounded or it has nothing to do.  Adding a true hypothesis
   to a lia context is monotone - it cannot break a proof that already closed. *)
unfold usp, argc, envc, STR0 in H; pose proof rz_range; lia.
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
(* WAS [CHEAD = 8 * argc + 8 * envc + 504 + 8 * G], which is this expression at [RZ = 1]:
   [auxv_size] enters [block_head_size] ADDITIVELY (75d69e00:StackLayout.v:399-401), so the
   flag costs one [+ 32 * RZ] term and no case split in the arithmetic. *)
Lemma chead_eq : CHEAD = 8 * argc + 8 * envc + 472 + 32 * RZ + 8 * G.
Proof.
unfold CHEAD, G, argc, envc, block_head_size, block_items.
pose proof auxsz_rz as HA. unfold AUXSZ in HA. lia.
Qed.
(* The lower bound WAS 512, which is this bound at [RZ = 1]; an rseq-off kernel lays down a
   432-byte vector, 32 bytes shorter, so the head starts at 480.  [chead_range] has no users
   anywhere under proofs/ -- firing control for that zero, same grep, same path, same
   revision: [chead_eq] has 13. *)
Lemma chead_range : 480 <= CHEAD <= 10752.
Proof. pose proof chead_eq. pose proof len_av. pose proof len_ev. pose proof gap_range. pose proof rz_range. lia. Qed.
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
Lemma lstr_hi : LSTR + 8 * argc + 8 * envc <= 2097152.
Proof.
destruct Hlaunch as [_ Hb]. unfold launch_bytes, e2big_limit in Hb.
rewrite inp_argv, inp_envp, inp_execfn in Hb. unfold LSTR, argc, envc. lia.
Qed.
Lemma pad_bounds_Z : 0 <= utop - 8 - LSTR - usp - CHEAD <= 4110.
Proof.
destruct Hlau as (_ & Hsw & _). destruct Hsw as (_ & Hslo & Hshi).
unfold launch_sp_lo, launch_sp_hi, align_down16 in Hslo, Hshi.
rewrite inp_argv, inp_envp, inp_execfn, inp_rseq in Hslo, Hshi.
change (ed_top rdraw) with top in Hslo, Hshi.
fold LSTR in Hslo, Hshi. fold CHEAD in Hslo, Hshi. fold utop usp in Hslo, Hshi.
pose proof (Z.mod_pos_bound (utop - 8 - LSTR) 16 ltac:(lia)).
pose proof (Z.mod_pos_bound (utop - 8 - LSTR - 4095) 16 ltac:(lia)).
pose proof rz_range. lia.
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
(* WAS [8 * argc + 8 * envc + 514 <= ...], which is this bound at [RZ = 1].  It is
   [chead_eq]'s constant plus the two summands [length_bsb_sum] adds under their own lower
   bounds: [472 + 32*RZ] from CHEAD, [0] from W ([pad_range]), [2] from LSTR ([lstr_lo]), [8]
   from the slot, [8*G >= 0] from [gap_range] -- so 482 + 32*RZ, and 514 at RZ = 1.  At
   RZ = 0 the 514 was not merely unproved, it was FALSE by 32 bytes, and [lia] reported it as
   "No applicable tactic" in farm round 20261106t073727z-309fe1.  Every use site below is
   given [rz_range] so the bound is still worth 514 where the flag is on. *)
Lemma bsb_ge : 8 * argc + 8 * envc + 482 + 32 * RZ <= Z.of_nat (length bsb).
Proof.
pose proof length_bsb_sum. pose proof chead_eq. pose proof lstr_lo. pose proof pad_range.
pose proof gap_range. pose proof rz_range. lia.
Qed.
Lemma str0_hi : STR0 + LSTR + 8 = utop.
Proof. unfold STR0. pose proof pad_eq. pose proof rz_range. lia. Qed.
Lemma brk_range : img_hi A <= bv_unsigned brk0 <= img_hi A + BRK_ASLR /\ bv_unsigned brk0 mod 4096 = 0.
Proof.
destruct Hbrk as (H1 & H2 & H3). unfold brk_aslr_max in H2. unfold page_size in H3.
rewrite (if_top _ _ _ IMG) in H1, H2. unfold BRK_ASLR. lia.
Qed.
Lemma usp_hi : usp + 192 <= 2 ^ 47.
Proof. pose proof usp_fit. pose proof bsb_ge. pose proof len_av. pose proof len_ev. pose proof rz_range. lia. Qed.
Lemma uE0 :
uE E0 (EVar V_S1) = usp / 32768 /\ uE E0 (EVar V_S2) = (usp mod 32768) / 16
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
Lemma u_e_atrandom : uE E0 (e_atrandom RZ) = usp + CHEAD - 16.
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
pose proof gap_range. pose proof chead_eq. pose proof bsb_ge. pose proof rz_range.
destruct uE0 as (_ & _ & _ & _ & _ & _ & _ & U8).
pose proof u_e_auxv as UA. unfold e_atrandom, eadd, eaddz, escale, uE, AUXSZ in *.
rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UA, U8. rewrite !Z.mod_small by lia. lia.
Qed.
Lemma u_e_str0 : uE E0 (e_str0 RZ) = STR0.
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
pose proof pad_range. pose proof chead_eq. pose proof gap_range. pose proof bsb_ge. pose proof rz_range.
destruct uE0 as (_ & _ & _ & _ & _ & U6 & _).
pose proof u_e_atrandom as UA. unfold e_str0, eadd, eaddz, uE, STR0 in *.
rewrite !mkAlu_denot, !edenot_lit.
rewrite !u_add64, !u64_lit by lia. rewrite UA, U6. rewrite !Z.mod_small by lia. lia.
Qed.
Lemma u_e_str1 : uE E0 (e_str1 RZ) = STR0 + L0 + 1.
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
pose proof pad_range. pose proof chead_eq. pose proof gap_range. pose proof bsb_ge. pose proof rz_range.
pose proof length_bsb_sum. pose proof lstr_hi.
destruct uE0 as (_ & _ & _ & _ & U5 & _).
assert (HL0 : 0 <= L0 <= 131071).
{ unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
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
Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.
Definition FULL0 : word -> option byte := wrap_mem inp mbase ph entryw sp rdraw.
Definition model0 : Model :=
with_vdso (vdso_run_init (ed_vdso rdraw))
(init_model (segments_reserved segs) brk0 mbase sp LIMIT inp).
Let cs0 := init_acs_of RZ A.
Let cs0z := init_acs_of_zero RZ A.
Let hid0 := hid A TOP argH0 E0 cs0 model0.
Let Mr0 := Mr A TOP argH0 E0 cs0 model0 FULL0.
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
(* LPS 727298f3: [cs_ok]'s [co_rdr].  The launch input of this Section spells its
   channel-reader flag [true] ([inp] above), so the initial model's flag is a
   computation on that input, not an assumption: [Run.valid_input]'s own conjunct
   [in_channel_reader inp = true] is what the statements quantify over. *)
Lemma model0_channel_reader : m_channel_reader model0 = true.
Proof. reflexivity. Qed.
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
(* [vdso_reserved] reads only [vdso_len] and [vdso_text_pages], both of which read only
   [kb_vdso] -- one of the nine fields [Run.recorded_kernel] copies from [default_kernel].  So
   [valid_input] alone moves it, by the model's own [f_equal] idiom (the proof of
   [Run.valid_input_vdso_text_pages], Run.v:5711, is exactly this shape).  No kernel pin. *)
Lemma inp_vdso_reserved : forall t, vdso_reserved (in_kernel inp) t = vdso_reserved default_kernel t.
Proof. intros t. exact (f_equal (fun k => vdso_reserved k t) (valid_input_recorded_kernel inp Hvi)). Qed.
Lemma resx_eq : RESX = [(Z_to_bv 64 (VTOP - 24576), Z_to_bv 64 16384);
(Z_to_bv 64 (VTOP - 24576 + 16384), Z_to_bv 64 8192)].
Proof.
pose proof vtop_range as [[T1 T2] T3].
unfold RESX. rewrite (inp_vdso_reserved VTOP). unfold vdso_reserved. cbv zeta.
replace (vdso_len default_kernel) with 24576 by (vm_compute; reflexivity).
replace (vdso_vvar_pages * page_size)%Z with 16384 by (vm_compute; reflexivity).
replace (vdso_text_pages default_kernel * page_size)%Z with 8192 by (vm_compute; reflexivity).
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
apply rdn_ext; [exact Hn|]. intros x Hx. apply Mr0_visible; [unfold usp, TOP in *; lia | apply Hvis; exact Hx].
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
(* rz_range added: STR0 unfolds to usp + CHEAD + W, and chead_eq now carries 472 + 32*RZ
   rather than a closed constant, so lia sees an UNBOUNDED RZ and has nothing to do -
   which it reports as "No applicable tactic", its own `first` running out, not as a
   missing hypothesis.  rz_range (0 <= RZ <= 1) is already proved at :104 and the chain
   at :188 in this same file poses it for exactly this reason.  Donor is in-file. *)
pose proof gap_range. pose proof str0_hi. pose proof lstr_lo. pose proof rz_range. unfold STR0 in *. lia.
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
Lemma auxv_word_ok : forall (j : nat) v,
(j < 2 * auxv_count rseq)%nat ->
nth j AUXW (Z_to_bv 64 0) = edenot E0 v ->
kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 v).
Proof.
intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum.
(* auxv_count_rz added: the hypothesis is Hj : (j < 2 * auxv_count rseq)%nat, and with
   rseq free lia cannot use it until auxv_count rseq is arithmetic.  auxv_count_rz
   (Z.of_nat (auxv_count rseq) = 27 + 2 * RZ) is proved at :115 and :581/:582 pose it
   for exactly this reason; this proof posed rz_range but not it.  The bound itself is
   already in the owner's prescribed form - j < 2 * auxv_count, not a literal 20 - so
   this is the missing FACT about the count, not a stale vector. *)
pose proof lstr_lo. pose proof bsb_ge. pose proof rz_range. pose proof auxv_count_rz.
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
pose proof (read_auxv_word segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi' j ltac:(rewrite inp_rseq; exact Hj)) as RW.
rewrite inp_rseq in RW. exact RW.
Qed.
Lemma auxw_ok : forall i ty v,
(0 <= i <= AUXV_NULL_IX RZ) ->
nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
nth (Z.to_nat (2 * i + 1)) AUXW (Z_to_bv 64 0) = edenot E0 v ->
know_ok segs E0 Mr0 (auxw i ty v).
Proof.
intros i ty v Hi H1 H2. unfold auxw.
constructor; [|constructor; [|constructor]].
- replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia. apply auxv_word_ok; [pose proof auxv_count_rz; pose proof rz_range; unfold AUXV_NULL_IX in *; lia|]. rewrite H1. reflexivity.
- replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia. apply auxv_word_ok; [pose proof auxv_count_rz; pose proof rz_range; unfold AUXV_NULL_IX in *; lia|]. exact H2.
Qed.
Lemma kr_ok : forall e lo hi, lo <= uE E0 e <= hi -> kentry_ok segs E0 Mr0 (KRange e lo hi).
Proof. intros e lo hi H. cbn [kentry_ok]. unfold uE in H. exact H. Qed.
Lemma Mr0_below : forall a : word, usp - 6144513 <= bv_unsigned a < usp -> Mr0 a = Some (Z_to_bv 8 0).
Proof.
intros a Ha. pose proof usp_lo. pose proof len_av.
rewrite Mr0_visible; [apply FULL0_below; exact Ha | unfold usp, TOP in *; lia | apply not_argH0; lia].
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
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge. pose proof rz_range.
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
Lemma cat_argv0_eq :
bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) = STR0.
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum.
rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0 Hav0).
change (total_arg_bytes_nat (firstn 0 (in_argv inp))) with 0%nat.
rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
rewrite inp_kernel. change (in_execfn inp) with execfn.
change (in_argv inp) with argv. change (in_envp inp) with envp.
unfold STR0, CHEAD, W, usp, rseq, top, cat_string_off in *.
rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia.
Qed.
Lemma argv0_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 8) 8 (e_str0 RZ)).
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge. pose proof rz_range.
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
Lemma argv1_word_ok : kentry_ok segs E0 Mr0 (kw_argv1 (e_argv1w RZ)).
Proof.
unfold kw_argv1.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge. pose proof rz_range.
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
assert (Hv : cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1
= edenot E0 (e_str1 RZ)).
{ apply bv_eq.
pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum.
assert (TF : forall l : list (list byte), (0 < length l)%nat ->
Z.of_nat (total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1)
by (intros [|x t] Hl; [cbn in Hl; lia|]; change (firstn 1 (x :: t)) with [x]; cbn -[Z.of_nat Z.add]; lia).
pose proof (TF argv Hav0) as TF0.
pose proof u_e_str1 as U. unfold uE in U.
rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1 Hav1).
rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
rewrite inp_kernel. change (in_execfn inp) with execfn.
change (in_argv inp) with argv. change (in_envp inp) with envp.
rewrite U. unfold STR0, CHEAD, W, usp, L0, rseq, top, cat_string_off in *.
rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia. }
rewrite <- Hv. apply RW; [exact Hav1|]. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
+ apply Z.ltb_ge in Hc. assert (Hav1 : length argv = 1%nat) by (unfold argc in Hc; pose proof Hav0; lia).
pose proof (read_argv_null segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as RW.
rewrite inp_argv in RW. rewrite Hav1 in RW.
exact RW.
Qed.
Lemma atrandom_ok : kentry_ok segs E0 Mr0 (KBlob (SA (fst (e_atrb RZ)) (snd (e_atrb RZ))) (ELit 16) K_RND).
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge.
pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof lstr_lo. pose proof rz_range.
assert (Hab : split_lit (e_atrandom RZ) = (fst (e_atrb RZ), snd (e_atrb RZ))) by (unfold e_atrb; destruct (split_lit (e_atrandom RZ)); reflexivity).
set (ab := fst (e_atrb RZ)) in *. set (ak := snd (e_atrb RZ)) in *.
pose proof (split_u E0 (e_atrandom RZ) ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
(* WAS [ak = 488], the literal at [RZ = 1]: the auxv base is 24 and the vector 464 bytes.
   [split_lit] matches on the head of [e_atrandom RZ], which [unlin] leaves stuck while [RZ]
   is open, so this is one of the three places in the file that needs a literal flag. *)
assert (Hak : ak = 456 + 32 * RZ).
{ subst ak. destruct rseq_cases as [[_ Hrz] | [_ Hrz]]; rewrite Hrz; vm_compute; reflexivity. }
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
rewrite (YK06.firstn1_skipn_nth _ _ (Z_to_bv 8 0)) in Hrd by (rewrite length_at_random_bytes; lia).
assert (Ha : (at_random_ptr sp rseq argv envp + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + CHEAD - 16 + i)).
{ apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
rewrite Ha in Hrd.
rewrite Mr0_visible; [| rewrite u64_lit; unfold usp, TOP in *; lia | apply not_argH0; rewrite u64_lit; unfold STR0, usp in *; lia].
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
Lemma atrandom_zero_ok : kentry_ok segs E0 Mr0 (KZero (SA (fst (e_atrb RZ)) (snd (e_atrb RZ))) (ELit 16)).
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge.
pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof lstr_lo. pose proof rz_range.
assert (Hab : split_lit (e_atrandom RZ) = (fst (e_atrb RZ), snd (e_atrb RZ))) by (unfold e_atrb; destruct (split_lit (e_atrandom RZ)); reflexivity).
set (ab := fst (e_atrb RZ)) in *. set (ak := snd (e_atrb RZ)) in *.
pose proof (split_u E0 (e_atrandom RZ) ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
(* see [atrandom_ok]: 488 was this at [RZ = 1]. *)
assert (Hak : ak = 456 + 32 * RZ).
{ subst ak. destruct rseq_cases as [[_ Hrz] | [_ Hrz]]; rewrite Hrz; vm_compute; reflexivity. }
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
pose proof Hzr as Hz0. unfold YK06.zero_random_draw in Hz0.
rewrite Hz0, YK06.at_random_bytes_zero, repeat_firstn_skipn in Hrd by lia.
assert (Ha : (at_random_ptr sp rseq argv envp + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + CHEAD - 16 + i)).
{ apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
rewrite Ha in Hrd.
rewrite Mr0_visible; [| rewrite u64_lit; unfold usp, TOP in *; lia | apply not_argH0; rewrite u64_lit; unfold STR0, usp in *; lia].
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
unfold Mr0, Mr, mrestrict. destruct (hid A TOP argH0 E0 cs0 model0 (Z_to_bv 64 i)); [reflexivity|].
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
Lemma atr_ptr_eq : at_random_ptr sp rseq argv envp = edenot E0 (e_atrandom RZ).
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof chead_eq. pose proof gap_range. pose proof rz_range.
pose proof len_av. pose proof len_ev. pose proof bsb_ge.
destruct (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as [off (Hp & Hoff & _ & _)].
rewrite inp_argv, inp_envp, inp_rseq in Hp, Hoff.
apply bv_eq. rewrite Hp, word_add_nat, u64_lit by (unfold CHEAD, usp in *; lia).
pose proof u_e_atrandom as U. unfold uE in U. rewrite U. unfold CHEAD, usp. lia.
Qed.
(* A type word alone (the pairs whose value stays unknown).  Copied from bzip2's
   [K/AS/AsanInit.v] [auxt_ok] (its port to LPS 727298f3). *)
Lemma auxt_ok : forall i ty,
(0 <= i < Z.of_nat (auxv_count rseq)) ->
nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
kentry_ok segs E0 Mr0 (auxt i ty).
Proof.
intros i ty Hi H1. unfold auxt.
replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia.
apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
Qed.
(* The whole vector is readable ([KUnk]): it is visible block memory below argv[0].
   Copied from bzip2's [K/AS/AsanInit.v] [auxv_unk_ok] (its port to LPS 727298f3). *)
Lemma auxv_unk_ok : kentry_ok segs E0 Mr0 (KUnk (SA (fst e_auxb) (snd e_auxb)) (ELit (AUXSZ RZ))).
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum.
pose proof lstr_lo. pose proof bsb_ge. pose proof rz_range.
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
rewrite Mr0_visible; [| rewrite u64_lit; unfold usp, TOP in *; lia | apply not_argH0; rewrite u64_lit; unfold STR0, usp in *; lia].
unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw) by (rewrite u64_lit; unfold usp in *; lia). fold bsb.
unfold stack_to_mem. fold usp. rewrite u64_lit by (unfold usp in *; lia).
replace (usp <=? usp + 8 * argc + 8 * envc + 24 + i) with true by (symmetry; apply Z.leb_le; lia).
cbv zeta.
replace (usp + 8 * argc + 8 * envc + 24 + i - usp <? Z.of_nat (length bsb)) with true by (symmetry; apply Z.ltb_lt; lia).
intros Hn. apply nth_error_None in Hn. lia.
Qed.
(* [YK09.auxt_all]: the readable vector, the launch-fixed values of pairs 12, 16, 17, 18 (and
   of the CONFIG_RSEQ pair at [RZ = 1]), and the type words of the pairs whose value stays
   unknown.  Pairs 0..25 sit before the conditional CONFIG_RSEQ pair, so their [nth]
   reduces without the flag.  As bzip2's [K/AS/AsanInit.v] [init_kn_with_ok] and
   [auxv_rseq_ok] (its port to LPS 727298f3). *)
Ltac auxv_nth :=
unfold AUXW, auxv_words, auxv_entries; rewrite la_rseq_eq;
cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul].
Lemma auxt_all_ok : know_ok segs E0 Mr0 (auxt_all RZ A).
Proof.
pose proof auxv_count_rz. pose proof rz_range.
unfold auxt_all. apply Forall_cons; [exact auxv_unk_ok|].
do 4 (apply Forall_app; split;
[ apply auxw_ok;
[ cbv [AUXV_NULL_IX]; lia
| auxv_nth; reflexivity
| auxv_nth; first [ reflexivity | (rewrite edenot_lit; reflexivity)
| (rewrite edenot_lit, <- Hapc; reflexivity) ] ]
| ]).
apply Forall_app; split.
- destruct rseq_cases as [[Hrs Hrz] | [Hrs Hrz]]; rewrite Hrz; cbn [Z.eqb Pos.eqb]; [|apply Forall_nil].
apply Forall_app; split; apply auxw_ok;
[ cbv [AUXV_NULL_IX]; lia
| unfold AUXW, auxv_words, auxv_entries; rewrite la_rseq_eq, Hrs;
cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul]; reflexivity
| unfold AUXW, auxv_words, auxv_entries; rewrite la_rseq_eq, Hrs;
cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
first [ reflexivity | (rewrite edenot_lit; reflexivity) ]
| cbv [AUXV_NULL_IX]; lia
| unfold AUXW, auxv_words, auxv_entries; rewrite la_rseq_eq, Hrs;
cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul]; reflexivity
| unfold AUXW, auxv_words, auxv_entries; rewrite la_rseq_eq, Hrs;
cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
first [ reflexivity | (rewrite edenot_lit; reflexivity) ] ].
- apply Forall_forall. intros K HK. apply in_map_iff in HK as (p & <- & Hp).
unfold AUXT_UNCLAIMED in Hp.
repeat (destruct Hp as [<-|Hp]; [ apply auxt_ok; [ cbn [fst]; lia | auxv_nth; reflexivity ] |]).
destruct Hp.
Qed.
Lemma init_kn_with_ok : forall atr, kentry_ok segs E0 Mr0 atr -> know_ok segs E0 Mr0 (init_kn_with RZ atr A).
Proof.
intros atr Hatr.
pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
pose proof pad_range. pose proof gap_range. pose proof chead_eq. pose proof length_bsb_sum. pose proof lstr_lo. pose proof rz_range.
pose proof brk_range as [B1 B2]. pose proof bsb_ge. pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
pose proof (if_ph _ _ _ IMG) as (P1 & P2 & P3).
destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8).
assert (HL0 : 0 <= L0 <= 131071).
{ unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
(* auxv_count_rz: init_kn_with is parameterised on RZ, so its KRange bounds carry
   27 + 2*RZ through auxv_count.  This proof posed rz_range at :800 but not the
   count fact, which is what turns `auxv_count rseq` into arithmetic lia can use -
   the same gap auxv_word_ok had at :550, where :581/:582 already posed it.
   AT_RANDOM's own offset needs no re-keying here: u_e_atr8 (:381) is symbolic,
   `usp / 8 + argc + envc + G`, with no literal, so the 136 -> 392 re-derivation
   does not apply to this row. *)
pose proof auxv_count_rz.
unfold init_kn_with.
destruct stack_window_ok as [SW1 SW2].
apply Forall_app; split.
{ apply Forall_cons; [apply kr_ok; rewrite U1; lia|].
apply Forall_cons; [apply kr_ok; rewrite U2; lia|].
apply Forall_cons; [apply kr_ok; unfold eaddz, uE; rewrite mkAlu_denot, edenot_lit, u_add64, u64_lit by lia;
pose proof u_e_atrandom as U; unfold uE in U; rewrite U; rewrite Z.mod_small by lia; lia|].
(* The bound does NOT come from u_e_atr8's expression - it has no RZ in it, which
   is what made me report twice that this line "had not moved".  It comes from
   usp's HEADROOM: usp_fit gives usp + length bsb <= 2^47 and bsb_ge gives
   length bsb >= 8*argc + 8*envc + 482 + 32*RZ, so
     usp / 8 + argc + envc + G  <=  2^44 - (482 + 32*RZ)/8 + G
   and the KRange in YK09 is now (0xFFFFFFFFFC5 - 4*r) to match.  lia needs all
   seven facts to run that derivation; it had none of them.  Donor: cgif_rgb_fuzzer
   YA02.v:788-790 in its own port, which hit this exact line first. *)
apply Forall_cons; [apply kr_ok; rewrite u_e_atr8;
pose proof usp_lo; pose proof usp_fit; pose proof bsb_ge; pose proof rz_range;
pose proof len_av; pose proof len_ev; pose proof gap_range; lia|].
apply Forall_cons; [apply kr_ok; rewrite u_e_sp0; lia|].
apply Forall_cons; [apply kr_ok; rewrite u_sp8; lia|].
apply Forall_cons; [apply kr_ok; rewrite U3; lia|].
apply Forall_cons; [apply kr_ok; rewrite U4; lia|].
apply Forall_cons; [apply kr_ok; rewrite U5; lia|].
apply Forall_cons; [apply kr_ok; rewrite uE0_L1; pose proof L1_range; lia|].
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
(* THE ONE GENUINE CASE SPLIT IN THE LADDER, and it is the ninth row only.
   [StackLayout.auxv_entries] is 26 unconditional pairs, then the two CONFIG_RSEQ pairs when
   the flag is on, then AT_NULL (75d69e00:theories/LinuxProcessSem/StackLayout.v:229-262).
   The eight rows claimed below carry indices 13, 14, 15, 11, 19, 20, 23 and 24 -- every one
   below 26 -- so their [nth] reduces through the common prefix without resolving the [if] at
   all, and they would need no split.  AT_NULL does: its index is [AUXV_NULL_IX RZ = 26 + 2*RZ]
   and it sits ABOVE the conditional pairs, so both the index and the list it indexes into
   depend on the flag.  [nth] is not additive in its index the way [auxv_size] is additive in
   [block_head_size], which is why the arithmetic above needed no split and this does.
   The goal that decided it, at the ninth row with the flag free:
     nth (Z.to_nat (2 * AUXV_NULL_IX RZ))
         (auxv_words la ph entryw uid gid hw (at_random_ptr sp rseq argv envp)
                     (at_execfn_ptr top execfn)) (Z_to_bv 64 0)
     = Z_to_bv 64 0
   -- [cbn] stops at [if la_rseq la then ... else ...] with nothing to decide.
   [rewrite la_rseq_true] WAS what made it concrete; [la_rseq_eq] plus the branch's own
   [Hrs] is the same step over a free flag. *)
destruct rseq_cases as [[Hrs Hrz] | [Hrs Hrz]].
- repeat (apply Forall_app; split).
1-9: apply auxw_ok;
[ pose proof rz_range; cbv [AUXV_NULL_IX]; lia
| unfold AUXW, auxv_words, auxv_entries; rewrite la_rseq_eq, Hrs; rewrite ?Hrz;
cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul AUXV_NULL_IX];
try reflexivity .. ].
all: try (rewrite edenot_lit; reflexivity).
1: rewrite edenot_lit, P1; reflexivity.
1: rewrite edenot_lit, P2; reflexivity.
1: rewrite edenot_lit, P3; reflexivity.
(* 75d69e00: the ninth row's AT_RANDOM value slot is now the SEVENTH ARGUMENT of
   [auxv_words] (75d69e00:theories/LinuxProcessSem/StackLayout.v:229-262 feeds it through),
   so the [rewrite Hrs] on line 869 -- which this branch needs to decide the AT_NULL index --
   also rewrites [rseq] INSIDE that argument, leaving the slot at the literal [true]/[1].
   [atr_ptr_eq] is still stated over the free [rseq]/[RZ]; carry the branch's own equations
   into it rather than un-rewriting the goal. *)
(* 11c-HOIST: [Q] is posed INSIDE the branch ON PURPOSE -- this placement is load-bearing.
   Line 869 rewrites only the GOAL, never [in *], so there is no lemma-vs-goal flag skew to
   hoist around; each branch needs [atr_ptr_eq] carrying ITS OWN literal.  The rewrites are
   written WITHOUT [?] so a missing occurrence fails here with "Found no subterm matching"
   rather than silently at the [exact].  Both occurrences are measured, not assumed: the
   round printed [atr_ptr_eq]'s type as
   [at_random_ptr sp rseq argv envp = edenot E0 (e_atrandom RZ)], so [rseq] and [RZ] are
   present syntactically.  [exact] closes the rest up to conversion. *)
1: pose proof atr_ptr_eq as Q; rewrite Hrs, Hrz in Q; exact Q.
apply Forall_cons; [exact Hatr|].
apply Forall_cons; [exact kimg_ok|].
apply Forall_cons; [exact rw_window_ok|].
apply Forall_nil.
exact auxt_all_ok.
- repeat (apply Forall_app; split).
1-9: apply auxw_ok;
[ pose proof rz_range; cbv [AUXV_NULL_IX]; lia
| unfold AUXW, auxv_words, auxv_entries; rewrite la_rseq_eq, Hrs; rewrite ?Hrz;
cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul AUXV_NULL_IX];
try reflexivity .. ].
all: try (rewrite edenot_lit; reflexivity).
1: rewrite edenot_lit, P1; reflexivity.
1: rewrite edenot_lit, P2; reflexivity.
1: rewrite edenot_lit, P3; reflexivity.
1: pose proof atr_ptr_eq as Q; rewrite Hrs, Hrz in Q; exact Q.
apply Forall_cons; [exact Hatr|].
apply Forall_cons; [exact kimg_ok|].
apply Forall_cons; [exact rw_window_ok|].
apply Forall_nil.
exact auxt_all_ok.
Qed.
Lemma init_kn_ok : know_ok segs E0 Mr0 (init_kn RZ A).
Proof. exact (init_kn_with_ok _ atrandom_ok). Qed.
Lemma init_kn_zero_ok : know_ok segs E0 Mr0 (init_kn_zero RZ A).
Proof. exact (init_kn_with_ok _ atrandom_zero_ok). Qed.
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
(pagedown CEIL, pageup (CEIL + (2 ^ 47 - CEIL)));
(pagedown (shadow_off A + CEIL / 8), pageup (shadow_off A + (CEIL + (2 ^ 47 - CEIL)) / 8))].
Proof.
pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
unfold allowA, cs0, init_acs_of, init_acs_of_with, init_vis. cbn [a_vis a_ghost app flat_map allow1 fst snd].
unfold sh_lo, sh_hi. cbn [fst snd].
unfold uE. rewrite !edenot_lit, !u64_lit by (unfold CEIL; lia). reflexivity.
Qed.
Lemma abytes_init : A_bytes (allowA A E0 cs0) <= vis_cost (img_hi A - img_lo A) + vis_cost (2 ^ 47 - CEIL)
/\ vis_cost (img_hi A - img_lo A) + vis_cost (2 ^ 47 - CEIL) <= LIMIT.
Proof.
pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof (if_shadow _ _ _ IMG) as S1.
rewrite allowA_init. cbn [A_bytes fst snd]. unfold vis_cost, CEIL, LIMIT, target_alloc_limit.
replace (img_lo A + (img_hi A - img_lo A)) with (img_hi A) by lia.
assert (P1 : forall z, z mod 4096 = 0 -> pagedown z = z) by (intros z Hz; unfold pagedown; lia).
assert (P2 : forall z, z mod 4096 = 0 -> pageup z = z) by (intros z Hz; unfold pageup; lia).
rewrite (P1 (img_lo A) I3), (P2 (img_hi A) I4).
rewrite (P1 0x7fff7f800000 eq_refl). rewrite (P2 (0x7fff7f800000 + (2 ^ 47 - 0x7fff7f800000)) eq_refl).
pose proof (pageup_minus_pagedown (shadow_off A + img_lo A / 8) (shadow_off A + img_hi A / 8) ltac:(lia)).
pose proof (pageup_minus_pagedown (shadow_off A + 0x7fff7f800000 / 8) (shadow_off A + (0x7fff7f800000 + (2 ^ 47 - 0x7fff7f800000)) / 8) ltac:(lia)).
split; lia.
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
Theorem init_cs_ok : cs_ok segs A LIMIT TOP SINV0 argH0 (fs_seed_tmp fs tmp) E0 cs0 R0 FULL0 model0.
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
- split; [|split].
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
by (symmetry; exact (vdso_top_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp)).
apply incl_appr, incl_refl.
- reflexivity.
- unfold TOP.
change (alloc_top (m_vmmaps model0))
with (alloc_top (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp LIMIT inp))).
rewrite alloc_top_init. unfold stack_max_size. lia.
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
- rewrite app_nil_r, sum_sizes_app, (if_sizes _ _ _ IMG), resx_sum.
pose proof resx_bytes_lo. lia.
- constructor.
- unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
destruct uE0 as (_ & _ & _ & _ & _ & _ & U7 & _). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
rewrite Z.mod_small by lia. lia.
- lia.
- lia.
- exact AB1.
- constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
- intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
- split; [intros; reflexivity | split; [intros; reflexivity | reflexivity]].
- exact model0_channel_reader.
Qed.
Lemma hw_facts_ok : know_ok segs E0 Mr0 (KRange (EVar V_HW) 0x112D 0x20112D :: auxw 10 16 (EVar V_HW)).
Proof.
assert (Ehw : edenot E0 (EVar V_HW) = hw) by reflexivity.
apply Forall_cons.
- apply kr_ok. unfold uE. rewrite Ehw. destruct Hhw as [H | H]; rewrite H; unfold hwcap_rv64gc, hwcap_rv64gcv; rewrite u64_lit by lia; lia.
- apply auxw_ok;
[ pose proof rz_range; cbv [AUXV_NULL_IX]; lia
| unfold AUXW, auxv_words, auxv_entries; rewrite la_rseq_eq;
cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
try reflexivity .. ].
all: rewrite ?edenot_lit; try reflexivity.
Qed.
(* AT_GID and AT_EGID (pairs 21, 22) are both [gid], the launch variable [V_GID]. *)
Lemma gid_facts_ok : know_ok segs E0 Mr0 (auxw 21 13 (EVar V_GID) ++ auxw 22 14 (EVar V_GID)).
Proof.
pose proof rz_range.
apply Forall_app; split; (apply auxw_ok;
[ cbv [AUXV_NULL_IX]; lia
| unfold AUXW, auxv_words, auxv_entries; rewrite la_rseq_eq;
cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
try reflexivity .. ]).
all: rewrite ?edenot_lit; try reflexivity.
Qed.
Lemma init_kn_g_ok : know_ok segs E0 Mr0 (init_kn_g RZ A).
Proof.
unfold init_kn_g.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof gap_range. pose proof bsb_ge. pose proof rz_range.
apply Forall_cons; [apply kr_ok; rewrite u_e_atr8; lia|].
apply Forall_app. split; [exact init_kn_ok|].
apply Forall_app. split; [exact hw_facts_ok | exact gid_facts_ok].
Qed.
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
- split; [|split].
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
by (symmetry; exact (vdso_top_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp)).
apply incl_appr, incl_refl.
- reflexivity.
- unfold TOP.
change (alloc_top (m_vmmaps model0))
with (alloc_top (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp LIMIT inp))).
rewrite alloc_top_init. unfold stack_max_size. lia.
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
- rewrite app_nil_r, sum_sizes_app, (if_sizes _ _ _ IMG), resx_sum.
pose proof resx_bytes_lo. lia.
- constructor.
- unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
destruct uE0 as (_ & _ & _ & _ & _ & _ & U7 & _). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
rewrite Z.mod_small by lia. lia.
- lia.
- lia.
- exact AB1.
- constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
- intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
- split; [intros; reflexivity | split; [intros; reflexivity | reflexivity]].
- exact model0_channel_reader.
Qed.
Theorem init_cs_ok_zero : cs_ok segs A LIMIT TOP SINV0 argH0 (fs_seed_tmp fs tmp) E0 cs0z R0 FULL0 model0.
Proof.
destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
destruct abytes_init as [AB1 AB2].
change (allowA A E0 cs0) with (allowA A E0 (init_acs_of_zero RZ A)) in AB1.
constructor; unfold cs0z; cbn [init_acs_of_zero init_acs_of_with a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
- exact init_regs_ok.
- reflexivity.
- exact init_kn_zero_ok.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- split; [|split].
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
by (symmetry; exact (vdso_top_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp)).
apply incl_appr, incl_refl.
- reflexivity.
- unfold TOP.
change (alloc_top (m_vmmaps model0))
with (alloc_top (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp LIMIT inp))).
rewrite alloc_top_init. unfold stack_max_size. lia.
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
- rewrite app_nil_r, sum_sizes_app, (if_sizes _ _ _ IMG), resx_sum.
pose proof resx_bytes_lo. lia.
- constructor.
- unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
destruct uE0 as (_ & _ & _ & _ & _ & _ & U7 & _). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
rewrite Z.mod_small by lia. lia.
- lia.
- lia.
- exact AB1.
- constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
- intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
- split; [intros; reflexivity | split; [intros; reflexivity | reflexivity]].
- exact model0_channel_reader.
Qed.
Theorem init_cfg_eq :
init_config segs apc ph sp brk0 mbase rdraw LIMIT inp = cfg_of segs R0 (a_entry A) FULL0 model0.
Proof.
unfold init_config, cfg_of, FULL0, entryw. rewrite init_mkst, Hapc. reflexivity.
Qed.
End c.
