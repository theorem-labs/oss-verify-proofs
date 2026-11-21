(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up section is over the run's ProcInput, with valid_launch, the launch premise entry_launch_ok_va and valid_input's recorded-kernel conjunct in place of a record built from separate fields, entry_stack_fits and the zero-random-draw, nofile and sigmask premises; the run's CONFIG_RSEQ flag is a parameter, so the auxv has 27 or 29 pairs, AT_NULL's pair index follows it and AT_HWCAP is pair 10; the new stack geometry, with the strings at the entry draw's top, a pad and a parity gap below them and AT_RANDOM at the end of the head; wrap_mem over the run, the mmap base and the entry word; the initial model carries the vDSO, whose vvar and text ranges are reserved in the ledger after the image's, with if_resx, co_res and co_vdso; the zeroed stack below sp reaching down to the model's stack_window_lo; the launch's gid as the value of V_GID, and the initial knowledge's auxv claims proved, auxt_ok, auxv_unk_ok, auxt_all_ok and gid_facts_ok; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); valid_input's channel-reader conjunct as the section hypothesis Hrdr, from which model0_channel_reader proves cs_ok's new co_rdr field for the initial model). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1d YK1a YK15 YK00 YK19 YK12 YK04 YK05 YK06 YK09 YK0h.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0d YK0f YK0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YA0c YA0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK07.
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
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 mbase : word.
(* 08b1429 (recipes/procinput-fields.md step 3): the section is over the run's input [inp];
   its fields keep their old names as local notations. *)
Variable inp : ProcInput.
Local Notation argv := (in_argv inp).
Local Notation envp := (in_envp inp).
Local Notation uid := (in_uid inp).
Local Notation gid := (in_gid inp).
Local Notation hw := (in_hwcap inp).
Local Notation execfn := (in_execfn inp).
Hypothesis IMG : img_facts segs A ph.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk segs brk0.
Hypothesis Hmb : valid_mmap_base mbase.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Huid : valid_id uid.
Hypothesis Hhw : valid_hwcap hw.
Hypothesis Hlaunch : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
(* #38, rules 12f and 12r: the KERNEL PIN IS GONE.  [Hypothesis Hkernel :
   in_kernel inp = default_kernel] fixed ALL THIRTEEN fields of the kernel
   record and was discharged silently into every statement in this file; it was
   approved "until the model retarget", and #38 IS that retarget.  It is DELETED
   by name, together with [inp_kernel], [rseq_true] and [la_rseq_true], so that
   every stale consumer fails at compile time rather than quietly keeping the
   pin.

   What replaces it is STRICTLY WEAKER and is not a tree-added pin at all:
   [Hrec] is LITERALLY the last conjunct of the model's own [Run.valid_input]
   (75d69e00:theories/LinuxProcessSem/Run.v:4583-4595, [in_kernel inp =
   recorded_kernel (in_kernel inp)]) - the same proposition, not a
   strengthening of it - so anything it constrains is already constrained by
   the published statement, and it is discharged at the top where [valid_input
   inp] already sits (YD0b.v:87,:121).

   [recorded_kernel] (Run.v:4575-4581) pins [kb_vdso], [kb_vlenb], [kb_cache],
   [kb_skb_head] and the four socket-buffer sysctls to the default build and
   LEAVES [kb_thp], [kb_aslr], [kb_guard], [kb_rnd_bits] and - the one that
   matters here - [kb_rseq] FREE.  That is why the two vDSO facts this file
   needs ([vdso_len], [vdso_text_pages], used by [resx_eq]) still follow, by
   the model's own route (Run.v:5710-5712 [valid_input_vdso_text_pages] derives
   the page count from exactly this conjunct, because [vdso_image_of] reads
   only [kb_vdso]: State.v:3784-3786), while the auxv layout does not and is
   carried by [RZ] instead. *)
Hypothesis Hrec : in_kernel inp = recorded_kernel (in_kernel inp).
(* LPS 727298f3: [cs_ok]'s new last field [co_rdr] needs the initial model's
   channel-reader flag.  [init_model] copies it from the input
   ([State.in_channel_reader]), and [Hrdr] is LITERALLY a conjunct of the model's own
   [Run.valid_input] (727298f3:theories/LinuxProcessSem/Run.v:4967
   [valid_input_channel_reader]), so it is discharged at the top where [valid_input inp]
   already sits, as [Hrec] is: nothing here narrows the published statement. *)
Hypothesis Hrdr : in_channel_reader inp = true.
Let rseq : bool := kb_rseq (in_kernel inp).
(* the run's CONFIG_RSEQ flag as the plan's 0 or 1; nothing fixes its value *)
Let RZ : Z := rseq_z rseq.
Let entryw : word := Z_to_bv 64 (a_entry A).
Let la : LaunchAuxv := launch_auxv inp sp mbase.
Let top : word := ed_top rdraw.
Lemma inp_rseq : kb_rseq (in_kernel inp) = rseq. Proof. reflexivity. Qed.
Lemma la_rseq_eq : la_rseq la = rseq.       Proof. reflexivity. Qed.
Lemma RZ_range : 0 <= RZ <= 1.              Proof. exact (rseq_z_range rseq). Qed.
(* the bridge the deleted [rseq_true] used to short-circuit: the model's own
   auxv size, at this run's flag, is the plan's [AUXSZ RZ] - for EITHER build *)
Lemma auxv_size_RZ : Z.of_nat (StackLayout.auxv_size rseq) = AUXSZ RZ.
Proof. symmetry. exact (AUXSZ_of rseq). Qed.
Lemma auxv_count_RZ : Z.of_nat (StackLayout.auxv_count rseq) = 27 + 2 * RZ.
Proof. unfold RZ, rseq_z, rseq. destruct (kb_rseq (in_kernel inp)); vm_compute; reflexivity. Qed.
(* the two vDSO facts [resx_eq] needs, from [Hrec] alone - no kernel pin *)
Lemma vdso_text_pages_eq : vdso_text_pages (in_kernel inp) = vdso_text_pages default_kernel.
Proof.
rewrite (f_equal vdso_text_pages Hrec).
unfold vdso_text_pages, vdso_image_of. cbn [recorded_kernel kb_vdso]. reflexivity.
Qed.
Lemma vdso_len_eq : vdso_len (in_kernel inp) = 24576.
Proof. unfold vdso_len. rewrite vdso_text_pages_eq. vm_compute. reflexivity. Qed.
Lemma vdso_text_bytes_eq : (vdso_text_pages (in_kernel inp) * page_size)%Z = 8192.
Proof. rewrite vdso_text_pages_eq. vm_compute. reflexivity. Qed.
Let bsb := entry_stack_image inp mbase ph entryw sp rdraw.
Let usp := bv_unsigned sp.
(* The tree keeps its sp-relative bound: the stack VMA reaches 8 MiB below sp. *)
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
intros E a H. unfold argH0 in H. destruct Hsp as [Hlo _]. unfold sp_window_lo in Hlo. unfold TOP.
pose proof (valid_argv_len argv Hva).
assert (HC : 0 <= CHEAD) by (unfold CHEAD; lia).
assert (HW : 0 <= W) by (unfold W; lia).
apply orb_prop in H as [H|H]; apply andb_prop in H as [H _]; apply Z.leb_le in H;
unfold usp, argc, envc, STR0 in H; lia.
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
(* #38: the head's auxv term is [auxv_size rseq], 432 or 464, so the literal 504
   (which was 464 + 40) becomes 472 + 32 * RZ.  Rule 12a - the old literal is
   reproduced at RZ = 1: 472 + 32 = 504. *)
Lemma chead_eq : CHEAD = 8 * argc + 8 * envc + 472 + 32 * RZ + 8 * G.
Proof.
(* [lia]'s zify treats [Z.of_nat (auxv_size rseq)] as an atom, and [HA] is the
   equation that names it - the same shape as the deleted [replace ... with
   464%nat], with the pin taken out of it. *)
pose proof auxv_size_RZ as HA. unfold AUXSZ in HA.
unfold CHEAD, G, argc, envc, block_head_size, block_items.
lia.
Qed.
Lemma chead_range : 480 <= CHEAD <= 10752.
Proof.
pose proof chead_eq. pose proof len_av. pose proof len_ev. pose proof gap_range.
pose proof RZ_range. lia.
Qed.
Lemma lstr_lo : 2 <= LSTR.
Proof.
unfold LSTR, launch_string_bytes.
pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
pose proof (Nat2Z.is_nonneg (length execfn)).
pose proof Hav0 as Hnz. revert Hnz.
destruct (in_argv inp) as [|a t]; intros Hnz; [cbn in Hnz; lia|].
cbn [flatten_strings flat_map]. rewrite !length_app. cbn [length]. lia.
Qed.
Lemma s0_in_strings : L0 + 1 <= LSTR.
Proof.
unfold LSTR, launch_string_bytes, L0.
pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
pose proof (Nat2Z.is_nonneg (length execfn)).
pose proof Hav0 as Hnz. revert Hnz.
destruct (in_argv inp) as [|a t]; intros Hnz; [cbn in Hnz; lia|].
cbn [flatten_strings flat_map nth]. rewrite !length_app. cbn [length]. lia.
Qed.
Lemma lstr_hi : LSTR + 8 * argc + 8 * envc <= 2097152.
Proof.
destruct Hlaunch as [_ Hb]. unfold launch_bytes, e2big_limit in Hb.
unfold LSTR, argc, envc. lia.
Qed.
Lemma pad_bounds_Z : 0 <= utop - 8 - LSTR - usp - CHEAD <= 4110.
Proof.
destruct Hlau as (_ & Hsw & _). destruct Hsw as (_ & Hslo & Hshi).
unfold launch_sp_lo, launch_sp_hi, align_down16 in Hslo, Hshi.
fold rseq in Hslo, Hshi.
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
(* Model PropExec.v (08b1429); the tree's PropExec copy (YK11) is trimmed of it. *)
Lemma entry_page_top_within_window :
  forall v inp' mbase' (sp' brk : word) draw,
  entry_launch_ok_va v (mkEntry sp' brk mbase' draw) inp' ->
  (entry_page_top draw <= va_stack_top v)%Z.
Proof.
  intros v inp' mbase' sp' brk draw Hok.
  cbn [entry_launch_ok_va] in Hok.
  destruct Hok as ((_ & Htop & _) & _ & _).
  unfold entry_page_top. exact Htop.
Qed.
Lemma usp_fit : usp + Z.of_nat (length bsb) <= 2 ^ 47.
Proof.
rewrite length_bsb_eq. unfold stack_image_size. fold utop usp.
pose proof (entry_page_top_within_window Sv48 inp mbase sp brk0 rdraw Hlau) as H.
unfold entry_page_top, va_stack_top, sp_window_hi in H. fold top utop in H. lia.
Qed.
(* #38: the literal 514 assumed the rseq-ON head (CHEAD's constant 504); at
   RZ = 0 the head is 32 bytes smaller, so the bound is 482 + 32 * RZ.  Rule
   12a: at RZ = 1 that is 514, the old literal exactly, so nothing downstream
   loses strength on the build this file used to be pinned to. *)
Lemma bsb_ge : 8 * argc + 8 * envc + 482 + 32 * RZ <= Z.of_nat (length bsb).
Proof.
pose proof length_bsb_sum. pose proof chead_eq. pose proof lstr_lo. pose proof pad_range.
pose proof gap_range. pose proof RZ_range. lia.
Qed.
Lemma str0_hi : STR0 + LSTR + 8 = utop.
Proof. unfold STR0. pose proof pad_eq. lia. Qed.
Lemma brk_range : img_hi A <= bv_unsigned brk0 <= img_hi A + BRK_ASLR /\ bv_unsigned brk0 mod 4096 = 0.
Proof.
destruct Hbrk as (H1 & H2 & H3). unfold brk_aslr_max in H2. unfold page_size in H3.
rewrite (if_top _ _ _ IMG) in H1, H2. unfold BRK_ASLR. lia.
Qed.
Lemma usp_hi : usp + 192 <= 2 ^ 47.
(* #38: [bsb_ge]'s bound is now [482 + 32 * RZ], so every consumer needs
   [0 <= RZ] for lia to see it is at least 482. *)
Proof. pose proof usp_fit. pose proof bsb_ge. pose proof RZ_range. pose proof len_av. pose proof len_ev. lia. Qed.
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
destruct uE0 as (_ & _ & _ & _ & _ & U6 & _).
pose proof u_e_atrandom as UA. unfold e_str0, eadd, eaddz, uE, STR0 in *.
rewrite !mkAlu_denot, !edenot_lit.
rewrite !u_add64, !u64_lit by lia. rewrite UA, U6. rewrite !Z.mod_small by lia. lia.
Qed.
Lemma u_e_str1 : uE E0 (e_str1 RZ) = STR0 + L0 + 1.
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
pose proof pad_range. pose proof chead_eq. pose proof gap_range. pose proof bsb_ge. pose proof RZ_range.
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
(* LPS 727298f3: [cs_ok]'s [co_rdr].  [init_model] takes the channel-reader flag
   from the launch input and [with_vdso] keeps [m_proc], so the initial model's flag
   is a computation on that input, not an assumption: it is [Hrdr], the conjunct of
   [Run.valid_input] the statements quantify over. *)
Lemma model0_channel_reader : m_channel_reader model0 = true.
Proof. exact Hrdr. Qed.
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
Lemma resx_eq : RESX = [(Z_to_bv 64 (VTOP - 24576), Z_to_bv 64 16384);
(Z_to_bv 64 (VTOP - 24576 + 16384), Z_to_bv 64 8192)].
Proof.
pose proof vtop_range as [[T1 T2] T3].
unfold RESX, vdso_reserved. cbv zeta.
replace (vdso_len (in_kernel inp)) with 24576 by (exact vdso_len_eq).
replace (vdso_vvar_pages * page_size)%Z with 16384 by (vm_compute; reflexivity).
replace (vdso_text_pages (in_kernel inp) * page_size)%Z with 8192 by (exact vdso_text_bytes_eq).
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
Lemma spb_eq : split_lit e_sp0 = (e_sp0, 0).
Proof. reflexivity. Qed.
Let AUXW := auxv_words la ph entryw uid gid hw
(at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn).
(* #38: the auxv is 54 or 58 WORDS ([2 * auxv_count], the unit this list is
   indexed in); the literal 58 was the rseq-on case.  This is exactly the side
   condition [YK12.read_auxv_word] takes, so it is now discharged by name. *)
Lemma auxv_word_ok : forall (j : nat) v,
(j < 2 * auxv_count rseq)%nat ->
nth j AUXW (Z_to_bv 64 0) = edenot E0 v ->
kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 v).
Proof.
intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum.
pose proof lstr_lo. pose proof bsb_ge. pose proof RZ_range.
(* #38: [Hj] is now [j < 2 * auxv_count rseq] (WORDS, 54 or 58) where it used
   to be the literal [j < 58], so every [lia] below needs the bridge that turns
   the symbolic count into arithmetic: count = 27 + 2 * RZ with 0 <= RZ <= 1. *)
pose proof auxv_count_RZ.
assert (Hj' : (j < 58)%nat) by lia.
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
pose proof (read_auxv_word segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi' j Hj) as RW.
exact RW.
Qed.
(* #38: AT_NULL's PAIR index is [AUXV_NULL_IX RZ] = 26 + 2 * RZ, so the claimed
   pair indices run to 26 or 28; the literal 28 was the rseq-on case. *)
Lemma auxw_ok : forall i ty v,
(0 <= i <= AUXV_NULL_IX RZ) ->
nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
nth (Z.to_nat (2 * i + 1)) AUXW (Z_to_bv 64 0) = edenot E0 v ->
know_ok segs E0 Mr0 (auxw i ty v).
Proof.
intros i ty v Hi H1 H2. unfold auxw.
(* the word bound [auxv_word_ok] takes is [2 * auxv_count rseq]; the pair bound
   here is [AUXV_NULL_IX RZ].  Pose the bridge so each [lia] below sees both in
   one arithmetic: count = 27 + 2 * RZ and NULL_IX = 26 + 2 * RZ. *)
pose proof auxv_count_RZ as HC. pose proof RZ_range as HR.
unfold AUXV_NULL_IX in Hi.
assert (HCn : (auxv_count rseq = Z.to_nat (27 + 2 * RZ))%nat) by lia.
clear HC.
constructor; [|constructor; [|constructor]].
- replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia. apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
- replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia. apply auxv_word_ok; [lia|]. exact H2.
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
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge. pose proof RZ_range.
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
Lemma cat_argv0_eq :
bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) = STR0.
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof RZ_range.
rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0 Hav0).
change (total_arg_bytes_nat (firstn 0 (in_argv inp))) with 0%nat.
rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
unfold STR0, CHEAD, W, usp, rseq, top, cat_string_off in *.
rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia.
Qed.
Lemma argv0_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 8) 8 (e_str0 RZ)).
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge. pose proof RZ_range.
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
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge. pose proof RZ_range.
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
pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof RZ_range.
assert (TF : forall l : list (list byte), (0 < length l)%nat ->
Z.of_nat (total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1)
by (intros [|x t] Hl; [cbn in Hl; lia|]; change (firstn 1 (x :: t)) with [x]; cbn -[Z.of_nat Z.add]; lia).
pose proof (TF argv Hav0) as TF0.
pose proof u_e_str1 as U. unfold uE in U.
rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1 Hav1).
rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
rewrite U. unfold STR0, CHEAD, W, usp, L0, rseq, top, cat_string_off in *.
rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia. }
rewrite <- Hv. apply RW; [exact Hav1|]. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
+ apply Z.ltb_ge in Hc. assert (Hav1 : length argv = 1%nat) by (unfold argc in Hc; pose proof Hav0; lia).
pose proof (read_argv_null segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as RW.
rewrite Hav1 in RW.
exact RW.
Qed.
Lemma atrandom_ok : kentry_ok segs E0 Mr0 (KBlob (SA (fst (e_atrb RZ)) (snd (e_atrb RZ))) (ELit 16) K_RND).
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge.
pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof lstr_lo.
pose proof RZ_range.
assert (Hab : split_lit (e_atrandom RZ) = (fst (e_atrb RZ), snd (e_atrb RZ))) by (unfold e_atrb; destruct (split_lit (e_atrandom RZ)); reflexivity).
set (ab := fst (e_atrb RZ)) in *. set (ak := snd (e_atrb RZ)) in *.
pose proof (split_u E0 (e_atrandom RZ) ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
(* #38: WAS the bare literal 488.  24 is argc's word plus the two NULL
   terminators; the rest is the auxv, which the revision made rseq-dependent.
   Rule 12a: at RZ = 1 this is 24 + 464 = 488, the old literal exactly. *)
assert (Hak : ak = 24 + AUXSZ RZ) by (subst ak; unfold RZ; exact (e_atrb_off rseq)).
unfold AUXSZ in Hak.
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
fold rseq in Hp, Hoff, Hrd.
assert (Hu : bv_unsigned (at_random_ptr sp rseq argv envp) = usp + CHEAD - 16).
{ rewrite Hp, word_add_nat, u64_lit by (unfold usp in *; lia). unfold CHEAD. lia. }
specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold bsb in Hrd.
rewrite (YK07.firstn1_skipn_nth _ _ (Z_to_bv 8 0)) in Hrd by (rewrite length_at_random_bytes; lia).
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
pose proof usp_lo. pose proof usp_fit. pose proof chead_eq. pose proof gap_range.
pose proof len_av. pose proof len_ev. pose proof bsb_ge. pose proof RZ_range.
destruct (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as [off (Hp & Hoff & _ & _)].
fold rseq in Hp, Hoff.
apply bv_eq. rewrite Hp, word_add_nat, u64_lit by (unfold CHEAD, usp in *; lia).
pose proof u_e_atrandom as U. unfold uE in U. rewrite U. unfold CHEAD, usp. lia.
Qed.
(* A type word alone (the pairs whose value stays unknown), as cgif/cgif_file_fuzzer's
   YA02.v [auxt_ok] (from bzip2's [K/AS/AsanInit.v]). *)
Lemma auxt_ok : forall i ty,
(0 <= i < Z.of_nat (auxv_count rseq)) ->
nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
kentry_ok segs E0 Mr0 (auxt i ty).
Proof.
intros i ty Hi H1. unfold auxt.
replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia.
apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
Qed.
(* The whole vector is readable ([KUnk]): it is visible block memory below argv[0]; as
   cgif/cgif_file_fuzzer's YA02.v [auxv_unk_ok] (from bzip2's [K/AS/AsanInit.v]). *)
Lemma auxv_unk_ok : kentry_ok segs E0 Mr0 (KUnk (SA (fst e_auxb) (snd e_auxb)) (ELit (AUXSZ RZ))).
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum.
pose proof lstr_lo. pose proof bsb_ge. pose proof RZ_range.
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
(* [YK0a.auxt_all]: the readable vector, the launch-fixed values of pairs 12, 16, 17, 18 (and
   of the CONFIG_RSEQ pair when the run's flag is on), and the type words of the pairs whose
   value stays unknown; as cgif/cgif_file_fuzzer's YA02.v [auxt_all_ok], with this file's
   [case_eq] on the run's flag in place of its [rseq_cases]. *)
Lemma auxt_all_ok : know_ok segs E0 Mr0 (auxt_all RZ A).
Proof.
pose proof auxv_count_RZ as HC. pose proof RZ_range as HR.
unfold auxt_all. apply Forall_cons; [exact auxv_unk_ok|].
repeat (apply Forall_app; split).
1-4: apply auxw_ok;
[ unfold AUXV_NULL_IX; lia
| unfold AUXW, auxv_words, auxv_entries, la; cbn [la_rseq launch_auxv];
case_eq (kb_rseq (in_kernel inp)); intros Hkbr;
cbn [rseq_z flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
try reflexivity .. ].
all: try (rewrite edenot_lit; reflexivity).
- unfold RZ, rseq. case_eq (kb_rseq (in_kernel inp)); intros Hkbr; cbn [rseq_z Z.eqb Pos.eqb]; [|apply Forall_nil].
apply Forall_app; split; apply auxw_ok;
try (unfold AUXV_NULL_IX, RZ, rseq; rewrite Hkbr; cbn [rseq_z]; lia);
unfold AUXW, auxv_words, auxv_entries, la; cbn [la_rseq launch_auxv]; rewrite Hkbr;
cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
first [ reflexivity | (rewrite edenot_lit; reflexivity) ].
- apply Forall_forall. intros K HK. apply in_map_iff in HK as (p & <- & Hp).
unfold AUXT_UNCLAIMED in Hp.
repeat (destruct Hp as [<-|Hp];
[ apply auxt_ok;
[ cbn [fst]; lia
| unfold AUXW, auxv_words, auxv_entries, la; cbn [la_rseq launch_auxv];
case_eq (kb_rseq (in_kernel inp)); intros Hkbr;
cbn [fst snd rseq_z flat_map app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
reflexivity ] |]).
destruct Hp.
Qed.
Lemma init_kn_with_ok : forall atr, kentry_ok segs E0 Mr0 atr -> know_ok segs E0 Mr0 (init_kn_with RZ atr A).
Proof.
intros atr Hatr.
pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
pose proof pad_range. pose proof gap_range. pose proof chead_eq. pose proof length_bsb_sum. pose proof lstr_lo.
pose proof brk_range as [B1 B2]. pose proof bsb_ge. pose proof RZ_range. pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
pose proof (if_ph _ _ _ IMG) as (P1 & P2 & P3).
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
(* #38, CORRECTED.  I wrote here that the bound "had not moved" because
   [u_e_atr8 = usp / 8 + argc + envc + G] has no [RZ] in it.  That was wrong,
   and a build of this unit said so: it named this line,
   "No applicable tactic", which is the [lia] failing.

   THE BOUND DOES NOT COME FROM THAT EXPRESSION, IT COMES FROM [usp]'s
   HEADROOM.  [usp_fit] gives [usp + length bsb <= 2 ^ 47] and [bsb_ge] now
   gives [length bsb >= 8*argc + 8*envc + 482 + 32*RZ], so
     usp / 8 + argc + envc + G  <=  2^44 - (482 + 32*RZ)/8 + G
   which is exactly [0xFFFFFFFFFC1] at RZ = 1 and FOUR LARGER at RZ = 0, where
   the 432-byte auxv leaves four more words of room.  The pinned literal was
   the rseq-ON case, tight, and too small by 4 for a build without CONFIG_RSEQ.
   The [KRange] in YK0a is now [0xFFFFFFFFFC5 - 4 * r] and this [lia] is given
   the three facts that derivation needs. *)
apply Forall_cons; [apply kr_ok; rewrite u_e_atr8;
pose proof usp_lo; pose proof usp_fit; pose proof bsb_ge; pose proof RZ_range;
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
repeat (apply Forall_app; split).
(* #38, rule 12j: the pin's [rewrite la_rseq_true] is replaced by a CASE SPLIT on
   the run's own flag, placed UPSTREAM of the [cbn] that follows, so each branch
   reduces [auxv_entries] on a literal exactly as the rewrite used to.  Nothing
   fixes which branch is taken.  The ninth group is AT_NULL, whose pair index is
   [AUXV_NULL_IX RZ], so that constant joins the delta list. *)
1-9: apply auxw_ok;
[ unfold AUXV_NULL_IX; pose proof RZ_range; lia
(* #38, rule 11d - WRONG ORDER, named by a build of this unit at
   YA02.v:815, "Found no subterm matching la_rseq la".  The rewrite fired
   BEFORE the unfolds that expose [la_rseq la], which is buried inside [AUXW]
   until [auxv_entries] is unfolded.  Reduce the flag to the run's own field
   by COMPUTATION instead, exactly as YQ0a.v:880 does
   (`cbn [la_rseq launch_auxv la_cache ...]`), and only then split on it. *)
(* #38.  My previous fix here was WRONG ABOUT THE CAUSE and the farm said so by
   reporting the SAME error at the SAME tactic (`rseq is already used`, the next
   build of this unit, YA02.v:828 - which is :823 shifted by the
   comment I added).  Taking [rseq] out of the unfold list did not help,
   because the name is not introduced by the UNFOLD: this section has
   [Let rseq := kb_rseq (in_kernel inp)], so when [destruct] abstracts the goal
   over that very term it must generalise the let-binding too, and it tries to
   re-introduce it under the name [rseq], which already exists.
   [case_eq] does `generalize (eq_refl ...)` and `case`, which never
   re-introduces the binder - so the split happens with no name to collide, and
   the equation arrives as a goal premise named by the following [intros]. *)
| unfold AUXW, auxv_words, auxv_entries, AUXV_NULL_IX, RZ, la;
cbn [la_rseq launch_auxv];
case_eq (kb_rseq (in_kernel inp)); intros Hkbr;
cbn [rseq_z flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
try reflexivity .. ].
all: try (rewrite edenot_lit; reflexivity).
(* The [case_eq] on the run's flag above doubles every goal it reaches, so the
   three image facts and AT_RANDOM's pointer are each wanted once per flag
   value: close them by kind, not by position. *)
all: try (rewrite edenot_lit, P1; reflexivity).
all: try (rewrite edenot_lit, P2; reflexivity).
all: try (rewrite edenot_lit, P3; reflexivity).
all: try exact atr_ptr_eq.
(* The AT_NULL pair's index is [2 * (26 + 2 * rseq_z rseq)] with [rseq] the section's [Let]
   for the run's flag, which [case_eq] split on but did not unfold: unfold it, rewrite the
   flag's equation and compute. *)
all: try (unfold rseq; rewrite Hkbr; reflexivity).
apply Forall_cons; [exact Hatr|].
apply Forall_cons; [exact kimg_ok|].
apply Forall_cons; [exact rw_window_ok|].
apply Forall_nil.
exact auxt_all_ok.
Qed.
Lemma init_kn_ok : know_ok segs E0 Mr0 (init_kn RZ A).
Proof. exact (init_kn_with_ok _ atrandom_ok). Qed.
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
Lemma hw_facts_ok : know_ok segs E0 Mr0 (KRange (EVar V_HW) 0x112D 0x20112D :: auxw 10 16 (EVar V_HW)).
Proof.
assert (Ehw : edenot E0 (EVar V_HW) = hw) by reflexivity.
apply Forall_cons.
- apply kr_ok. unfold uE. rewrite Ehw. destruct Hhw as [H | H]; rewrite H; unfold hwcap_rv64gc, hwcap_rv64gcv; rewrite u64_lit by lia; lia.
- apply auxw_ok; [unfold AUXV_NULL_IX; pose proof RZ_range; lia | | rewrite Ehw];
(* #38, rule 12j, as in [init_kn_with_ok]: case split instead of the pin's
   [rewrite la_rseq_true], upstream of the reduction.  AT_HWCAP is pair 10,
   below index 26, so this row is the same in both branches. *)
unfold AUXW, auxv_words, auxv_entries, RZ, la;
cbn [la_rseq launch_auxv];
(* [case_eq], not [destruct], for the reason given at the first site: the
   section's [Let rseq] is the same term, and [destruct] would try to
   re-introduce that name. *)
case_eq (kb_rseq (in_kernel inp)); intros Hkbr;
cbn [rseq_z flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
reflexivity.
Qed.
(* AT_GID and AT_EGID (pairs 21, 22) are both [gid], the launch variable [V_GID]; below
   index 26, so the same in both branches of the run's flag. *)
Lemma gid_facts_ok : know_ok segs E0 Mr0 (auxw 21 13 (EVar V_GID) ++ auxw 22 14 (EVar V_GID)).
Proof.
assert (Egid : edenot E0 (EVar V_GID) = gid) by reflexivity.
apply Forall_app; split;
(apply auxw_ok; [unfold AUXV_NULL_IX; pose proof RZ_range; lia | | rewrite Egid];
unfold AUXW, auxv_words, auxv_entries, RZ, la;
cbn [la_rseq launch_auxv];
case_eq (kb_rseq (in_kernel inp)); intros Hkbr;
cbn [rseq_z flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
reflexivity).
Qed.
(* YA01.init_kn_g: AT_HWCAP is auxv pair 10, AT_GID/AT_EGID pairs 21 and 22. *)
Lemma init_kn_g_ok : know_ok segs E0 Mr0 (init_kn_g RZ A).
Proof.
unfold init_kn_g. apply Forall_app. split; [exact init_kn_ok|].
apply Forall_app. split; [exact hw_facts_ok | exact gid_facts_ok].
Qed.
Theorem init_cs_ok_g : cs_ok segs A LIMIT TOP SINV0 argH0 (in_fs inp) E0 (init_acs_of_g RZ A) R0 FULL0 model0.
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
- (* co_res: the reserved ledger is the image's plus the vDSO pages (State.init_reserved) *)
pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
pose proof (if_hull _ _ _ IMG) as (G1 & G2 & G3 & G4).
pose proof (if_resx _ _ _ IMG) as [RX1 RX2]. pose proof resx_bytes_lo.
exists RESX. split; [reflexivity|].
split; [| split; [pose proof resx_len; lia | rewrite resx_sum; lia]].
rewrite resx_eq. repeat constructor;
cbn [fst snd];
rewrite !u64_lit
by (unfold mmap_base_min, mmap_base_max, sp_window_hi in *; lia);
unfold KHI, mmap_base_min, mmap_base_max, sp_window_hi in *; lia.
- reflexivity.
- change (alloc_top (m_vmmaps model0)) with (bv_unsigned sp - stack_max_size). unfold TOP, stack_max_size. lia.
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
- constructor.
- (* co_vdso *)
replace (m_kernel model0) with (in_kernel inp) by reflexivity.
replace (vdso_top (m_vmmaps model0)) with VTOP
by (symmetry; exact (vdso_top_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp)).
apply incl_appr, incl_refl.
- exact model0_channel_reader.
Qed.
Theorem init_cfg_eq : forall apc : N, Z.of_N apc = a_entry A ->
init_config segs apc ph sp brk0 mbase rdraw LIMIT inp = cfg_of segs R0 (a_entry A) FULL0 model0.
Proof.
intros apc Hpc. unfold init_config, cfg_of, FULL0, entryw. rewrite init_mkst, Hpc. reflexivity.
Qed.
End c.
