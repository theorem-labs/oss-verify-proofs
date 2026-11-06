(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA02.v (donor image sha256 1c29845fe605), with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1d YK1a YK15 YK00 YK19 YK12 YK03 YK04 YK05 YK08 YK0g.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK0c YK0e YK0f.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YA0c YA0e.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK06.
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
if_shadow : 0 <= shadow_off A <= 2 ^ 47
}.
Definition stack_image_size (argv envp : list (list byte)) : Z :=
let struct_size := (8 + (Z.of_nat (length argv) + 1) * 8
+ (Z.of_nat (length envp) + 1) * 8 + 160)%Z in
let len := (struct_size + total_arg_bytes argv + total_arg_bytes envp)%Z in
(len + ((8 - len mod 8) mod 8) + 16)%Z.
Section c.
Variable segs : list Segment.
Variable A : atable.
Variable ph : PhdrInfo.
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
Hypothesis IMG : img_facts segs A ph.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk segs brk0.
Hypothesis Hmb : valid_mmap_base mbase.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Huid : valid_id uid.
Hypothesis Hhw : valid_hwcap hw.
Hypothesis Hzr : YK06.zero_random_draw (ed_random rdraw).
Definition inp : ProcInput := mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp.
Hypothesis Hnof : valid_nofile nofile.
Hypothesis Hsig : valid_sigmask inp.
Let bsb := build_stack_bytes ph sp argv envp uid hw rdraw.
Let SIMG := entry_stack_image ph sp argv envp uid hw rdraw.
Let usp := bv_unsigned sp.
Definition TOP : Z := bv_unsigned sp - 8388608.
Let argc := Z.of_nat (length argv).
Let envc := Z.of_nat (length envp).
Let L0 := Z.of_nat (length (nth 0 argv [])).
Let L1 := Z.of_nat (length (nth 1 argv [])).
Let W := (Z.of_nat (length bsb) - 16 - (8 * argc + 8 * envc + 184)) / 8.
Definition vals0 : list word :=
[Z_to_bv 64 (usp / 32768); Z_to_bv 64 argc; Z_to_bv 64 envc; Z_to_bv 64 L0; Z_to_bv 64 W;
Z_to_bv 64 (bv_unsigned brk0 / 4096); Z_to_bv 64 ((usp mod 32768) / 16); Z_to_bv 64 L1; uid;
hw].
Definition E0 : env := Env (fun n => nth n vals0 (Z_to_bv 64 0))
(fun k => if Nat.eqb k K_RND then at_random_bytes (ed_random rdraw) else []).
Definition argH0 (E : env) (a : word) : bool :=
let z := bv_unsigned a in
(((usp + 8 * argc + 16 <=? z) && (z <? usp + 8 * argc + 8 * envc + 24))
|| ((usp + 8 * argc + 8 * envc + 184 <=? z) && (z <? usp + 8 * argc + 8 * envc + 184 + 8 * W)))%bool.
Definition SINV0 (E : env) (M : word -> option byte) : Prop :=
(forall n, (n < NX0G)%nat -> ev E n = ev E0 n)
/\ (forall a, argH0 E a = true -> M a = wrap_mem ph sp argv envp uid hw rdraw a)
/\ eb E = eb E0.
Lemma argH0_high : forall E a, argH0 E a = true -> TOP <= bv_unsigned a.
Proof.
intros E a H. unfold argH0 in H. destruct Hsp as [Hlo _]. unfold sp_window_lo in Hlo. unfold TOP.
pose proof (valid_argv_len argv Hva).
apply orb_prop in H as [H|H]; apply andb_prop in H as [H _]; apply Z.leb_le in H; unfold usp, argc, envc in H; lia.
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
Lemma length_bsb_eq : Z.of_nat (length bsb) = stack_image_size argv envp.
Proof.
unfold bsb, build_stack_bytes, stack_image_size. cbv zeta.
rewrite (string_addrs_pair argv). cbv beta iota.
rewrite (string_addrs_pair envp). cbv beta iota.
rewrite !length_app, length_at_random_bytes, repeat_length, !length_flat_map_le8,
!length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes,
!length_flatten_strings.
rewrite !total_arg_bytes_Z. unfold auxv_size.
rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul.
match goal with
| |- context [Z.to_nat ?pd] =>
assert (Hpd : (0 <= pd < 8)%Z) by (apply Z.mod_pos_bound; lia); rewrite (Z2Nat.id pd) by lia
end.
lia.
Qed.
Lemma usp_fit : usp + Z.of_nat (length bsb) <= 2 ^ 47.
Proof.
pose proof (build_stack_bytes_within_span ph sp argv envp uid hw rdraw) as B. fold bsb in B.
unfold entry_stack_fits, sp_window_hi in Hfit. unfold usp. lia.
Qed.
Lemma bsb_ge : 8 * argc + 8 * envc + 200 <= Z.of_nat (length bsb) /\ (Z.of_nat (length bsb) - 16 - (8 * argc + 8 * envc + 184)) mod 8 = 0.
Proof.
rewrite length_bsb_eq. unfold stack_image_size, argc, envc. cbv zeta.
pose proof (total_arg_bytes_Z argv). pose proof (total_arg_bytes_Z envp).
match goal with |- context [((8 - ?l mod 8) mod 8)%Z] => set (len := l) end.
assert (0 <= Z.of_nat (total_arg_bytes_nat argv)) by lia.
split; [lia|].
assert (Hpd : 0 <= (8 - len mod 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (Hm : (len + (8 - len mod 8) mod 8) mod 8 = 0).
{ rewrite <- Zplus_mod_idemp_l. rewrite Zplus_mod_idemp_r.
replace (len mod 8 + (8 - len mod 8)) with 8 by lia. reflexivity. }
replace (len + (8 - len mod 8) mod 8 + 16 - 16 - (8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184))
with (len + (8 - len mod 8) mod 8 - 8 * (Z.of_nat (length argv) + Z.of_nat (length envp) + 23)) by (unfold len; lia).
rewrite Zminus_mod, Hm, Z.mul_comm, Z_mod_mult. reflexivity.
Qed.
Lemma W_range : 0 <= W /\ 8 * W = Z.of_nat (length bsb) - 16 - (8 * argc + 8 * envc + 184) /\ W <= 280000.
Proof.
pose proof bsb_ge as [G M]. pose proof (bsb_bound ph sp argv envp uid hw rdraw Hva Hve) as B. fold bsb in B.
unfold W. pose proof len_av. pose proof len_ev.
lia.
Qed.
Lemma brk_range : img_hi A <= bv_unsigned brk0 <= img_hi A + BRK_ASLR /\ bv_unsigned brk0 mod 4096 = 0.
Proof.
destruct Hbrk as (H1 & H2 & H3). unfold brk_aslr_max in H2. unfold page_size in H3.
rewrite (if_top _ _ _ IMG) in H1, H2. unfold BRK_ASLR. lia.
Qed.
Lemma usp_hi : usp + 192 <= 2 ^ 47.
Proof. pose proof usp_fit. pose proof bsb_ge as [G _]. pose proof len_av. pose proof len_ev. lia. Qed.
Lemma uE0 :
uE E0 (EVar V_S1) = usp / 32768 /\ uE E0 (EVar V_S2) = (usp mod 32768) / 16
/\ uE E0 (EVar V_ARGC) = argc /\ uE E0 (EVar V_ENVC) = envc /\ uE E0 (EVar V_L0) = L0
/\ uE E0 (EVar V_W) = W /\ uE E0 (EVar V_BRK) = bv_unsigned brk0 / 4096.
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
pose proof (u64_range brk0) as [B1 B2].
assert (HL0 : 0 <= L0 <= 131071).
{ unfold L0. pose proof (valid_argv_str_len argv 0 Hva ltac:(destruct Hva as [Hl _]; lia)). lia. }
unfold uE. cbn [edenot E0 ev nth vals0 V_S1 V_S2 V_ARGC V_ENVC V_L0 V_W V_BRK].
rewrite !u64_lit by lia. repeat split; reflexivity.
Qed.
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
Lemma u_e_str0 : uE E0 e_str0 = usp + 8 * argc + 8 * envc + 184.
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev.
pose proof u_e_auxv as UA. unfold e_str0, eaddz, uE in *. rewrite mkAlu_denot, edenot_lit.
rewrite u_add64, u64_lit by lia. rewrite UA. rewrite Z.mod_small by lia. lia.
Qed.
Lemma u_e_str1 : uE E0 e_str1 = usp + 8 * argc + 8 * envc + 184 + L0 + 1.
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
destruct uE0 as (_ & _ & _ & _ & U5 & _).
assert (HL0 : 0 <= L0 <= 131071).
{ unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
pose proof u_e_str0 as US. unfold e_str1, eadd, eaddz, uE in *. rewrite !mkAlu_denot, !edenot_lit.
rewrite !u_add64, !u64_lit by lia. rewrite US, U5. rewrite !Z.mod_small by lia. lia.
Qed.
Lemma u_e_atrandom : uE E0 e_atrandom = usp + Z.of_nat (length bsb) - 16.
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
destruct uE0 as (_ & _ & _ & _ & _ & U6 & _).
pose proof u_e_str0 as US. unfold e_atrandom, eadd, escale, uE in *. rewrite mkAlu_denot, mkMd_denot, edenot_lit.
rewrite u_add64, u_mul64, u64_lit by lia. rewrite US, U6. rewrite !Z.mod_small by lia. lia.
Qed.
Lemma u_e_atr8 : uE E0 e_atr8 = usp / 8 + argc + envc + W.
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7). pose proof u_sp8 as U8.
unfold e_atr8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
rewrite !u_add64, !u_mul64, !u64_lit by lia.
rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit, !u_add64, !u_mul64, !u64_lit in U8 by lia.
rewrite U1, U2, U3, U4, U6 in *. rewrite !Z.mod_small by lia. rewrite !Z.mod_small in U8 by lia. lia.
Qed.
Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.
Definition FULL0 : word -> option byte := wrap_mem ph sp argv envp uid hw rdraw.
Definition model0 : Model := init_model (segments_reserved segs) brk0 mbase sp LIMIT inp.
Let cs0 := init_acs_of A.
Let cs0z := init_acs_of_zero A.
Let hid0 := hid A TOP argH0 E0 cs0 model0.
Let Mr0 := Mr A TOP argH0 E0 cs0 model0 FULL0.
Lemma model0_facts :
m_halted model0 = None /\ m_fds model0 = fds_std /\ m_tid model0 = None
/\ vm_reserved (m_vmmaps model0) = segments_reserved segs /\ vm_maps (m_vmmaps model0) = []
/\ vm_noaccess (m_vmmaps model0) = [] /\ m_vm_lazy model0 = [] /\ m_vm_materialized model0 = []
/\ vm_limit (m_vmmaps model0) = LIMIT /\ vm_brk (m_vmmaps model0) = brk0 /\ vm_start_brk (m_vmmaps model0) = brk0
/\ vm_mmap_base (m_vmmaps model0) = mbase /\ eager_used model0 = 0.
Proof. repeat split; reflexivity. Qed.
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
Lemma FULL0_below : forall a : word, usp - 8388608 <= bv_unsigned a < usp -> FULL0 a = Some (Z_to_bv 8 0).
Proof.
intros a Ha. unfold FULL0, wrap_mem.
assert (Hs : stack_to_mem sp SIMG a = None).
{ unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
fold SIMG. rewrite Hs. unfold stack_max_size, usp in *.
replace (Z.leb (bv_unsigned sp - 8 * 1024 * 1024) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma FULL0_low : forall a : word, bv_unsigned a < usp - 8388608 -> FULL0 a = None.
Proof.
intros a Ha. unfold FULL0, wrap_mem.
assert (Hs : stack_to_mem sp SIMG a = None).
{ unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
fold SIMG. rewrite Hs. unfold stack_max_size, usp in *.
replace (Z.leb (bv_unsigned sp - 8 * 1024 * 1024) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.
Lemma rdn_Mr0_stack : forall (a : word) n,
usp <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
(forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> argH0 E0 x = false) ->
rdn segs Mr0 a n = rdn segs (stack_to_mem sp SIMG) a n.
Proof.
intros a n Ha Hn Hvis. pose proof usp_lo. unfold SIMG.
rewrite <- (rdn_wrap_stack_above segs ph sp argv envp a n uid hw rdraw) by (unfold usp in *; lia).
apply rdn_ext; [exact Hn|]. intros x Hx. apply Mr0_visible; [unfold usp, TOP, CEIL in *; lia | apply Hvis; exact Hx].
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
\/ usp + 8 * argc + 8 * envc + 184 <= bv_unsigned a < usp + Z.of_nat (length bsb) - 16.
Proof.
intros a H. unfold argH0 in H. pose proof W_range as (W1 & W2 & W3).
apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; [left|right]; lia.
Qed.
Lemma not_argH0 : forall a : word,
(bv_unsigned a < usp + 8 * argc + 16 \/ (usp + 8 * argc + 8 * envc + 24 <= bv_unsigned a < usp + 8 * argc + 8 * envc + 184)
\/ usp + Z.of_nat (length bsb) - 16 <= bv_unsigned a) -> argH0 E0 a = false.
Proof.
intros a H. destruct (argH0 E0 a) eqn:Ha; [|reflexivity]. apply argH0_range in Ha.
pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _]. lia.
Qed.
Lemma kword_stack : forall b k v (w : word),
bv_unsigned (edenot E0 b) + k = bv_unsigned w ->
usp <= bv_unsigned w -> bv_unsigned w + 8 <= usp + Z.of_nat (length bsb) ->
(forall x : word, bv_unsigned w <= bv_unsigned x < bv_unsigned w + 8 -> argH0 E0 x = false) ->
rdn segs (stack_to_mem sp SIMG) w 8%nat = Some (word_le8 (edenot E0 v)) ->
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
Lemma auxv_word_ok : forall (j : nat) v,
(j < 20)%nat ->
nth j (auxv_words ph (at_random_ptr sp argv envp) uid hw) (Z_to_bv 64 0) = edenot E0 v ->
kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 v).
Proof.
intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
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
rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul in Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. lia.
- rewrite <- Hv.
pose proof (read_auxv_word segs ph sp rdraw argv envp uid hw Hva Hve Hhi' j Hj) as RW.
exact RW.
Qed.
Lemma auxw_ok : forall i ty v,
(0 <= i <= 9) ->
nth (Z.to_nat (2 * i)) (auxv_words ph (at_random_ptr sp argv envp) uid hw) (Z_to_bv 64 0) = Z_to_bv 64 ty ->
nth (Z.to_nat (2 * i + 1)) (auxv_words ph (at_random_ptr sp argv envp) uid hw) (Z_to_bv 64 0) = edenot E0 v ->
know_ok segs E0 Mr0 (auxw i ty v).
Proof.
intros i ty v Hi H1 H2. unfold auxw.
constructor; [|constructor; [|constructor]].
- replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia. apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
- replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia. apply auxv_word_ok; [lia|]. exact H2.
Qed.
Lemma kr_ok : forall e lo hi, lo <= uE E0 e <= hi -> kentry_ok segs E0 Mr0 (KRange e lo hi).
Proof. intros e lo hi H. cbn [kentry_ok]. unfold uE in H. exact H. Qed.
Lemma Mr0_below : forall a : word, usp - 8388608 <= bv_unsigned a < usp -> Mr0 a = Some (Z_to_bv 8 0).
Proof.
intros a Ha. pose proof usp_lo. pose proof len_av.
rewrite Mr0_visible; [apply FULL0_below; exact Ha | unfold TOP, CEIL; lia | apply not_argH0; lia].
Qed.
Lemma stack_window_ok :
kentry_ok segs E0 Mr0 (KWr (SA e_sp0 (-8388608)) (ELit 8388608))
/\ kentry_ok segs E0 Mr0 (KZero (SA e_sp0 (-8388608)) (ELit 8388608)).
Proof.
pose proof usp_lo. pose proof usp_hi.
assert (Hst : estart E0 (SA e_sp0 (-8388608)) = usp - 8388608).
{ unfold estart. cbn [a_base a_off]. pose proof u_e_sp0 as U. unfold uE in U. rewrite U. lia. }
assert (Hl : elenZ E0 (ELit 8388608) = 8388608) by (apply elenZ_lit; lia).
assert (Hfl : flat E0 (SA e_sp0 (-8388608)) (elenZ E0 (ELit 8388608))).
{ unfold flat. rewrite Hst, Hl. lia. }
split; cbn [kentry_ok]; (split; [exact Hfl|]); rewrite Hst, ?Hl.
- intros d m Hd Hdm. apply store_ok_of_all; rewrite u_small by lia; [lia|].
intros x Hx. unfold wview. rewrite (Mr0_below x) by lia. discriminate.
- intros i Hi. apply Mr0_below. rewrite u_small by lia. lia.
Qed.
Lemma argc_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 0) 8 (EVar V_ARGC)).
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
apply (kword_stack e_sp0 0 (EVar V_ARGC) sp).
- pose proof u_e_sp0 as U. unfold uE in U. rewrite U. unfold usp. lia.
- unfold usp. lia.
- unfold usp in *. lia.
- intros x Hx. apply not_argH0. unfold usp in *. lia.
- pose proof (read_argc ph segs sp argv envp uid hw rdraw) as RW.
assert (Hv : len_word argv = edenot E0 (EVar V_ARGC)).
{ apply bv_eq. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. rewrite U3. unfold argc. exact (u_argcN argv Hva). }
rewrite <- Hv. apply RW. fold bsb. pose proof usp_fit. unfold usp in *. lia.
Qed.
Lemma argv0_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 8) 8 e_str0).
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
apply (kword_stack e_sp0 8 e_str0 (sp + nat_to_word (8 + 8 * 0))%bv).
- pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
- rewrite word_add_nat, u64_lit; unfold usp in *; lia.
- rewrite word_add_nat, u64_lit; unfold usp in *; lia.
- intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
- pose proof (read_argv_ptr_k ph segs sp argv envp 0 uid hw rdraw Hav0) as RW.
assert (Hv : cat_argv_ptr sp argv envp 0 = edenot E0 e_str0).
{ apply bv_eq. rewrite (@u_cat_argv_ptr ph sp rdraw argv envp uid hw Hva Hve Hlo' Hhi' 0 Hav0).
pose proof u_e_str0 as U. unfold uE in U. rewrite U. unfold cat_struct_size, auxv_size. replace (total_arg_bytes_nat (firstn 0 argv)) with 0%nat by reflexivity.
unfold usp, argc, envc. lia. }
rewrite <- Hv. apply RW. fold bsb. unfold usp in *. lia.
Qed.
Lemma argv1_word_ok : kentry_ok segs E0 Mr0 (kw_argv1 e_argv1w).
Proof.
unfold kw_argv1.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
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
pose proof (read_argv_ptr_k ph segs sp argv envp 1 uid hw rdraw Hav1) as RW.
assert (Hv : cat_argv_ptr sp argv envp 1 = edenot E0 e_str1).
{ apply bv_eq. rewrite (@u_cat_argv_ptr ph sp rdraw argv envp uid hw Hva Hve Hlo' Hhi' 1 Hav1).
pose proof u_e_str1 as U. unfold uE in U. rewrite U. unfold cat_struct_size, auxv_size.
assert (TF : forall l : list (list byte), (0 < length l)%nat ->
Z.of_nat (total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1)
by (intros [|x t] Hl; [cbn in Hl; lia|]; change (firstn 1 (x :: t)) with [x]; cbn -[Z.of_nat Z.add]; lia).
rewrite Nat2Z.inj_add, (TF argv Hav0). unfold L0, usp, argc, envc. lia. }
rewrite <- Hv. apply RW. fold bsb. unfold usp in *. lia.
+ apply Z.ltb_ge in Hc. assert (Hav1 : length argv = 1%nat) by (unfold argc in Hc; pose proof Hav0; lia).
pose proof (read_argv_null segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as RW. rewrite Hav1 in RW.
exact RW.
Qed.
Lemma atrandom_ok : kentry_ok segs E0 Mr0 (KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND).
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
assert (Hab : split_lit e_atrandom = (fst e_atrb, snd e_atrb)) by (unfold e_atrb; destruct (split_lit e_atrandom); reflexivity).
set (ab := fst e_atrb) in *. set (ak := snd e_atrb) in *.
pose proof (split_u E0 e_atrandom ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
assert (Hak : ak = 184) by (subst ak; vm_compute; reflexivity).
specialize (Hs ltac:(lia) ltac:(lia)).
assert (Hst : estart E0 (SA ab ak) = usp + Z.of_nat (length bsb) - 16) by (unfold estart; cbn [a_base a_off]; lia).
assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
cbn [kentry_ok]. rewrite Hst, Hl.
assert (HE : eb E0 K_RND = at_random_bytes (ed_random rdraw)) by (unfold E0; cbn [eb]; rewrite Nat.eqb_refl; reflexivity).
rewrite HE.
split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
split; [rewrite length_at_random_bytes; reflexivity|].
intros i Hi.
destruct (at_random_off segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as [off (Hp & Hlen & Hmod & Hrd)].
fold bsb in Hlen.
assert (Hu : bv_unsigned (at_random_ptr sp argv envp) = usp + Z.of_nat off).
{ rewrite Hp, word_add_nat. apply u64_lit. unfold usp in *. lia. }
specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold bsb in Hrd. fold SIMG in Hrd.
rewrite (YK06.firstn1_skipn_nth _ _ (Z_to_bv 8 0)) in Hrd by (rewrite length_at_random_bytes; lia).
assert (Ha : (at_random_ptr sp argv envp + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + i)).
{ apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
rewrite Ha in Hrd.
rewrite Mr0_visible; [| rewrite u64_lit; unfold usp, TOP, CEIL in *; lia | apply not_argH0; rewrite u64_lit; unfold usp in *; lia].
unfold FULL0. rewrite (wrap_above_sp ph sp argv envp _ uid hw rdraw) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
cbn [rdn] in Hrd.
destruct (stack_to_mem sp SIMG (Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + i))) as [b|] eqn:Hstk.
- cbn in Hrd. injection Hrd as ->. reflexivity.
- exfalso. unfold stack_to_mem in Hstk. fold usp in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
replace (usp <=? usp + Z.of_nat (length bsb) - 16 + i) with true in Hstk by (symmetry; apply Z.leb_le; lia).
cbv zeta in Hstk.
assert (HL : (length bsb <= length SIMG)%nat) by (unfold SIMG, entry_stack_image; cbv zeta; rewrite length_app; fold bsb; lia).
replace (usp + Z.of_nat (length bsb) - 16 + i - usp <? Z.of_nat (length SIMG)) with true in Hstk by (symmetry; apply Z.ltb_lt; lia).
apply nth_error_None in Hstk. lia.
Qed.
Lemma atrandom_zero_ok : kentry_ok segs E0 Mr0 (KZero (SA (fst e_atrb) (snd e_atrb)) (ELit 16)).
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
assert (Hab : split_lit e_atrandom = (fst e_atrb, snd e_atrb)) by (unfold e_atrb; destruct (split_lit e_atrandom); reflexivity).
set (ab := fst e_atrb) in *. set (ak := snd e_atrb) in *.
pose proof (split_u E0 e_atrandom ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
assert (Hak : ak = 184) by (subst ak; vm_compute; reflexivity).
specialize (Hs ltac:(lia) ltac:(lia)).
assert (Hst : estart E0 (SA ab ak) = usp + Z.of_nat (length bsb) - 16) by (unfold estart; cbn [a_base a_off]; lia).
assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
cbn [kentry_ok]. rewrite Hst, Hl. split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
intros i Hi.
destruct (at_random_off segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as [off (Hp & Hlen & Hmod & Hrd)].
fold bsb in Hlen.
assert (Hu : bv_unsigned (at_random_ptr sp argv envp) = usp + Z.of_nat off).
{ rewrite Hp, word_add_nat. apply u64_lit. unfold usp in *. lia. }
specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold bsb in Hrd. fold SIMG in Hrd.
pose proof Hzr as Hz0. unfold YK06.zero_random_draw in Hz0.
rewrite Hz0, YK06.at_random_bytes_zero, repeat_firstn_skipn in Hrd by lia.
assert (Ha : (at_random_ptr sp argv envp + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + i)).
{ apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
rewrite Ha in Hrd.
rewrite Mr0_visible; [| rewrite u64_lit; unfold usp, TOP, CEIL in *; lia | apply not_argH0; rewrite u64_lit; unfold usp in *; lia].
unfold FULL0. rewrite (wrap_above_sp ph sp argv envp _ uid hw rdraw) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
cbn [rdn] in Hrd.
destruct (stack_to_mem sp SIMG (Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + i))) as [b|] eqn:Hstk.
- cbn in Hrd. injection Hrd as ->. reflexivity.
- exfalso. unfold stack_to_mem in Hstk. fold usp in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
replace (usp <=? usp + Z.of_nat (length bsb) - 16 + i) with true in Hstk by (symmetry; apply Z.leb_le; lia).
cbv zeta in Hstk.
assert (HL : (length bsb <= length SIMG)%nat) by (unfold SIMG, entry_stack_image; cbv zeta; rewrite length_app; fold bsb; lia).
replace (usp + Z.of_nat (length bsb) - 16 + i - usp <? Z.of_nat (length SIMG)) with true in Hstk by (symmetry; apply Z.ltb_lt; lia).
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
Lemma atr_ptr_eq : at_random_ptr sp argv envp = edenot E0 e_atrandom.
Proof.
pose proof usp_lo. pose proof usp_fit.
destruct (at_random_off segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as [off (Hp & Hlen & Hmod & _)]. fold bsb in Hlen.
apply bv_eq. rewrite Hp, word_add_nat, u64_lit by (unfold usp in *; lia).
pose proof u_e_atrandom as U. unfold uE in U. rewrite U. unfold usp. lia.
Qed.
Lemma init_kn_with_ok : forall atr, kentry_ok segs E0 Mr0 atr -> know_ok segs E0 Mr0 (init_kn_with atr A).
Proof.
intros atr Hatr.
pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
pose proof brk_range as [B1 B2]. pose proof bsb_ge as [G _]. pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
pose proof (if_ph _ _ _ IMG) as (P1 & P2 & P3).
destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7).
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
apply Forall_cons; [apply kr_ok; rewrite uE0_uid; unfold valid_id in Huid; pose proof (u64_range uid); lia|].
apply Forall_cons; [apply kr_ok; rewrite U6; lia|].
apply Forall_cons; [apply kr_ok; rewrite U7; unfold BRK_ASLR in *; lia|].
apply Forall_cons; [exact SW1|].
apply Forall_cons; [exact SW2|].
apply Forall_cons; [exact argc_word_ok|].
apply Forall_cons; [exact argv0_word_ok|].
apply Forall_cons; [exact argv1_word_ok|].
apply Forall_nil. }
repeat (apply Forall_app; split).
1-9: apply auxw_ok; [lia | rewrite auxv_words_eq; cbn [nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul]; try reflexivity ..].
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
Lemma init_kn_zero_ok : know_ok segs E0 Mr0 (init_kn_zero A).
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
Lemma allowA_init_g : allowA A E0 (init_acs_of_g A) =
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
Lemma abytes_init_g : A_bytes (allowA A E0 (init_acs_of_g A)) <= vis_cost (img_hi A - img_lo A) + vis_cost STACK_VIS
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
- reflexivity.
- reflexivity.
-   unfold model0, TOP. rewrite alloc_top_init. unfold stack_max_size. lia.
- reflexivity.
- constructor.
- apply seps_nil.
- unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
unfold model0. apply init_sp_ok_init_model. exact Hsp.
- constructor.
- constructor.
- intros z Hz. exact Hz.
- constructor.
- constructor.
- rewrite app_nil_r, (if_sizes _ _ _ IMG). lia.
- constructor.
- unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
destruct uE0 as (_ & _ & _ & _ & _ & _ & U7). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
rewrite Z.mod_small by lia. lia.
- lia.
- lia.
- exact AB1.
- constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
- intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
- split; [intros; reflexivity | split; [intros; reflexivity | reflexivity]].
Qed.
Lemma hw_facts_ok : know_ok segs E0 Mr0 (KRange (EVar V_HW) 0x112D 0x20112D :: auxw 3 16 (EVar V_HW)).
Proof.
assert (Ehw : edenot E0 (EVar V_HW) = hw) by reflexivity.
apply Forall_cons.
- apply kr_ok. unfold uE. rewrite Ehw. destruct Hhw as [H | H]; rewrite H; unfold hwcap_rv64gc, hwcap_rv64gcv; rewrite u64_lit by lia; lia.
- apply auxw_ok; [lia | rewrite auxv_words_eq; cbn [nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul]; try reflexivity ..].
all: rewrite ?edenot_lit; try reflexivity.
Qed.
Lemma init_kn_g_ok : know_ok segs E0 Mr0 (init_kn_g A).
Proof.
unfold init_kn_g.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3). pose proof bsb_ge as [G _].
apply Forall_cons; [apply kr_ok; rewrite u_e_atr8; clear - H H0 H1 H2 W1 W2 W3 G; lia|].
apply Forall_app. split; [exact init_kn_ok | exact hw_facts_ok].
Qed.
Theorem init_cs_ok_g : cs_ok segs A LIMIT TOP SINV0 argH0 (fs_seed_tmp fs tmp) E0 (init_acs_of_g A) R0 FULL0 model0.
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
- reflexivity.
- reflexivity.
-   unfold model0, TOP. rewrite alloc_top_init. unfold stack_max_size. lia.
- reflexivity.
- constructor.
- apply seps_nil.
- unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
unfold model0. apply init_sp_ok_init_model. exact Hsp.
- constructor.
- constructor.
- intros z Hz. exact Hz.
- constructor.
- constructor.
- rewrite app_nil_r, (if_sizes _ _ _ IMG). lia.
- constructor.
- unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
destruct uE0 as (_ & _ & _ & _ & _ & _ & U7). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
rewrite Z.mod_small by lia. lia.
- lia.
- lia.
- exact AB1.
- constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
- intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
- split; [intros; reflexivity | split; [intros; reflexivity | reflexivity]].
Qed.
Theorem init_cs_ok_zero : cs_ok segs A LIMIT TOP SINV0 argH0 (fs_seed_tmp fs tmp) E0 cs0z R0 FULL0 model0.
Proof.
destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
destruct abytes_init as [AB1 AB2].
change (allowA A E0 cs0) with (allowA A E0 (init_acs_of_zero A)) in AB1.
constructor; unfold cs0z; cbn [init_acs_of_zero init_acs_of_with a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
- exact init_regs_ok.
- reflexivity.
- exact init_kn_zero_ok.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
-   unfold model0, TOP. rewrite alloc_top_init. unfold stack_max_size. lia.
- reflexivity.
- constructor.
- apply seps_nil.
- unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
unfold model0. apply init_sp_ok_init_model. exact Hsp.
- constructor.
- constructor.
- intros z Hz. exact Hz.
- constructor.
- constructor.
- rewrite app_nil_r, (if_sizes _ _ _ IMG). lia.
- constructor.
- unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
destruct uE0 as (_ & _ & _ & _ & _ & _ & U7). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
rewrite Z.mod_small by lia. lia.
- lia.
- lia.
- exact AB1.
- constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
- intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
- split; [intros; reflexivity | split; [intros; reflexivity | reflexivity]].
Qed.
Theorem init_cfg_eq : forall apc : N, Z.of_N apc = a_entry A ->
init_config segs apc ph sp brk0 mbase rdraw LIMIT inp = cfg_of segs R0 (a_entry A) FULL0 model0.
Proof.
intros apc Hpc. unfold init_config, cfg_of. cbn [in_argv in_envp in_uid in_hwcap inp]. rewrite init_mkst. rewrite Hpc. reflexivity.
Qed.
End c.
