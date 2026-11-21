(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the asan start-up section stated over the run's ProcInput in place of its separate argv, envp, fs, uid, hwcap and other fields, with the launch premises valid_launch and entry_launch_ok_va in place of entry_stack_fits and the recorded-kernel premise on the run's kernel; SINV0, argH0, E0, FULL0 and model0 over the input and the mmap base; the run's CONFIG_RSEQ flag passed to x_stmt, check, init_acs_of_g and check_sound; the start-up munmap node node_munmap2, which may refuse or cut, discharged; and SINV0_sp0's projection named for node_brk2_sound; valid_input's channel-reader conjunct Hrdr, which init_cs_ok_g takes for cs_ok's new co_rdr field). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK15 YK18 YK00 YK05 YK06 YK0d YK0f YK0g YK0a YK0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YA01 YA0c YA0e YA0d YA0f YA02 YA04 YA07 YA08 YA03 YA0a YA0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YA00.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG. Import APSXG.
Open Scope Z_scope.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.
Definition XN_SPLITVIS : nat := 64.
Definition XNG (segs : list Segment) (XN1 : nat -> list expr -> acs -> option acs) (id : nat) (args : list expr) (cs : acs) : option acs :=
if Nat.eqb id XN_SPLITVIS then xn_splitvis YA02.LIMIT args cs else
match id with O => xn_havoccell NX0G segs args cs | S i => XN1 i args cs end.
Definition is_sum_x (x : xnode) : bool :=
match x with
| XIMemset | XMemset | XIMemcpy | XMemcpy | XMemIsZero | XIStrncpy | XPopFree => true
| XEnvScan | XPnScan | XLayout | XSniff => false
end.
Section b. Context {fx : YK11.FPState}.
Lemma XE0_sound : forall SEGS A nx0 LIMIT TOP SINV argH FS0, emit_stmt SEGS A nx0 LIMIT TOP XE0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros bm id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : forall SEGS A nx0 LIMIT TOP SINV argH FS0, ext2_stmt SEGS A nx0 LIMIT TOP XB0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros bm id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.
(* #38: [x_stmt] gained [rz] (the run's CONFIG_RSEQ flag) after [TOP], because
   [node_x] reaches [e_str0]/[e_argv1w], which the revision made r-dependent.
   This lemma is about a node that cannot fire, so it quantifies over the flag
   and never inspects it - nothing here is pinned. *)
Lemma x_stmt_XSniff_dead : forall SEGS A nx0 LIMIT TOP rz SINV argH FS0, x_stmt SEGS A nx0 LIMIT TOP rz SINV argH FS0 XSniff.
Proof. intros ? ? ? ? ? ? ? ? ?. intros args bm cs cs' E R FULL model T _ _ H. cbn [node_x] in H. discriminate H. Qed.
Section c.
Variable segs : list Segment.
Variable A : atable.
Variable ph : PhdrInfo.
Hypothesis IMG : img_facts segs A ph.
Hypothesis SEGS_wx : wx_segs_nowrap segs.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok segs A.
Hypothesis HULL_ok : hull_ok A.
Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis RES_chk : res_cover_check segs A = true.
Hypothesis SEGS_wr : segs_wr_ok segs.
Let RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
(segments_reserved segs) := if_res _ _ _ IMG.
Let RES_cover : res_cover_ok segs A := res_cover_check_sound segs A RES_chk.
Variables we1 we2 we3 wp0 wp1 wp2 wp3 wp4 : bv 32.
Hypothesis Xenv : 0 <= x_envscan A /\ x_envscan A + 12 < 2 ^ 64 /\ x_envscan_k A = x_envscan A + 12.
Hypothesis Fe1 : fetch_word segs (Z_to_bv 64 (x_envscan A)) = Some we1.
Hypothesis Fe2 : fetch_word segs (Z_to_bv 64 (x_envscan A + 4)) = Some we2.
Hypothesis Fe3 : fetch_word segs (Z_to_bv 64 (x_envscan A + 8)) = Some we3.
Hypothesis Ee : is_ecall we1 = false /\ is_ecall we2 = false /\ is_ecall we3 = false.
Hypothesis De1 : decode_any we1 = Some (Load SZ8 true 10 9 0, 4%Z).
Hypothesis De2 : decode_any we2 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Hypothesis De3 : decode_any we3 = Some (Branch BC_NE 10 0 8184, 4%Z).
Hypothesis Xpn : 8 <= x_pnscan A /\ x_pnscan A + 12 < 2 ^ 64 /\ x_pnscan_k A = x_pnscan A + 12.
Hypothesis Fp0 : fetch_word segs (Z_to_bv 64 (x_pnscan A - 8)) = Some wp0.
Hypothesis Fp1 : fetch_word segs (Z_to_bv 64 (x_pnscan A - 4)) = Some wp1.
Hypothesis Fp2 : fetch_word segs (Z_to_bv 64 (x_pnscan A)) = Some wp2.
Hypothesis Fp3 : fetch_word segs (Z_to_bv 64 (x_pnscan A + 4)) = Some wp3.
Hypothesis Fp4 : fetch_word segs (Z_to_bv 64 (x_pnscan A + 8)) = Some wp4.
Hypothesis Ep : is_ecall wp0 = false /\ is_ecall wp1 = false /\ is_ecall wp2 = false /\ is_ecall wp3 = false /\ is_ecall wp4 = false.
Hypothesis Dp0 : decode_any wp0 = Some (Store SZ8 10 11 0, 4%Z).
Hypothesis Dp1 : decode_any wp1 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Hypothesis Dp2 : decode_any wp2 = Some (Load SZ1 false 13 11 4095, 4%Z).
Hypothesis Dp3 : decode_any wp3 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Hypothesis Dp4 : decode_any wp4 = Some (Branch BC_NE 13 0 8180, 4%Z).
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 mbase : word.
(* 08b1429: over the run's input [inp] (recipes/procinput-fields.md step 3), as YA02. *)
Variable inp : ProcInput.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk segs brk0.
Hypothesis Hmb : valid_mmap_base mbase.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Huid : valid_id (in_uid inp).
Hypothesis Hhw : valid_hwcap (in_hwcap inp).
Hypothesis Hlaunch : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
(* #38 (rules 12f, 12r): the kernel pin is replaced by [valid_input]'s own
   recorded-kernel conjunct (75d69e00:Run.v:4596), which fixes kb_vdso,
   kb_vlenb, kb_cache, kb_skb_head and the four socket-memory fields and
   leaves kb_thp, kb_aslr, kb_guard, kb_rnd_bits and kb_rseq FREE.  As YA02. *)
Hypothesis Hrec : in_kernel inp = recorded_kernel (in_kernel inp).
(* LPS 727298f3: [valid_input]'s channel-reader conjunct (Run.v:4967
   [valid_input_channel_reader]), which [YA02.init_cs_ok_g] takes for [cs_ok]'s new
   last field [co_rdr].  As YA02. *)
Hypothesis Hrdr : in_channel_reader inp = true.
#[local] Notation SINV := (SINV0 A ph sp rdraw brk0 mbase inp).
#[local] Notation argH := (argH0 sp rdraw inp).
#[local] Notation E0a := (E0 sp rdraw brk0 inp).
#[local] Notation LIM := YA02.LIMIT.
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation FSQ := (in_fs inp).
Hypothesis SUM_imemset : fill_spec segs (x_imemset A) 256.
Hypothesis SUM_memset : fill_spec segs (x_memset A) two64.
Hypothesis SUM_imemcpy : copy_spec segs (x_imemcpy A).
Hypothesis SUM_memcpy : copy_spec segs (x_memcpy A).
Hypothesis SUM_miz : miz_spec segs (x_memiszero A).
Hypothesis SUM_istrncpy : istrncpy_spec segs (x_istrncpy A) (x_sealed A).
Hypothesis SUM_popfree : popfree_spec segs (x_popfree A).
Variable XN1 : nat -> list expr -> acs -> option acs.
Hypothesis XN1_sound : forall i args, node1_stmt segs A NX0G LIM TOP SINV argH FSQ always (XN1 i args).
Variable IT0 : itab.
Hypothesis IT0_ok : itab_sound segs IT0.
Variable HS : nat -> option acs.
Variable hole_le : nat -> nat -> bool.
Variable startup_plan : plan.
Variable startup_shape : shape.
Variables KC0 BFUEL FUEL : nat.
(* #38: [init_acs_of_g] gained the run's CONFIG_RSEQ flag as its FIRST argument
   (YA01.v:719, via [init_kn_g] YA01.v:713), because the auxv table was
   retabled.  The flag is taken from the run - [kb_rseq (in_kernel inp)], as
   YA02.v:84-86 takes it - and nothing here pins it.
   #38 (rule 2g): [APG.check] (YA0c.v) also gained the same flag as a section
   [Variable rz : Z] declared after [LIMIT], so it is the sixth argument of the
   discharged [check], before [XN].  The same run-derived flag is passed. *)
Hypothesis startup_cert :
check segs IT0 A NX0G LIM (APC.rseq_z (kb_rseq (in_kernel inp))) (XNG segs XN1) XE0 XB0 HS hole_le KC0 BFUEL FUEL None
(init_acs_of_g (APC.rseq_z (kb_rseq (in_kernel inp))) A) startup_plan = COk startup_shape.
Hypothesis startup_live : lv startup_plan = true.
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0G E E' -> HOLES h E fs' = HOLES h E' fs'.
Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
Hypothesis HOLES_le : forall h' h E fs' tr, hole_le h' h = true -> HOLES h' E fs' tr -> HOLES h E fs' tr.
Hypothesis HOLES_sound : holes_stmt segs A LIM TOP HS SINV argH HOLES FSQ.
Let TOK : top_ok TOP := top_ok0 sp Hsp.
Let AH := argH0_high sp rdraw inp Hsp Hva.
Let AA := argH0_agree sp rdraw inp.
Let SF := SINV0_frame A ph sp rdraw brk0 mbase inp.
Let SA := SINV0_agree A ph sp rdraw brk0 mbase inp.
Lemma SS1 : forall E M, SINV E M ->
uE E e_sp0 = TOP + 8388608 /\ uE E (EVar V_S1) = (TOP + 8388608) / 32768 /\ (TOP + 8388608) mod 16 = 0.
Proof. intros E M H. eapply SINV0_s1; eassumption. Qed.
(* #38: [x_stmt] (YA0e.v:1644) gained [rz] after [TOP]; [node_x] reaches
   [e_str0]/[e_argv1w], which the revision made r-dependent. *)
Lemma node_x_sound_all : forall x, x_stmt segs A NX0G LIM TOP (APC.rseq_z (kb_rseq (in_kernel inp))) SINV argH FSQ x.
Proof.
assert (SS0 : forall E M, SINV E M -> SINV E M) by (intros E M H; exact H).
intros x. destruct x.
- exact (node_x_sound_XIMemset segs A NX0G LIM TOP SEGS_wx SEGS_in_hull HULL_ok TOK SINV argH AH AA SF SA SS1 SHADOW_ok FSQ (APC.rseq_z (kb_rseq (in_kernel inp))) SUM_imemset).
- exact (node_x_sound_XIMemcpy segs A NX0G LIM TOP SEGS_wx SEGS_in_hull HULL_ok TOK SINV argH AH AA SF SA FSQ (APC.rseq_z (kb_rseq (in_kernel inp))) SEGS_wr SUM_imemcpy).
- exact (node_x_sound_XMemset segs A NX0G LIM TOP SEGS_wx SEGS_in_hull HULL_ok TOK SINV argH AH AA SF SA SS1 SHADOW_ok FSQ (APC.rseq_z (kb_rseq (in_kernel inp))) SUM_memset).
- exact (node_x_sound_XMemcpy segs A NX0G LIM TOP SEGS_wx SEGS_in_hull HULL_ok TOK SINV argH AH AA SF SA FSQ (APC.rseq_z (kb_rseq (in_kernel inp))) SEGS_wr SUM_memcpy).
- exact (node_x_sound_XMemIsZero segs A NX0G LIM TOP SEGS_wx SEGS_in_hull HULL_ok TOK SINV argH AH AA SF SA FSQ (APC.rseq_z (kb_rseq (in_kernel inp))) SUM_miz).
- eapply init_x_sound_envscan; solve [eassumption | exact SF | exact SA | exact SS0].
- eapply init_x_sound_pnscan; solve [eassumption | exact SF | exact SA | exact SS0].
- eapply init_x_sound_layout.
- exact (node_x_sound_XIStrncpy segs A NX0G LIM TOP SEGS_wx SEGS_in_hull HULL_ok TOK SINV argH AH AA SF SA FSQ (APC.rseq_z (kb_rseq (in_kernel inp))) SUM_istrncpy).
- exact (node_x_sound_XPopFree segs A NX0G LIM TOP SEGS_wx SEGS_in_hull HULL_ok TOK SINV argH AH AA SF SA FSQ (APC.rseq_z (kb_rseq (in_kernel inp))) SUM_popfree).
- apply x_stmt_XSniff_dead.
Qed.
Lemma XNG_sound : ext_stmt segs A NX0G LIM TOP (XNG segs XN1) SINV argH FSQ.
Proof.
intros id args. unfold XNG. destruct (Nat.eqb id XN_SPLITVIS); [eapply xn_splitvis_sound; eauto|].
destruct id as [|i].
- eapply xn_havoccell_sound; eauto.
- apply XN1_sound.
Qed.
Theorem asan_startup_gen :
srealizes segs (cfg_of segs (R0 sp) (a_entry A) (FULL0 A ph sp rdraw mbase inp)
(model0 segs sp rdraw brk0 mbase inp))
(sd HOLES t_nil E0a FSQ startup_shape).
Proof.
assert (HC : cs_ok segs A LIM TOP SINV argH FSQ E0a (init_acs_of_g (APC.rseq_z (kb_rseq (in_kernel inp))) A) (R0 sp) (FULL0 A ph sp rdraw mbase inp)
(model0 segs sp rdraw brk0 mbase inp)) by (eapply init_cs_ok_g; eassumption).
assert (NSYS : forall y, sys_stmt segs A NX0G LIM TOP SINV argH FSQ y) by (eapply node_sys_sound; eauto).
(* #38, rule 25p - the first time this line has ever been REACHED, since every
   earlier round stopped above it.  [node_brk2_sound] is YA08.v:381, in Section
   j, and it USES [SINV_sp0] at YA08.v:462, so the discharged theorem takes
   `forall E M, SINV E M -> uE E e_sp0 = TOP + 8388608` as a premise.  This
   file has no hypothesis of that shape: [SS1] (:137) proves the CONJUNCTION
   that YA0e/YA0f want, and its FIRST conjunct is exactly that equation.
   [eauto] searches the local context and the core database; it cannot invent
   a [proj1] around a global lemma, so that one premise was left open and
   `assert ... by` reported `Proof is not complete.` over the whole of :173,
   characters 0-94.  The projection is named here, as [SS0] is at :144, so the
   [eauto]s below find it by [assumption].  Nothing new is assumed. *)
assert (SSP : forall E M, SINV E M -> uE E e_sp0 = TOP + 8388608)
by (intros E M H; exact (proj1 (SS1 E M H))).
assert (NBRK : brk2_stmt segs A NX0G LIM TOP SINV argH FSQ) by (eapply node_brk2_sound; eauto).
assert (NMM2 : mm2_stmt segs A NX0G LIM TOP SINV argH FSQ (node_mmap2g A NX0G LIM)) by (eapply node_mmap2g_sound_OBL; eauto).
assert (NMIN : forall hole, mm3_stmt segs A NX0G LIM TOP SINV argH FSQ (node_mmapin_g A LIM hole)) by (eapply node_mmapin_g_sound_OBL; eauto).
assert (NMIN2 : mm2_stmt segs A NX0G LIM TOP SINV argH FSQ (node_mmapin2_g A LIM)) by (eapply node_mmapin2_g_sound_OBL; eauto).
assert (NMPR : mm2_stmt segs A NX0G LIM TOP SINV argH FSQ (node_mprotect2g A LIM)) by (eapply node_mprotect2g_sound_OBL; eauto).
(* 08b1429: the start-up munmap is a PMunmap2 node (refused / cut). *)
assert (NMUN : mm2_stmt segs A NX0G LIM TOP SINV argH FSQ (node_munmap2 A)) by (eapply node_munmap2_sound; eauto).
assert (NEXIT : exit_stmt segs A LIM TOP SINV argH FSQ) by (eapply node_exit_sound; eauto).
assert (NJOIN : join_stmt segs A NX0G LIM TOP SINV argH FSQ) by (eapply node_join_sound; eauto).
(* #38: [check_sound]'s section (YA0e.v:48-88) declares [rz] after [TOP] and
   before [HS], so the flag is passed there - the same run-derived flag as in
   [startup_cert] and in [node_x_sound_all]. *)
pose proof (check_sound segs IT0 IT0_ok A NX0G LIM TOP (APC.rseq_z (kb_rseq (in_kernel inp))) HS (XNG segs XN1) XE0 XB0
SEGS_wx SEGS_in_hull TOK HULL_ok SHADOW_ok SINV argH AH AA SF SA
HOLES HOLES_agree HOLES_nil hole_le HOLES_le FSQ KC0
NSYS NBRK NMM2 NMIN NMIN2 NMPR NMUN NEXIT node_x_sound_all NJOIN XNG_sound
(XE0_sound _ _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _ _) HOLES_sound
FUEL BFUEL None startup_plan (init_acs_of_g (APC.rseq_z (kb_rseq (in_kernel inp))) A) startup_shape startup_cert
true E0a (R0 sp) (FULL0 A ph sp rdraw mbase inp)
(model0 segs sp rdraw brk0 mbase inp) t_nil HC) as R.
exact (R I eq_refl startup_live).
Qed.
Theorem asan_startup_init : forall apc : N, Z.of_N apc = a_entry A ->
srealizes segs (init_config segs apc ph sp brk0 mbase rdraw YA02.LIMIT inp)
(sd HOLES t_nil E0a FSQ startup_shape).
Proof.
intros apc Hpc.
rewrite (init_cfg_eq segs A ph sp rdraw brk0 mbase inp apc Hpc).
exact asan_startup_gen.
Qed.
End c.
End b.
