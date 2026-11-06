(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA0h.v (donor image sha256 7093581aab04), with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK15 YK18 YK00 YK04 YK05 YK0c YK0e YK0f YK09 YK0a.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YA01 YA0c YA0e YA0d YA0f YA02 YA04 YA07 YA08 YA03 YA0a YA0b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YA00.
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
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : forall SEGS A nx0 LIMIT TOP SINV argH FS0, ext2_stmt SEGS A nx0 LIMIT TOP XB0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.
Lemma x_stmt_XSniff_dead : forall SEGS A nx0 LIMIT TOP SINV argH FS0, x_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 XSniff.
Proof. intros ? ? ? ? ? ? ? ?. intros args cs cs' E R FULL model T _ _ H. cbn [node_x] in H. discriminate H. Qed.
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
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variable stdin : InputStream.
Variables uid gid hw : word.
Variable groups : list word.
Variable net : NetQueue.
Variables nofile sigmask : word.
Variable urnd : InputStream. Variable tmp : Fs.Fs.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk segs brk0.
Hypothesis Hmb : valid_mmap_base mbase.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Huid : valid_id uid.
Hypothesis Hhw : valid_hwcap hw.
#[local] Notation SINV := (SINV0 ph sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 ph sp rdraw argv envp uid hw).
#[local] Notation E0a := (E0 ph sp rdraw brk0 argv envp uid hw).
#[local] Notation LIM := YA02.LIMIT.
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation FSQ := (fs_seed_tmp fs tmp).
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
Hypothesis startup_cert :
check segs IT0 A NX0G LIM (XNG segs XN1) XE0 XB0 HS hole_le KC0 BFUEL FUEL None (init_acs_of_g A) startup_plan = COk startup_shape.
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0G E E' -> HOLES h E fs' = HOLES h E' fs'.
Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
Hypothesis HOLES_le : forall h' h E fs' tr, hole_le h' h = true -> HOLES h' E fs' tr -> HOLES h E fs' tr.
Hypothesis HOLES_sound : holes_stmt segs A LIM TOP HS SINV argH HOLES FSQ.
Let TOK : top_ok TOP := top_ok0 sp Hsp.
Let AH := argH0_high ph sp rdraw argv envp uid hw Hsp Hva.
Let AA := argH0_agree ph sp rdraw argv envp uid hw.
Let SF := SINV0_frame ph sp rdraw brk0 argv envp uid hw.
Let SA := SINV0_agree ph sp rdraw brk0 argv envp uid hw.
Let SP0 := SINV0_sp0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit.
Let SS1 := SINV0_s1 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit.
Lemma node_x_sound_all : forall x, x_stmt segs A NX0G LIM TOP SINV argH FSQ x.
Proof.
assert (SS0 : forall E M, SINV E M -> SINV E M) by (intros E M H; exact H).
intros x. destruct x.
- exact (node_x_sound_XIMemset segs A NX0G LIM TOP SEGS_wx SEGS_in_hull HULL_ok TOK SINV argH AH AA SF SA SS1 SHADOW_ok FSQ SUM_imemset).
- exact (node_x_sound_XIMemcpy segs A NX0G LIM TOP SEGS_wx SEGS_in_hull HULL_ok TOK SINV argH AH AA SF SA FSQ SEGS_wr SUM_imemcpy).
- exact (node_x_sound_XMemset segs A NX0G LIM TOP SEGS_wx SEGS_in_hull HULL_ok TOK SINV argH AH AA SF SA SS1 SHADOW_ok FSQ SUM_memset).
- exact (node_x_sound_XMemcpy segs A NX0G LIM TOP SEGS_wx SEGS_in_hull HULL_ok TOK SINV argH AH AA SF SA FSQ SEGS_wr SUM_memcpy).
- exact (node_x_sound_XMemIsZero segs A NX0G LIM TOP SEGS_wx SEGS_in_hull HULL_ok TOK SINV argH AH AA SF SA FSQ SUM_miz).
- exact (init_x_sound_envscan segs A ph SEGS_wx SEGS_in_hull HULL_ok we1 we2 we3 Xenv Fe1 Fe2 Fe3 Ee De1 De2 De3
sp rdraw brk0 argv envp FSQ Hsp Hva Hve uid hw Hfit SINV SS0 SF).
- exact (init_x_sound_pnscan segs A ph SEGS_wx SEGS_in_hull HULL_ok wp0 wp1 wp2 wp3 wp4 Xpn Fp0 Fp1 Fp2 Fp3 Fp4 Ep Dp0 Dp1 Dp2 Dp3 Dp4
sp rdraw brk0 argv envp FSQ Hsp Hva Hve uid hw Hfit SINV SS0 SF SA).
- exact (init_x_sound_layout segs A ph sp rdraw argv envp FSQ uid hw SINV).
- exact (node_x_sound_XIStrncpy segs A NX0G LIM TOP SEGS_wx SEGS_in_hull HULL_ok TOK SINV argH AH AA SF SA FSQ SUM_istrncpy).
- exact (node_x_sound_XPopFree segs A NX0G LIM TOP SEGS_wx SEGS_in_hull HULL_ok TOK SINV argH AH AA SF SA FSQ SUM_popfree).
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
srealizes segs (cfg_of segs (R0 sp) (a_entry A) (FULL0 ph sp rdraw argv envp uid hw)
(model0 segs sp brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp))
(sd HOLES t_nil E0a FSQ startup_shape).
Proof.
pose proof (init_cs_ok_g segs A ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp IMG Hsp Hbrk Hva Hve Hfit Huid Hhw) as HC.
assert (NSYS : forall y, sys_stmt segs A NX0G LIM TOP SINV argH FSQ y) by (eapply node_sys_sound; eauto).
assert (NBRK : brk2_stmt segs A NX0G LIM TOP SINV argH FSQ) by (eapply node_brk2_sound; eauto).
assert (NMM2 : mm2_stmt segs A NX0G LIM TOP SINV argH FSQ (node_mmap2g A NX0G LIM)) by (eapply node_mmap2g_sound_OBL; eauto).
assert (NMIN : forall hole, mm3_stmt segs A NX0G LIM TOP SINV argH FSQ (node_mmapin_g A LIM hole)) by (eapply node_mmapin_g_sound_OBL; eauto).
assert (NMIN2 : mm2_stmt segs A NX0G LIM TOP SINV argH FSQ (node_mmapin2_g A LIM)) by (eapply node_mmapin2_g_sound_OBL; eauto).
assert (NMPR : mm2_stmt segs A NX0G LIM TOP SINV argH FSQ (node_mprotect2g A LIM)) by (eapply node_mprotect2g_sound_OBL; eauto).
assert (NEXIT : exit_stmt segs A LIM TOP SINV argH FSQ) by (eapply node_exit_sound; eauto).
assert (NJOIN : join_stmt segs A NX0G LIM TOP SINV argH FSQ) by (eapply node_join_sound; eauto).
pose proof (check_sound segs IT0 IT0_ok A NX0G LIM TOP HS (XNG segs XN1) XE0 XB0
SEGS_wx SEGS_in_hull TOK HULL_ok SHADOW_ok SINV argH AH AA SF SA
HOLES HOLES_agree HOLES_nil hole_le HOLES_le FSQ KC0
NSYS NBRK NMM2 NMIN NMIN2 NMPR NEXIT node_x_sound_all NJOIN XNG_sound
(XE0_sound _ _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _ _) HOLES_sound
FUEL BFUEL None startup_plan (init_acs_of_g A) startup_shape startup_cert
E0a (R0 sp) (FULL0 ph sp rdraw argv envp uid hw)
(model0 segs sp brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp) t_nil HC) as R.
exact (R I eq_refl).
Qed.
Theorem asan_startup_init : forall apc : N, Z.of_N apc = a_entry A ->
srealizes segs (init_config segs apc ph sp brk0 mbase rdraw YA02.LIMIT
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp))
(sd HOLES t_nil E0a FSQ startup_shape).
Proof.
intros apc Hpc.
rewrite (init_cfg_eq segs A ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp apc Hpc).
exact asan_startup_gen.
Qed.
End c.
End b.
