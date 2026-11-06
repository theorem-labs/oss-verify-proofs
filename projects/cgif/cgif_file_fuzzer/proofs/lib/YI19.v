(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open ReadWrite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s YK0p YK0r YP0n YP0o.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP0h YP01.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI06 YI16 YI00 YI14 YI07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma rdn_of_mbytes : forall segs mem bs a,
(forall j, (j < length bs)%nat -> mbyte segs mem (a + Z.of_nat j) = Some (nth j bs (Z_to_bv 8 0))) ->
rdn segs mem (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
intros segs mem bs. induction bs as [|b bs IH]; intros a H; [reflexivity|].
cbn [length rdn]. pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn [nth Z.of_nat] in H0. rewrite Z.add_0_r in H0.
unfold mbyte in H0. rewrite H0. rewrite Z_to_bv64_add1. rewrite (IH (a + 1)); [reflexivity|].
intros j Hj. specialize (H (S j) ltac:(cbn; lia)). cbn [nth] in H. rewrite <- H. f_equal. lia.
Qed.
Lemma read_cstr_of_garr8 : forall segs mem a l,
garr8 segs mem a (l ++ [0]) -> Forall (fun x => 0 < x < 256) l -> (length l <= 4095)%nat ->
read_cstr (mrb segs mem) (Z_to_bv 64 a) = CstrOk (map (fun z => Z_to_bv 8 z) l).
Proof.
intros segs mem a l HG Hnz Hlen.
apply read_cstr_of_rdn.
- rewrite length_map. exact Hlen.
- intros Hin. apply in_map_iff in Hin as (x & Hx & Hxin).
rewrite Forall_forall in Hnz. specialize (Hnz x Hxin).
apply (f_equal bv_unsigned) in Hx. rewrite !Z_to_bv_unsigned in Hx. unfold bv_wrap, bv_modulus in Hx.
change (2 ^ Z.of_N 8) with 256 in Hx. rewrite Z.mod_small in Hx by lia. rewrite Z.mod_small in Hx by lia. lia.
- rewrite length_map.
replace (map (fun z => Z_to_bv 8 z) l ++ [Z_to_bv 8 0]) with (map (fun z => Z_to_bv 8 z) (l ++ [0])) by (rewrite map_app; reflexivity).
replace (length l + 1)%nat with (length (map (fun z => Z_to_bv 8 z) (l ++ [0]))) by (rewrite length_map, length_app; reflexivity).
apply rdn_of_mbytes. intros j Hj. rewrite length_map in Hj.
rewrite (garr8_mbyte segs mem a (l ++ [0]) j HG Hj).
change (Z_to_bv 8 0) with ((fun z => Z_to_bv 8 z) 0). rewrite map_nth. reflexivity.
Qed.
Lemma errno_ret_unsigned : forall e, 1 <= e <= 4095 -> bv_unsigned (errno_ret e) = 2 ^ 64 - e.
Proof.
intros e He. unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
replace (- e) with (2 ^ 64 - e + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Definition unlink_tmp_errnos : list Z := EISDIR :: ENOENT :: unlinkat_errnos.
Lemma unlink_errnos_range : forall e, In e unlink_tmp_errnos -> 1 <= e <= 4095.
Proof. intros e He. cbv [unlink_tmp_errnos unlinkat_errnos In] in He. repeat (destruct He as [<-|He]; [vm_compute; split; discriminate|]). destruct He. Qed.
Lemma openat_errnos_range : forall e, In e openat_errnos -> 1 <= e <= 4095.
Proof. intros e He. cbv [openat_errnos In] in He. repeat (destruct He as [<-|He]; [vm_compute; split; discriminate|]). destruct He. Qed.
Lemma sink_path_eq : sink_path = sink_path_bytes.
Proof. reflexivity. Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Context {SH : sink_head} {SK : sink_syms}.
Local Notation segs := (ms_segs B).
Lemma stdio_env_path : forall regs pc mem,
stdio_env B mem ->
read_cstr (ms_read_byte (pend_at regs pc mem (seg_rom segs))) (Z_to_bv 64 sk_path_addr) = CstrOk sink_path.
Proof.
intros regs pc mem (_ & _ & Hp & _). rewrite pend_read_byte_mrb.
apply (read_cstr_of_garr8 segs mem sk_path_addr sink_path_Z Hp); [|cbn; lia].
unfold sink_path_Z. repeat (constructor; [lia|]). constructor.
Qed.
Definition unlink_outcome (mdc md' : Model) (RET : word) : Prop :=
m_fds md' = m_fds mdc /\
(((exists e, In e unlink_tmp_errnos /\ RET = errno_ret e) /\ m_fs md' = m_fs mdc) \/
(RET = Z_to_bv 64 0 /\ (m_fs md' = m_fs mdc \/ m_fs md' = fs_remove (m_fs mdc) sink_path))).
Lemma J_unlink_node : forall regs pc mem0 STK sp0 FP L A mem md Lc Ac mdc Q,
journal B MR STK sp0 FP L A mem md Lc Ac mem0 mdc ->
sink_open_fp FP ->
stdio_env B mem0 ->
fd_names_path (m_fds mdc) sink_path = false ->
bv_unsigned (getr regs 17) = 35 -> getr regs 10 = AT_FDCWD -> bv_unsigned (flag32 (getr regs 12)) = 0 ->
getr regs 11 = Z_to_bv 64 sk_path_addr ->
(forall RET md',
journal B MR STK sp0 FP L A mem md Lc Ac mem0 md' -> unlink_outcome mdc md' RET ->
SR segs (mkCfg (mkst (regupd regs 10 RET) (v_addi pc 4) mem0 (seg_rom segs)) md') Q) ->
SR segs (mkCfg (pend_at regs pc mem0 (seg_rom segs)) mdc) Q.
Proof.
intros regs pc mem0 STK sp0 FP L A mem md Lc Ac mdc Q HJ Hfp Henv Hfdn Hno Hdir Hfl Hpath HK.
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
destruct sink_path_facts as (F1 & F2 & F3 & _ & _ & _ & F7 & F8). rewrite <- sink_path_eq in F1, F2, F3, F7.
pose proof (stdio_env_path regs pc mem0 Henv) as Hcstr. rewrite <- Hpath in Hcstr.
destruct (fs_under (m_fs mdc) sink_path) eqn:Hun.
{
apply (SR_unlink_tmp_isdir segs regs pc mem0 (seg_rom segs) mdc sink_path sink_name_bytes Q Hh Hlz Hno Hdir Hfl Hcstr F1 F2 F3 F7 F8 Hun Hfdn).
apply HK; [exact HJ|]. split; [reflexivity|]. left. split; [|reflexivity]. exists EISDIR. split; [left; reflexivity | reflexivity]. }
destruct (fs_lookup (m_fs mdc) sink_path) as [d|] eqn:Hlk.
- apply (SR_unlink_tmp_present segs regs pc mem0 (seg_rom segs) mdc sink_path sink_name_bytes d Q Hh Hlz Hno Hdir Hfl Hcstr F1 F2 F3 F7 F8 Hun Hlk Hfdn).
+ intros e He. apply HK; [exact HJ|]. split; [reflexivity|]. left. split; [|reflexivity].
exists e. split; [right; right; exact He | reflexivity].
+ apply HK.
* rewrite with_fs_os_upd. apply (journal_os_upd B MR LAWS); [exact HJ | exact Hfp | apply fds_rel_refl | | apply fs_remove_sorted].
intros p Hp. apply fs_lookup_remove_other. exact Hp.
* split; [rewrite with_fs_os_upd; reflexivity|]. right. split; [reflexivity|]. right. rewrite with_fs_os_upd. reflexivity.
-
apply (SR_unlink_tmp_absent segs regs pc mem0 (seg_rom segs) mdc sink_path sink_name_bytes Q Hh Hlz Hno Hdir Hfl Hcstr F1 F2 F3 F7 F8 Hun Hlk Hfdn).
apply HK; [exact HJ|]. split; [reflexivity|]. left. split; [|reflexivity]. exists ENOENT. split; [right; left; reflexivity | reflexivity].
Qed.
Definition sink_os (md : Model) (fd : Z) (W : list Z) : Prop :=
fs_lookup (m_fs md) sink_path = Some (bytes W) /\
fd_lookup (m_fds md) (Z_to_bv 64 fd) = Some (FdFileW sink_path (Z_to_bv 64 (Z.of_nat (length W)))) /\
fd_names_path (fd_remove (m_fds md) (Z_to_bv 64 fd)) sink_path = false.
Lemma fd_remove_insert : forall fds (fd : word) e, fd_remove (fd_insert fds fd e) fd = fd_remove fds fd.
Proof.
intros fds fd e. unfold fd_remove, fd_insert. cbn [List.filter fst].
replace (bv_eqb fd fd) with true by (symmetry; apply bv_eqb_eq; reflexivity). cbn [negb].
induction fds as [|[k x] r IH]; [reflexivity|]. cbn [List.filter fst].
destruct (bv_eqb k fd) eqn:Ek; cbn [negb]; [exact IH|]. cbn [List.filter fst]. rewrite Ek. cbn [negb]. rewrite IH. reflexivity.
Qed.
Lemma rdn_of_garr8 : forall mem a X, garr8 segs mem a X ->
rdn segs mem (Z_to_bv 64 a) (length X) = Some (bytes X).
Proof.
intros mem a X HG. rewrite <- (bytes_length X) at 1. apply rdn_of_mbytes. intros j Hj. rewrite bytes_length in Hj.
rewrite (garr8_mbyte segs mem a X j HG Hj). unfold bytes.
change (Z_to_bv 8 0) with ((fun z => Z_to_bv 8 z) 0). rewrite map_nth. reflexivity.
Qed.
Lemma word_to_nat_len : forall n : nat, Z.of_nat n < 2 ^ 64 -> word_to_nat (Z_to_bv 64 (Z.of_nat n)) = n.
Proof.
intros n Hn. unfold word_to_nat. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite Z.mod_small by lia. apply Nat2Z.id.
Qed.
Lemma u64_small : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. exact Hz. Qed.
Lemma sink_os_written : forall STK sp0 FP L A mem md Lc Ac mem0 mdc fd W X,
journal B MR STK sp0 FP L A mem md Lc Ac mem0 mdc -> sink_open_fp FP ->
sink_os mdc fd W -> Z.of_nat (length W) + Z.of_nat (length X) < 2 ^ 64 ->
let md' := with_fds (fd_insert (m_fds mdc) (Z_to_bv 64 fd)
(FdFileW sink_path (Z_to_bv 64 (Z.of_nat (length W)) + len_word (bytes X))))
(with_fs (fs_set (m_fs mdc) sink_path (file_write (bytes W) (Z_to_bv 64 (Z.of_nat (length W))) (bytes X))) mdc) in
journal B MR STK sp0 FP L A mem md Lc Ac mem0 md' /\ sink_os md' fd (W ++ X).
Proof.
intros STK sp0 FP L A mem md Lc Ac mem0 mdc fd W X HJ Hfp (Hfs & Hfd & Hnm) Hlen md'.
assert (Hfw : file_write (bytes W) (Z_to_bv 64 (Z.of_nat (length W))) (bytes X) = bytes (W ++ X)).
{ rewrite file_write_append; [symmetry; apply bytes_app|]. rewrite word_to_nat_len by lia. symmetry. apply bytes_length. }
assert (Emd : md' = os_upd (m_vmmaps mdc)
(fd_insert (m_fds mdc) (Z_to_bv 64 fd) (FdFileW sink_path (Z_to_bv 64 (Z.of_nat (length W)) + len_word (bytes X))))
(fs_set (m_fs mdc) sink_path (bytes (W ++ X)))
(statpins_restrict (fs_set (m_fs mdc) sink_path (bytes (W ++ X))) (m_statpins mdc)) mdc).
{ subst md'. rewrite Hfw, with_fs_os_upd, with_fds_os_upd. reflexivity. }
split.
- rewrite Emd. apply (journal_os_upd B MR LAWS); [exact HJ | exact Hfp | | | apply fs_set_sorted].
+ intros fd'. destruct (bv_eqb (Z_to_bv 64 fd) fd') eqn:E.
* apply bv_eqb_eq in E. subst fd'. right. split; [right; eexists; exact Hfd|].
right. eexists. apply fd_lookup_insert_eq.
* left. apply fd_lookup_insert_neq. intros ->. rewrite (proj2 (bv_eqb_eq _ _) eq_refl) in E. discriminate E.
+ intros p Hp. apply fs_lookup_set_other. exact Hp.
- rewrite Emd. unfold sink_os. rewrite os_upd_fs, os_upd_fds. split; [apply fs_lookup_set_same|]. split.
+ rewrite fd_lookup_insert_eq. f_equal. f_equal. apply bv_eq. rewrite bv_add_unsigned.
unfold len_word. rewrite bytes_length, length_app, Nat2Z.inj_add.
rewrite !u64_small by lia. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
+ rewrite fd_remove_insert. exact Hnm.
Qed.
Lemma J_writev_node2 : forall regs pc mem0 STK sp0 FP L A mem md Lc Ac mdc Q fd W (iov b0 b1 : Z) X0 X1,
journal B MR STK sp0 FP L A mem md Lc Ac mem0 mdc -> sink_open_fp FP ->
sink_os mdc fd W -> 0 <= fd < 2 ^ 31 ->
bv_unsigned (getr regs 17) = 66 -> getr regs 10 = Z_to_bv 64 fd -> getr regs 12 = Z_to_bv 64 2 ->
getr regs 11 = Z_to_bv 64 iov -> 0 <= iov -> iov + 32 <= 2 ^ 47 ->
rdn segs mem0 (Z_to_bv 64 iov) 8 = Some (word_le8 (Z_to_bv 64 b0)) ->
rdn segs mem0 (Z_to_bv 64 (iov + 8)) 8 = Some (word_le8 (Z_to_bv 64 (Z.of_nat (length X0)))) ->
rdn segs mem0 (Z_to_bv 64 (iov + 16)) 8 = Some (word_le8 (Z_to_bv 64 b1)) ->
rdn segs mem0 (Z_to_bv 64 (iov + 24)) 8 = Some (word_le8 (Z_to_bv 64 (Z.of_nat (length X1)))) ->
garr8 segs mem0 b0 X0 -> garr8 segs mem0 b1 X1 ->
0 <= b0 -> b0 + Z.of_nat (length X0) <= 2 ^ 47 -> 0 <= b1 -> b1 + Z.of_nat (length X1) <= 2 ^ 47 ->
1 <= Z.of_nat (length X0) + Z.of_nat (length X1) <= MAX_RW_COUNT ->
Z.of_nat (length W) + Z.of_nat (length X0) + Z.of_nat (length X1) <= 2 ^ 62 ->
(forall md', journal B MR STK sp0 FP L A mem md Lc Ac mem0 md' -> sink_os md' fd (W ++ X0 ++ X1) ->
SR segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat (length X0) + Z.of_nat (length X1)))) (v_addi pc 4) mem0 (seg_rom segs)) md') Q) ->
SR segs (mkCfg (pend_at regs pc mem0 (seg_rom segs)) mdc) Q.
Proof.
intros regs pc mem0 STK sp0 FP L A mem md Lc Ac mdc Q fd W iov b0 b1 X0 X1 HJ Hfp Hos Hfdr Hno Hfd Hcnt Hiov Hiov0 Hiov1
Rb0 Rl0 Rb1 Rl1 G0 G1 Hb0 Hb0' Hb1 Hb1' Htot Hmax HK.
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
pose proof Hos as (Hfs & Hfdl & Hnm).
assert (HT : TASK_SIZE = 2 ^ 47) by reflexivity. assert (HM : MAX_RW_COUNT = 0x7ffff000) by reflexivity.
assert (Hiovu : bv_unsigned (getr regs 11) = iov) by (rewrite Hiov; apply u64_small; lia).
destruct (sink_os_written STK sp0 FP L A mem md Lc Ac mem0 mdc fd W (X0 ++ X1) HJ Hfp Hos
ltac:(rewrite length_app, Nat2Z.inj_add; lia)) as [HJ' Hos'].
eapply (SR_writev_file2 segs regs pc mem0 (seg_rom segs) mdc (Z_to_bv 64 fd) sink_path _ (bytes W)
(Z_to_bv 64 b0) (Z_to_bv 64 (Z.of_nat (length X0))) (Z_to_bv 64 b1) (Z_to_bv 64 (Z.of_nat (length X1)))
(bytes X0) (bytes X1) Q Hh Hlz Hno Hfdl).
- apply Syscall.fd32_id. rewrite u64_small by lia. lia.
- exact Hfd.
- exact Hcnt.
- apply ms_read_u64_of_rdn. rewrite Hiov. exact Rb0.
- apply ms_read_u64_of_rdn. rewrite Hiovu. exact Rl0.
- apply ms_read_u64_of_rdn. rewrite Hiovu. exact Rb1.
- apply ms_read_u64_of_rdn. rewrite Hiovu. exact Rl1.
- apply ms_read_bytes_of_rdn. rewrite word_to_nat_len by lia. apply rdn_of_garr8. exact G0.
- apply ms_read_bytes_of_rdn. rewrite word_to_nat_len by lia. apply rdn_of_garr8. exact G1.
- unfold access_okb. rewrite Hiovu, HT. apply andb_true_intro. split; apply Z.leb_le; lia.
- unfold access_okb. rewrite !u64_small by lia. rewrite HT. apply andb_true_intro. split; apply Z.leb_le; lia.
- unfold access_okb. rewrite !u64_small by lia. rewrite HT. apply andb_true_intro. split; apply Z.leb_le; lia.
- rewrite !u64_small by lia. lia.
- exact Hfs.
- rewrite !u64_small by lia. lia.
- rewrite u64_small by lia. rewrite bytes_length. unfold rw_bytes_max. lia.
- rewrite <- bytes_app.
assert (Elen : Z_to_bv 64 (Z.of_nat (length X0) + Z.of_nat (length X1)) = len_word (bytes (X0 ++ X1)))
by (unfold len_word; rewrite bytes_length, length_app, Nat2Z.inj_add; reflexivity).
specialize (HK _ HJ' Hos'). rewrite Elen in HK. exact HK.
Qed.
Lemma J_writev_node1 : forall regs pc mem0 STK sp0 FP L A mem md Lc Ac mdc Q fd W (iov b0 : Z) X0,
journal B MR STK sp0 FP L A mem md Lc Ac mem0 mdc -> sink_open_fp FP ->
sink_os mdc fd W -> 0 <= fd < 2 ^ 31 ->
bv_unsigned (getr regs 17) = 66 -> getr regs 10 = Z_to_bv 64 fd -> getr regs 12 = Z_to_bv 64 1 ->
getr regs 11 = Z_to_bv 64 iov -> 0 <= iov -> iov + 16 <= 2 ^ 47 ->
rdn segs mem0 (Z_to_bv 64 iov) 8 = Some (word_le8 (Z_to_bv 64 b0)) ->
rdn segs mem0 (Z_to_bv 64 (iov + 8)) 8 = Some (word_le8 (Z_to_bv 64 (Z.of_nat (length X0)))) ->
garr8 segs mem0 b0 X0 ->
0 <= b0 -> b0 + Z.of_nat (length X0) <= 2 ^ 47 ->
1 <= Z.of_nat (length X0) <= MAX_RW_COUNT ->
Z.of_nat (length W) + Z.of_nat (length X0) <= 2 ^ 62 ->
(forall md', journal B MR STK sp0 FP L A mem md Lc Ac mem0 md' -> sink_os md' fd (W ++ X0) ->
SR segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat (length X0)))) (v_addi pc 4) mem0 (seg_rom segs)) md') Q) ->
SR segs (mkCfg (pend_at regs pc mem0 (seg_rom segs)) mdc) Q.
Proof.
intros regs pc mem0 STK sp0 FP L A mem md Lc Ac mdc Q fd W iov b0 X0 HJ Hfp Hos Hfdr Hno Hfd Hcnt Hiov Hiov0 Hiov1
Rb0 Rl0 G0 Hb0 Hb0' Htot Hmax HK.
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
pose proof Hos as (Hfs & Hfdl & Hnm).
assert (HT : TASK_SIZE = 2 ^ 47) by reflexivity. assert (HM : MAX_RW_COUNT = 0x7ffff000) by reflexivity.
assert (Hiovu : bv_unsigned (getr regs 11) = iov) by (rewrite Hiov; apply u64_small; lia).
destruct (sink_os_written STK sp0 FP L A mem md Lc Ac mem0 mdc fd W X0 HJ Hfp Hos ltac:(lia)) as [HJ' Hos'].
eapply (SR_writev_file1 segs regs pc mem0 (seg_rom segs) mdc (Z_to_bv 64 fd) sink_path _ (bytes W)
(Z_to_bv 64 b0) (Z_to_bv 64 (Z.of_nat (length X0))) (bytes X0) Q Hh Hlz Hno Hfdl).
- apply Syscall.fd32_id. rewrite u64_small by lia. lia.
- exact Hfd.
- exact Hcnt.
- apply ms_read_u64_of_rdn. rewrite Hiov. exact Rb0.
- apply ms_read_u64_of_rdn. rewrite Hiovu. exact Rl0.
- apply ms_read_bytes_of_rdn. rewrite word_to_nat_len by lia. apply rdn_of_garr8. exact G0.
- unfold access_okb. rewrite Hiovu, HT. apply andb_true_intro. split; apply Z.leb_le; lia.
- unfold access_okb. rewrite !u64_small by lia. rewrite HT. apply andb_true_intro. split; apply Z.leb_le; lia.
- rewrite !u64_small by lia. lia.
- exact Hfs.
- rewrite !u64_small by lia. lia.
- rewrite u64_small by lia. rewrite bytes_length. unfold rw_bytes_max. lia.
- assert (Elen : Z_to_bv 64 (Z.of_nat (length X0)) = len_word (bytes X0)) by (unfold len_word; rewrite bytes_length; reflexivity).
specialize (HK _ HJ' Hos'). rewrite Elen in HK. exact HK.
Qed.
Lemma fd_lookup_remove_same : forall fds (fd : word), fd_lookup (fd_remove fds fd) fd = None.
Proof.
intros fds fd. unfold fd_remove. induction fds as [|[k e] r IH]; [reflexivity|]. cbn [List.filter fst].
destruct (bv_eqb k fd) eqn:Ek; cbn [negb]; [exact IH|]. cbn [fd_lookup]. rewrite Ek. exact IH.
Qed.
Lemma J_close_node : forall regs pc mem0 STK sp0 FP L A mem md Lc Ac mdc Q fd W,
journal B MR STK sp0 FP L A mem md Lc Ac mem0 mdc -> sink_open_fp FP ->
sink_os mdc fd W -> 0 <= fd < 2 ^ 31 ->
bv_unsigned (getr regs 17) = 57 -> getr regs 10 = Z_to_bv 64 fd ->
(forall md', journal B MR STK sp0 FP L A mem md Lc Ac mem0 md' ->
fd_names_path (m_fds md') sink_path = false -> m_fs md' = m_fs mdc ->
SR segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem0 (seg_rom segs)) md') Q) ->
SR segs (mkCfg (pend_at regs pc mem0 (seg_rom segs)) mdc) Q.
Proof.
intros regs pc mem0 STK sp0 FP L A mem md Lc Ac mdc Q fd W HJ Hfp (Hfs & Hfdl & Hnm) Hfdr Hno Hfd HK.
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
eapply (SR_close segs regs pc mem0 (seg_rom segs) mdc (Z_to_bv 64 fd) _ Q Hh Hlz Hno Hfd).
- apply Syscall.fd32_id. rewrite u64_small by lia. lia.
- exact Hfdl.
- apply HK.
+ rewrite with_fds_os_upd. apply (journal_os_upd B MR LAWS); [exact HJ | exact Hfp | | apply fs_rel_refl | auto].
intros fd'. destruct (bv_eqb (Z_to_bv 64 fd) fd') eqn:E.
* apply bv_eqb_eq in E. subst fd'. right. split; [right; eexists; exact Hfdl|]. left. apply fd_lookup_remove_same.
* left. apply fd_lookup_remove_neq. intros ->. rewrite (proj2 (bv_eqb_eq _ _) eq_refl) in E. discriminate E.
+ rewrite with_fds_os_upd, os_upd_fds. exact Hnm.
+ rewrite with_fds_os_upd, os_upd_fs. reflexivity.
Qed.
Definition open_tmp_errnos : list Z := EISDIR :: openat_errnos.
Lemma open_tmp_errnos_range : forall e, In e open_tmp_errnos -> 1 <= e <= 4095.
Proof. intros e He. cbv [open_tmp_errnos openat_errnos In] in He. repeat (destruct He as [<-|He]; [vm_compute; split; discriminate|]). destruct He. Qed.
Definition openat_outcome (mdc md' : Model) (RET : word) : Prop :=
((exists e, In e open_tmp_errnos /\ RET = errno_ret e) /\ m_fds md' = m_fds mdc /\ m_fs md' = m_fs mdc) \/
(exists fd : Z, 0 <= fd <= 4096 /\ RET = Z_to_bv 64 fd /\ fd_lookup (m_fds mdc) (Z_to_bv 64 fd) = None /\
m_fds md' = fd_insert (m_fds mdc) (Z_to_bv 64 fd) (FdFileW sink_path (Z_to_bv 64 0)) /\
m_fs md' = fs_set (m_fs mdc) sink_path []).
Lemma J_openat_node : forall regs pc mem0 STK sp0 FP L A mem md Lc Ac mdc Q,
journal B MR STK sp0 FP L A mem md Lc Ac mem0 mdc ->
sink_open_fp FP ->
stdio_env B mem0 ->
bv_unsigned (getr regs 17) = 56 -> getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = wr_create_flags ->
getr regs 11 = Z_to_bv 64 sk_path_addr ->
(forall RET md',
journal B MR STK sp0 FP L A mem md Lc Ac mem0 md' -> openat_outcome mdc md' RET ->
SR segs (mkCfg (mkst (regupd regs 10 RET) (v_addi pc 4) mem0 (seg_rom segs)) md') Q) ->
SR segs (mkCfg (pend_at regs pc mem0 (seg_rom segs)) mdc) Q.
Proof.
intros regs pc mem0 STK sp0 FP L A mem md Lc Ac mdc Q HJ Hfp Henv Hno Hdir Hfl Hpath HK.
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
destruct sink_path_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8). rewrite <- sink_path_eq in F1, F2, F3, F4, F5, F6, F7.
pose proof (stdio_env_path regs pc mem0 Henv) as Hcstr. rewrite <- Hpath in Hcstr.
destruct (fs_under (m_fs mdc) sink_path) eqn:Hun.
{
apply (SR_openat_tmp_isdir segs regs pc mem0 (seg_rom segs) mdc sink_path sink_name_bytes Q Hh Hlz Hno Hdir Hfl Hcstr F1 F3 F4 F5 F6 F7 F8 Hun).
apply HK; [exact HJ|]. left. split; [|split; reflexivity]. exists EISDIR. split; [left; reflexivity | reflexivity]. }
destruct (fd_lookup (m_fds mdc) (alloc_fd (m_fds mdc))) as [e0|] eqn:Hfree.
{
apply (SR_openat_tmp_create_full segs regs pc mem0 (seg_rom segs) mdc sink_path sink_name_bytes Q Hh Hlz Hno Hdir Hfl Hcstr F1 F3 F4 F5 F6 F7 F8 Hun).
- rewrite Hfree. discriminate.
- intros e He. apply HK; [exact HJ|]. left. split; [|split; reflexivity]. exists e. split; [right; exact He | reflexivity]. }
apply (SR_openat_tmp_create segs regs pc mem0 (seg_rom segs) mdc sink_path sink_name_bytes Q Hh Hlz Hno Hdir Hfl Hcstr F1 F3 F4 F5 F6 F7 F8 Hun Hfree).
- intros e He. apply HK; [exact HJ|]. left. split; [|split; reflexivity]. exists e. split; [right; exact He | reflexivity].
- pose proof (Checks.Sys.Fs.Open.alloc_fd_le (m_fds mdc)) as Hle. pose proof (u64_range (alloc_fd (m_fds mdc))) as Hr0.
set (fdw := alloc_fd (m_fds mdc)) in *.
rewrite <- (Z_to_bv_bv_unsigned 64 fdw). apply HK.
+ rewrite (with_fs_os_upd (fs_set (m_fs mdc) sink_path []) mdc). rewrite with_fds_os_upd. rewrite os_upd_twice.
rewrite os_upd_fs, os_upd_vmmaps, os_upd_statpins.
apply (journal_os_upd B MR LAWS); [exact HJ | exact Hfp | | | apply fs_set_sorted].
* intros fd'. rewrite Z_to_bv_bv_unsigned. destruct (bv_eqb fdw fd') eqn:E.
-- apply bv_eqb_eq in E. subst fd'. right. split; [left; exact Hfree|].
right. eexists. unfold fd_insert. cbn [fd_lookup fst]. rewrite (proj2 (bv_eqb_eq _ _) eq_refl). reflexivity.
-- left. unfold fd_insert. cbn [fd_lookup fst].
rewrite E. fold (fd_remove (m_fds mdc) fdw). apply fd_lookup_remove_neq.
intros ->. rewrite (proj2 (bv_eqb_eq _ _) eq_refl) in E. discriminate E.
* intros p Hp. apply fs_lookup_set_other. exact Hp.
+ right. exists (bv_unsigned fdw). rewrite !Z_to_bv_bv_unsigned.
split; [lia|]. split; [reflexivity|]. split; [exact Hfree|].
rewrite (with_fs_os_upd (fs_set (m_fs mdc) sink_path []) mdc), with_fds_os_upd, os_upd_twice, os_upd_fds, os_upd_fs, os_upd_fs. split; reflexivity.
Qed.
Lemma J_ioctl_winsz_node : forall regs pc mem0 STK sp0 FP L A mem md Lc Ac mdc Q fd off,
journal B MR STK sp0 FP L A mem md Lc Ac mem0 mdc ->
bv_unsigned (getr regs 17) = 29 -> getr regs 10 = Z_to_bv 64 fd -> 0 <= fd < 2 ^ 31 ->
fd_lookup (m_fds mdc) (Z_to_bv 64 fd) = Some (FdFileW sink_path off) ->
cmd32 (getr regs 11) = TIOCGWINSZ ->
SR segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem0 (seg_rom segs)) mdc) Q ->
SR segs (mkCfg (pend_at regs pc mem0 (seg_rom segs)) mdc) Q.
Proof.
intros regs pc mem0 STK sp0 FP L A mem md Lc Ac mdc Q fd off HJ Hno Hfd Hfdr Hlk Hcmd HK.
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
apply (SR_ioctl_winsz segs regs pc mem0 (seg_rom segs) mdc (Z_to_bv 64 fd) (FdFileW sink_path off) Q Hh Hlz Hno Hfd).
- apply Syscall.fd32_id. rewrite u64_small by lia. lia.
- exact Hlk.
- intros _ _. discriminate.
- exact Hcmd.
- exact HK.
Qed.
Lemma J_close_node_fds : forall regs pc mem0 STK sp0 FP L A mem md Lc Ac mdc Q fd W,
journal B MR STK sp0 FP L A mem md Lc Ac mem0 mdc -> sink_open_fp FP ->
sink_os mdc fd W -> 0 <= fd < 2 ^ 31 ->
bv_unsigned (getr regs 17) = 57 -> getr regs 10 = Z_to_bv 64 fd ->
(forall md', journal B MR STK sp0 FP L A mem md Lc Ac mem0 md' ->
m_fds md' = fd_remove (m_fds mdc) (Z_to_bv 64 fd) -> m_fs md' = m_fs mdc ->
SR segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem0 (seg_rom segs)) md') Q) ->
SR segs (mkCfg (pend_at regs pc mem0 (seg_rom segs)) mdc) Q.
Proof.
intros regs pc mem0 STK sp0 FP L A mem md Lc Ac mdc Q fd W HJ Hfp (Hfs & Hfdl & Hnm) Hfdr Hno Hfd HK.
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
eapply (SR_close segs regs pc mem0 (seg_rom segs) mdc (Z_to_bv 64 fd) _ Q Hh Hlz Hno Hfd).
- apply Syscall.fd32_id. rewrite u64_small by lia. lia.
- exact Hfdl.
- apply HK.
+ rewrite with_fds_os_upd. apply (journal_os_upd B MR LAWS); [exact HJ | exact Hfp | | apply fs_rel_refl | auto].
intros fd'. destruct (bv_eqb (Z_to_bv 64 fd) fd') eqn:E.
* apply bv_eqb_eq in E. subst fd'. right. split; [right; eexists; exact Hfdl|]. left. apply fd_lookup_remove_same.
* left. apply fd_lookup_remove_neq. intros ->. rewrite (proj2 (bv_eqb_eq _ _) eq_refl) in E. discriminate E.
+ rewrite with_fds_os_upd, os_upd_fds. reflexivity.
+ rewrite with_fds_os_upd, os_upd_fs. reflexivity.
Qed.
End f.
End c.
