(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YL0b.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Reusable/YL0b_cfw.v, with its module paths changed; 8 of its 84 lines of code are new or changed and 8 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK0s YK15 YM06 YM02 YK0p YP0n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import
YP0m YP0e YP09 YP0l YP06 YP08 YP03 YP04 YP05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL07 YL0a.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0d YL0b YP0n2_cfw.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import SlotAgree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : malloc_syms.
Let segs := ms_segs B.
Theorem crz_read_win : forall E ss ms model fd pth off data bs (a cnt : Z) T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok_ecall segs E ss ms -> ss_resv ss = None ->
bv_unsigned (sv_denot E (sr_get (ss_regs ss) 17%bv)) = 63 ->
sv_denot E (sr_get (ss_regs ss) 10%bv) = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some (FdFile pth off) ->
fs_lookup (m_fs model) pth = Some data ->
bv_unsigned (sv_denot E (sr_get (ss_regs ss) 11%bv)) = a ->
bv_unsigned (sv_denot E (sr_get (ss_regs ss) 12%bv)) = cnt -> 0 < cnt <= 65536 ->
file_read data off (sv_denot E (sr_get (ss_regs ss) 12%bv)) = bs ->
win_check (ss_mem ss) a 65536 = true -> seg_win_check segs a (Z.to_nat 65536) = true -> 0 <= a -> a + 65536 <= 2 ^ 47 ->
(forall regs,
regs_ok E (ss_regs ss) regs -> facts_ok E (ss_facts ss) ->
mem_ok segs E (wbytes (ms_mem ms) (Z_to_bv 64 a) bs) (ss_mem ss) ->
(forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs (wbytes (ms_mem ms) (Z_to_bv 64 a) bs) (a + i) = nth_error bs (Z.to_nat i)) ->
(forall x : word, bv_unsigned x < a \/ a + Z.of_nat (length bs) <= bv_unsigned x ->
wbytes (ms_mem ms) (Z_to_bv 64 a) bs x = ms_mem ms x) ->
Z.of_nat (length bs) <= cnt ->
crealizes B (mkCfg (mkst (regupd regs 10%bv (len_word bs)) (v_addi (Z_to_bv 64 (ss_pc ss)) 4)
(wbytes (ms_mem ms) (Z_to_bv 64 a) bs) (seg_rom segs))
(with_fds (fd_insert (m_fds model) fd (FdFile pth (off + len_word bs))) model)) T) ->
crealizes B (mkCfg ms model) T.
Proof using.
intros E ss ms model fd pth off data bs a cnt T Hh Hlz HS Hrv H17 H10 H32 Hlk Hfs H11 H12 Hcnt Hbs Hck Hseg Ha0 Ha47 Hk.
destruct (st_ok_ecall_shape segs E ss ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
subst ms. cbn [ms_mem pend_at] in Hk.
pose proof (u64_range (sv_denot E (sr_get (ss_regs ss) 11%bv))) as Ra. rewrite H11 in Ra.
assert (Hlen : Z.of_nat (length bs) <= cnt).
{ rewrite <- Hbs. rewrite file_read_length. rewrite H12. lia. }
assert (HA : sv_denot E (sr_get (ss_regs ss) 11%bv) = Z_to_bv 64 a).
{ rewrite <- H11. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (Hau : bv_unsigned (Z_to_bv 64 a) = a).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
destruct (read_dest_ok_w segs mem (Z_to_bv 64 a) bs) as [w Hw].
{ intros i Hi. rewrite Hau. apply (seg_win_wview segs a 65536 mem); [exact Hseg | lia | lia]. }
eapply (crz_read_file B regs _ mem (seg_rom segs) model fd pth off data bs w T Hh Hlz).
- rewrite (Hregs 17%bv). exact H17.
- rewrite (Hregs 10%bv). exact H10.
- exact H32.
- exact Hlk.
- exact Hfs.
- rewrite (Hregs 12%bv). unfold modeled_rw_count. apply Z.leb_le. rewrite H12.
assert (X : rw_bytes_max = 2 ^ 17) by reflexivity. rewrite X. lia.
- rewrite (Hregs 12%bv). exact Hbs.
- rewrite (Hregs 11%bv), HA. exact Hw.
- rewrite (Hregs 11%bv), (Hregs 12%bv), HA, H12. unfold access_okb, TASK_SIZE. rewrite Hau.
apply andb_true_intro; split; apply Z.leb_le; lia.
- rewrite read_mem_wbytes, (Hregs 11%bv), HA.
assert (Hout : forall x : word, bv_unsigned x < a \/ a + Z.of_nat (length bs) <= bv_unsigned x ->
wbytes mem (Z_to_bv 64 a) bs x = mem x).
{ intros x [Hx|Hx]; [apply wbytes_below; rewrite Hau; lia | apply wbytes_above; rewrite Hau; lia]. }
apply Hk.
+ exact Hregs.
+ exact HG.
+ apply (mem_ok_win segs E mem _ (ss_mem ss) a 65536 Hmem Hck).
intros x Hx64 Hx. apply Hout. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia.
+ intros i Hi. unfold mbyte.
rewrite (wbytes_inside' bs mem (Z_to_bv 64 a) (Z_to_bv 64 (a + i))) by (rewrite ?Hau, ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite ?Z.mod_small by lia; lia).
rewrite Hau. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
replace (a + i - a) with i by lia. symmetry. apply nth_error_nth'. lia.
+ exact Hout.
+ exact Hlen.
Qed.
End e.
End d.
