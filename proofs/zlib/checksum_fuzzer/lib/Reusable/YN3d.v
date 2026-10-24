(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO00 YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YN3e YN35 YN3f YN3g YN34.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable segs : list Segment.
Lemma rz_sym_ioctl_winsz : forall E ss ms model fd ch T,
m_halted model = None -> m_vm_lazy model = [] -> st_ok_ecall segs E ss ms -> ss_resv ss = None ->
bv_unsigned (sv_denot E (sr_get (ss_regs ss) 17)) = 29 ->
sv_denot E (sr_get (ss_regs ss) 10) = fd -> fdchan fd ch model -> fd32 fd = fd ->
cmd32 (sv_denot E (sr_get (ss_regs ss) 11)) = TIOCGWINSZ ->
(forall ms', st_ok segs E (resume ss (SLit (2^64 - 25)) (ss_mem ss) (ss_facts ss)) ms' ->
ms_mem ms' = ms_mem ms -> realizes segs (mkCfg ms' model) T) ->
realizes segs (mkCfg ms model) T.
Proof.
intros E ss ms model fd ch T Hh Hlz HS Hrv H17 H10 [Hlk _] H32 H11 Hk.
destruct (st_ok_ecall_shape segs E ss ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
subst ms. cbn [ms_mem pend_at] in Hk.
eapply (rz_ioctl_winsz segs regs _ mem (seg_rom segs) model fd _ T Hh Hlz).
- rewrite (Hregs 17%bv). exact H17.
- rewrite (Hregs 10%bv). exact H10.
- exact H32.
- exact Hlk.
- intros rd wr; discriminate.
- rewrite (Hregs 11%bv). exact H11.
- apply Hk; [|reflexivity].
replace (errno_ret ENOTTY) with (sv_denot E (SLit (2^64 - 25)))
by (apply bv_eq; vm_compute; reflexivity).
apply st_ok_resume_sv; auto.
Qed.
End b.
Definition IOCTL_PC : Z := 0x182b4.
Definition pf0_check (k : nat) (ss : sstate) (ret : Z) : option (sstate * list Z) :=
match sym_runN src0segs src0tbl FUEL ss with
| (s1, RS_ecall) =>
if negb (ss_pc s1 =? IOCTL_PC) then None else
match sr_get (ss_regs s1) 17, sr_get (ss_regs s1) 10, sr_get (ss_regs s1) 11, ss_resv s1 with
| SLit 29, SLit 1, SLit 21523, None =>
let s2 := resume s1 (SLit (2^64 - 25)) (ss_mem s1) (ss_facts s1) in
match wx_step k s2 with
| Some (s3, s4, zs, 1) =>
if skeleton_eqb (skeleton (ss_mem ss)) (skeleton (ss_mem s3)) then
match sym_run_toN src0segs src0tbl FUEL ret s4 with
| (s5, RS_running) => if ss_pc s5 =? ret then Some (s5, zs) else None
| _ => None
end else None
| _ => None
end
| _, _, _, _ => None
end
| _ => None
end.
Theorem realizes_printf0_by_run : forall E ss ms model ch k ret s5 zs T,
st_ok src0segs E ss ms -> m_halted model = None -> m_vm_lazy model = [] ->
pf0_check k ss ret = Some (s5, zs) ->
fdchan (Z_to_bv 64 1) ch model ->
(forall ms' ws, st_ok src0segs (havoc E k ws) s5 ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
realizes src0segs (mkCfg ms' model) T) ->
realizes src0segs (mkCfg ms model) (t_emit (map (WriteEv ch) (map (Z_to_bv 8) zs)) T).
Proof.
intros E ss ms model ch k ret s5 zs T HS Hh Hlz Hck Hch Hk. unfold pf0_check in Hck.
destruct (sym_runN src0segs src0tbl FUEL ss) as [s1 st] eqn:Hrun. destruct st; try discriminate.
destruct (ss_pc s1 =? IOCTL_PC) eqn:Hpc; [|discriminate]. cbn [negb] in Hck.
destruct (sr_get (ss_regs s1) 17) as [no| | | | | | | | | |] eqn:H17; try discriminate.
destruct no as [|p|]; try discriminate. do 5 (destruct p as [p|p|]; try discriminate).
destruct (sr_get (ss_regs s1) 10) as [a0| | | | | | | | | |] eqn:H10; try discriminate.
destruct a0 as [|p|]; try discriminate. destruct p; try discriminate.
destruct (sr_get (ss_regs s1) 11) as [a1| | | | | | | | | |] eqn:H11; try discriminate.
destruct a1 as [|p|]; try discriminate. do 15 (destruct p as [p|p|]; try discriminate).
destruct (ss_resv s1) eqn:Hrv; try discriminate.
set (s2 := resume s1 (SLit (2^64 - 25)) (ss_mem s1) (ss_facts s1)) in Hck.
destruct (wx_step k s2) as [[[[s3 s4] zs'] fd]|] eqn:Hwx; [|discriminate].
destruct fd as [|p|]; try discriminate. destruct p; try discriminate.
destruct (skeleton_eqb (skeleton (ss_mem ss)) (skeleton (ss_mem s3))) eqn:Hsk; [|discriminate].
apply skeleton_eqb_eq in Hsk.
destruct (sym_run_toN src0segs src0tbl FUEL ret s4) as [s5' st'] eqn:Hrun2. destruct st'; try discriminate.
destruct (ss_pc s5' =? ret); [|discriminate]. injection Hck as <- <-.
eapply (rz_run_ecall src0segs src0tbl src0tbl_ok FUEL E ss s1 ms model _ Hh Hlz HS Hrun).
intros ms1 HS1 HF1.
eapply (rz_sym_ioctl_winsz src0segs E s1 ms1 model (Z_to_bv 64 1) ch _ Hh Hlz HS1 Hrv).
- rewrite H17. reflexivity.
- rewrite H10. reflexivity.
- exact Hch.
- reflexivity.
- rewrite H11. apply bv_eq. vm_compute. reflexivity.
- intros ms2 HS2 Hm2. fold s2 in HS2.
destruct (sym_run_sound src0segs src0tbl src0tbl_ok _ E ss s1 RS_ecall ms HS Hrun) as (_ & _ & _ & Hsk1 & _).
eapply (realizes_stdio_writev_by_run E s2 ms2 model ch k s3 s4 zs' (Zpos xH) _ HS2 Hh Hlz Hwx Hch).
intros ms4 ws HS4 HF4 Hsk4 Hma4.
eapply (rz_run_to_running src0segs src0tbl src0tbl_ok FUEL ret (havoc E k ws) s4 s5' ms4 model _ Hh Hlz HS4 Hrun2).
intros ms5 HS5 HF5. apply (Hk ms5 ws HS5).
assert (Hsk2 : skeleton (ss_mem s2) = skeleton (ss_mem ss)) by (subst s2; cbn [resume ss_mem]; exact Hsk1).
apply (frame_of_trans E (ss_mem ss) (ss_mem s2) (ms_mem ms) (ms_mem ms2) (ms_mem ms5)).
+ symmetry. exact Hsk2.
+ rewrite Hm2. exact HF1.
+ apply (frame_of_trans E (ss_mem s2) (ss_mem s4) (ms_mem ms2) (ms_mem ms4) (ms_mem ms5)).
* rewrite Hsk4, Hsk2. reflexivity.
* exact HF4.
* eapply frame_of_agree; [apply env_agree_havoc | exact Hma4 | exact HF5].
Qed.
End a.
Ltac src0_printf0_tac HS Hch k ret :=
lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
lazymatch type of Hch with fdchan (Z_to_bv 64 1) ?ch ?model =>
let r := eval vm_compute in (pf0_check k ss ret) in
lazymatch r with
| Some (?s5, ?zs) =>
let Hck := fresh "Hck" in
assert (Hck : pf0_check k ss ret = Some (s5, zs)) by (vm_compute; reflexivity);
apply (realizes_printf0_by_run E ss ms model ch k ret s5 zs _ HS ltac:(assumption) ltac:(assumption) Hck Hch);
clear Hck HS;
let ms' := fresh "ms" in let ws := fresh "ws" in let HF := fresh "HF" in
intros ms' ws HS HF;
sym_transport src0segs E ss s5 ms' HS HF
| None => fail "src0_printf0_tac: pf0_check failed on this state"
end
end end.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ss_pf_demo : sstate :=
set_regs_pc ss_main_f [(2%bv : reg, SOff 0 (-208)); (10%bv : reg, SLit 0); (8%bv : reg, SLit 7);
(9%bv : reg, SLit 0x2f9c0); (18%bv : reg, SLit 0); (19%bv : reg, SLit 0);
(20%bv : reg, SLit 0x2f9b0); (21%bv : reg, SLit 2); (22%bv : reg, SLit 0)] 0x140f4.
Lemma pf_demo_first : forall E ms model ch T,
st_ok src0segs E ss_pf_demo ms ->
m_halted model = None -> m_vm_lazy model = [] ->
fdchan (Z_to_bv 64 1) ch model ->
(forall ms' ws, st_ok src0segs (havoc E 10 ws)
(fst (match pf0_check 10 ss_pf_demo 0x140fc with Some p => p | None => (ss_pf_demo, []) end)) ms' ->
realizes src0segs (mkCfg ms' model) T) ->
realizes src0segs (mkCfg ms model) (t_emit (map (WriteEv ch) (to_bytes [48; 10])) T).
Proof.
intros E ms model ch T HS Hh Hlz Hch Hk.
src0_printf0_tac HS Hch 10%nat 0x140fc.
apply (Hk _ ws). exact HS.
Qed.
Definition ss_pf_after1 : sstate :=
Eval vm_compute in (fst (match pf0_check 10 ss_pf_demo 0x140fc with Some p => p | None => (ss_pf_demo, []) end)).
Lemma pf_demo_next_run :
match sym_run_toN src0segs src0tbl FUEL 0x140fc (set_regs_pc ss_pf_after1 [(10%bv : reg, SLit 0)] 0x140f4) with
| (s, RS_running) => (ss_pc s, chunk_word_at (ss_mem s) None (0x1f868 + 40))
| _ => (0, None)
end = (0x140fc, Some (SLit 0x5018a)).
Proof. vm_compute. reflexivity. Qed.
Definition ss_flush_demo : sstate :=
let s := fst (sym_run_toN src0segs src0tbl FUEL 0x140fc (set_regs_pc ss_pf_after1 [(10%bv : reg, SLit 0)] 0x140f4)) in
set_regs_pc s [(10%bv : reg, SLit 0)] 0x15b38.
Lemma flush_demo : forall E ms model ch,
st_ok src0segs E ss_flush_demo ms ->
m_halted model = None -> m_vm_lazy model = [] ->
fdchan (Z_to_bv 64 1) ch model ->
realizes src0segs (mkCfg ms model)
(t_emit (map (WriteEv ch) (to_bytes [48; 10])) (t_exit (Z_to_bv 64 0) (m_fs model))).
Proof.
intros E ms model ch HS Hh Hlz Hch.
src0_diag_exit_tac HS Hch 21%nat.
Qed.
Definition exit_demo_E : sstate := set_regs_pc ss_main_f [(10%bv : reg, SLit 3)] SRC1_EXIT.
Lemma exit_demo_E_ok : exit_run_check src0segs src0tbl exit_demo_E 3 = true.
Proof. vm_compute. reflexivity. Qed.
Definition stdout_dirty (rs : smem) : smem :=
match store_region rs None (SRC1_STDOUT_FILE + 32) 8 (CVal 8 (SLit (0x50188 + 1024))) with
| Some rs1 =>
match store_region rs1 None (SRC1_STDOUT_FILE + 40) 8 (CVal 8 (SOff 10 0x50188)) with
| Some rs2 =>
match store_region rs2 None (SRC1_STDOUT_FILE + 56) 8 (CVal 8 (SLit 0x50188)) with
| Some rs3 =>
match store_region rs3 None (SRC1_STDOUT_FILE + 72) 8 (CVal 8 (SLit SRC1_STDIO_WRITE)) with
| Some rs4 =>
match store_region rs4 None (SRC1_STDOUT_FILE + 144) 4 (CVal 4 (SLit 4294967295)) with
| Some rs5 => rs5 | None => [] end
| None => [] end
| None => [] end
| None => [] end
| None => [] end.
Definition exit_demo_F : sstate :=
add_atom (mkSS SRC1_EXIT (sr_sets (ss_regs ss_main_f) [(10%bv : reg, SLit 0)])
(stdout_dirty (ss_mem ss_main_f)) None (ss_facts ss_main_f))
10 (mkAF 1 6 0).
Lemma exit_demo_F_ok :
match run_to_check src0segs src0tbl SRC1_STDIO_WRITE exit_demo_F with
| Some ss1 => (ss_pc ss1, sr_get (ss_regs ss1) 1, sr_get (ss_regs ss1) 10,
sr_get (ss_regs ss1) 11, sr_get (ss_regs ss1) 12)
| None => (0, SLit 0, SLit 0, SLit 0, SLit 0)
end
= (SRC1_STDIO_WRITE, SLit SRC1_CLOSE_STDOUT_RET, SLit SRC1_STDOUT_FILE, SLit 0, SLit 0).
Proof. vm_compute. reflexivity. Qed.
End c.
