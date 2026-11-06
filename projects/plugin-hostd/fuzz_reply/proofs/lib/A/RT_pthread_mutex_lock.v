(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contract alock_realizes (lib/A/W_sites.v) proved for
   fuzz_reply.asan's musl pthread_mutex_lock at 0x9883c. *)
(* The code (fuzz_reply.asan 0x9883c, the same bytes as the plain build's lib/Prog/pthread_mutex_lock.v):
     lbu a1,0(a0); andi a1,a1,15; bnez a1,slow; addi a2,a0,4; li a3,16;
     lr.w.aqrl a4,(a2); bne a4,a1,out; sc.w.aqrl a5,a3,(a2); bnez a5,retry;
   out: sext.w a4,a4; beqz a4,done; slow: ...; done: li a0,0; ret
   A normal mutex (type byte with low nibble 0) whose lock word is 0 takes the fast path: the reservation the lr.w
   sets is the one the sc.w uses, the sc.w stores 16 and succeeds, and the entry returns.  The proof steps the 13
   instructions concretely (SRr_msteps); the only store is the sc.w's 4 bytes at A + 4, which dest_ok says are
   writable, visible and not allocator-owned, so the allocator state is carried over by AR_laws's frame law.
   The theorem is in the donor's corollary shape (proofs/cgif/cgif_file_fuzzer/lib/A/AF0s.v:514): it holds for every
   asyms B whose AR obeys AR_laws, at the placement PB_fr (lib/A/W_img.v), whose pa_segs is frsegs. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YN2e YK1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_tbl W_place W_kit W_img W_sites.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AE2k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* Build identity: this is fuzz_reply.asan (ofl_head 0x5f9b68 is the ASan sink head AE2k.tfib_sink_head carries;
   main and LLVMFuzzerTestOneInput begin with their frame allocations at 0x81e4c and 0x840b0), and the entry the
   walks call as WS_pthread_mutex_lock is 0x9883c, whose first word is musl's `lbu a1,0(a0)`. *)
Lemma rt_lock_build_id :
  AE2k.A_ofl_head = 0x5f9b68 /\ @YI16.sk_ofl_head AE2k.tfib_sink_head = 0x5f9b68 /\
  fr_sigma WS_pthread_mutex_lock = 0x9883c /\
  option_map bv_unsigned (fetch_word frsegs (w64 0x81e4c)) = Some 0xfb010113 /\
  option_map bv_unsigned (fetch_word frsegs (w64 0x840b0)) = Some 0xec010113 /\
  option_map bv_unsigned (fetch_word frsegs (w64 0x9883c)) = Some 0x00054583.
Proof.
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [vm_compute; reflexivity|]. split; vm_compute; reflexivity.
Qed.

(* The code table of the entry's words 0x9883c .. 0x98874, decided against the image. *)
Definition lk_tbl : ctable := Eval vm_compute in build_table frsegs 0x9883c 15 TEmpty.
Lemma lk_tbl_eq : lk_tbl = build_table frsegs 0x9883c 15 TEmpty.
Proof. vm_cast_no_check (eq_refl lk_tbl). Qed.
Lemma lk_tbl_ok : table_ok frsegs lk_tbl.
Proof. rewrite lk_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
Lemma lk_fetch : forall (p : word) (w : bv 32), clookup lk_tbl (bv_unsigned p) = Some (bv_unsigned w) ->
fetch_word frsegs p = Some w.
Proof. intros p w H. rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w). apply lk_tbl_ok. exact H. Qed.
Lemma lk_F0 : fetch_word frsegs (w64 0x9883c) = Some (0x00054583%bv : bv 32).
Proof. apply lk_fetch. vm_compute. reflexivity. Qed.
Lemma lk_F1 : fetch_word frsegs (w64 0x98840) = Some (0x00f5f593%bv : bv 32).
Proof. apply lk_fetch. vm_compute. reflexivity. Qed.
Lemma lk_F2 : fetch_word frsegs (w64 0x98844) = Some (0x02059263%bv : bv 32).
Proof. apply lk_fetch. vm_compute. reflexivity. Qed.
Lemma lk_F3 : fetch_word frsegs (w64 0x98848) = Some (0x00450613%bv : bv 32).
Proof. apply lk_fetch. vm_compute. reflexivity. Qed.
Lemma lk_F4 : fetch_word frsegs (w64 0x9884c) = Some (0x01000693%bv : bv 32).
Proof. apply lk_fetch. vm_compute. reflexivity. Qed.
Lemma lk_F5 : fetch_word frsegs (w64 0x98850) = Some (0x1606272f%bv : bv 32).
Proof. apply lk_fetch. vm_compute. reflexivity. Qed.
Lemma lk_F6 : fetch_word frsegs (w64 0x98854) = Some (0x00b71663%bv : bv 32).
Proof. apply lk_fetch. vm_compute. reflexivity. Qed.
Lemma lk_F7 : fetch_word frsegs (w64 0x98858) = Some (0x1ed627af%bv : bv 32).
Proof. apply lk_fetch. vm_compute. reflexivity. Qed.
Lemma lk_F8 : fetch_word frsegs (w64 0x9885c) = Some (0xfe079ae3%bv : bv 32).
Proof. apply lk_fetch. vm_compute. reflexivity. Qed.
Lemma lk_F9 : fetch_word frsegs (w64 0x98860) = Some (0x0007071b%bv : bv 32).
Proof. apply lk_fetch. vm_compute. reflexivity. Qed.
Lemma lk_F10 : fetch_word frsegs (w64 0x98864) = Some (0x00070663%bv : bv 32).
Proof. apply lk_fetch. vm_compute. reflexivity. Qed.
Lemma lk_F11 : fetch_word frsegs (w64 0x98870) = Some (0x00000513%bv : bv 32).
Proof. apply lk_fetch. vm_compute. reflexivity. Qed.
Lemma lk_F12 : fetch_word frsegs (w64 0x98874) = Some (0x00008067%bv : bv 32).
Proof. apply lk_fetch. vm_compute. reflexivity. Qed.
Lemma lk_D0 : decode_any (0x00054583%bv : bv 32) =
Some (Load SZ1 false (11%bv : bv 5) (10%bv : bv 5) (0%bv : bv 12), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma lk_D1 : decode_any (0x00f5f593%bv : bv 32) =
Some (OpImm ALU_AND (11%bv : bv 5) (11%bv : bv 5) (15%bv : bv 12), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma lk_D2 : decode_any (0x02059263%bv : bv 32) =
Some (Branch BC_NE (11%bv : bv 5) (0%bv : bv 5) (36%bv : bv 13), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma lk_D3 : decode_any (0x00450613%bv : bv 32) =
Some (OpImm ALU_ADD (12%bv : bv 5) (10%bv : bv 5) (4%bv : bv 12), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma lk_D4 : decode_any (0x01000693%bv : bv 32) =
Some (OpImm ALU_ADD (13%bv : bv 5) (0%bv : bv 5) (16%bv : bv 12), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma lk_D5 : decode_any (0x1606272f%bv : bv 32) =
Some (Lr AW true true (14%bv : bv 5) (12%bv : bv 5), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma lk_D6 : decode_any (0x00b71663%bv : bv 32) =
Some (Branch BC_NE (14%bv : bv 5) (11%bv : bv 5) (12%bv : bv 13), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma lk_D7 : decode_any (0x1ed627af%bv : bv 32) =
Some (Sc AW true true (15%bv : bv 5) (12%bv : bv 5) (13%bv : bv 5), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma lk_D8 : decode_any (0xfe079ae3%bv : bv 32) =
Some (Branch BC_NE (15%bv : bv 5) (0%bv : bv 5) (8180%bv : bv 13), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma lk_D9 : decode_any (0x0007071b%bv : bv 32) =
Some (OpImm32 (14%bv : bv 5) (14%bv : bv 5) (0%bv : bv 12), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma lk_D10 : decode_any (0x00070663%bv : bv 32) =
Some (Branch BC_EQ (14%bv : bv 5) (0%bv : bv 5) (12%bv : bv 13), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma lk_D11 : decode_any (0x00000513%bv : bv 32) =
Some (OpImm ALU_ADD (10%bv : bv 5) (0%bv : bv 5) (0%bv : bv 12), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma lk_D12 : decode_any (0x00008067%bv : bv 32) =
Some (Jalr (0%bv : bv 5) (1%bv : bv 5) (0%bv : bv 12), 4%Z).
Proof. vm_refl_bv. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* A machine state between the lr.w and the sc.w: as mkst, but holding the reservation rv. *)
Definition mkst_rv (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (rv : option word) : machine_state :=
{| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := None;
   ms_resv := rv; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}.

(* lr.w: the 4 bytes at rs1, sign-extended into rd; the reservation becomes rs1. *)
Lemma step_lrw_rv : forall segs regs pc mem rom w aq rl rd rs1 bs v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Lr AW aq rl rd rs1, 4%Z) ->
amo_aligned AW (getr regs rs1) = true ->
rdn segs mem (getr regs rs1) 4%nat = Some bs ->
bytes_le_to_Z bs = bv_unsigned v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst_rv (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v)) (v_addi pc 4) mem rom
  (Some (getr regs rs1))).
Proof.
intros segs regs pc mem rom w aq rl rd rs1 bs v Hfetch Hecall Hdecode Hal Hread Hv.
step_pipeline Hfetch Hecall Hdecode.
unfold getr in *; rewrite ?bv_eqb0_is_x0 in *.
rewrite Hal; cbv beta iota delta [negb].
rewrite ov_rdn, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
unfold mkst_rv. destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* A branch not taken, with a reservation held. *)
Lemma step_branch_ft_rv : forall segs regs pc mem rom rv w c rs1 rs2 (imm : bv 13),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
branch_taken c (getr regs rs1) (getr regs rs2) = false ->
RiscvSemantics.step segs (mkst_rv regs pc mem rom rv) = MachineOk (mkst_rv regs (v_addi pc 4) mem rom rv).
Proof.
intros segs regs pc mem rom rv w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
unfold mkst_rv. step_pipeline Hfetch Hecall Hdecode.
unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
destruct (is_x0 rs1); destruct (is_x0 rs2);
cbv beta iota; rewrite Hc; cbv beta iota;
rewrite b_npc4; reflexivity.
Qed.

(* sc.w with the reservation at rs1: the low 4 bytes of rs2 stored at rs1, rd = 0, the reservation dropped. *)
Lemma step_scw_rv : forall segs regs pc mem rom w aq rl rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Sc AW aq rl rd rs1 rs2, 4%Z) ->
amo_aligned AW (getr regs rs1) = true ->
store_ok segs mem (getr regs rs1) 4%nat = true ->
RiscvSemantics.step segs (mkst_rv regs pc mem rom (Some (getr regs rs1))) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4)
  (wbytes mem (getr regs rs1) (word_to_le_bytes 4 (getr regs rs2))) rom).
Proof.
intros segs regs pc mem rom w aq rl rd rs1 rs2 Hfetch Hecall Hdecode Hal Hok.
unfold mkst_rv. step_pipeline Hfetch Hecall Hdecode.
unfold getr in *; rewrite ?bv_eqb0_is_x0 in *.
rewrite Hal; cbv beta iota delta [negb].
rewrite Z.eqb_refl; cbv beta iota.
rewrite Hok; cbv beta iota.
rewrite write_to_mem_wbytes, YK1e.low32_le_bytes, b_npc4.
destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma v_addi_0 : forall x : word, v_addi x 0 = x.
Proof. intros x. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma getr_other_u : forall regs (k r : bv 5) v, bv_unsigned r <> bv_unsigned k ->
getr (regupd regs k v) r = getr regs r.
Proof. intros regs k r v H. apply getr_other. intros E. subst. exact (H eq_refl). Qed.

Lemma aview_mod64 : forall segs (H : word -> bool) (m : word -> option byte) a,
aview segs H m a = aview segs H m (a mod 2 ^ 64).
Proof.
intros segs H m a. unfold aview, mbyte.
assert (E : Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia. }
rewrite E. reflexivity.
Qed.

(* The thirteen steps of the fast path, one lemma each, at their pcs. *)
Lemma lk_s0 : forall regs mem b, rdn frsegs mem (getr regs (10%bv : bv 5)) 1 = Some [b] ->
RiscvSemantics.step frsegs (mkst regs (w64 0x9883c) mem (seg_rom frsegs)) =
MachineOk (mkst (regupd regs (11%bv : bv 5) (Z_to_bv 64 (bv_unsigned b))) (w64 0x98840) mem (seg_rom frsegs)).
Proof.
intros regs mem b Hr.
assert (Hr' : rdn frsegs mem (v_addi (getr regs (10%bv : bv 5)) (bv_signed (0%bv : bv 12))) 1 = Some [b]).
{ change (bv_signed (0%bv : bv 12)) with 0. rewrite v_addi_0. exact Hr. }
rewrite (step_lbu frsegs _ _ _ _ _ _ _ _ _ lk_F0 eq_refl lk_D0 Hr'). reflexivity.
Qed.
Lemma lk_s1 : forall regs mem,
RiscvSemantics.step frsegs (mkst regs (w64 0x98840) mem (seg_rom frsegs)) =
MachineOk (mkst (regupd regs (11%bv : bv 5) (v_andi (getr regs (11%bv : bv 5)) 15)) (w64 0x98844) mem (seg_rom frsegs)).
Proof. intros regs mem. rewrite (step_andi frsegs _ _ _ _ _ _ _ _ lk_F1 eq_refl lk_D1). reflexivity. Qed.
Lemma lk_s2 : forall regs mem, getr regs (11%bv : bv 5) = w64 0 ->
RiscvSemantics.step frsegs (mkst regs (w64 0x98844) mem (seg_rom frsegs)) =
MachineOk (mkst regs (w64 0x98848) mem (seg_rom frsegs)).
Proof.
intros regs mem H.
assert (Hc : branch_taken BC_NE (getr regs (11%bv : bv 5)) (getr regs (0%bv : bv 5)) = false) by (rewrite H; reflexivity).
rewrite (step_branch_ft_gen frsegs _ _ _ _ _ _ _ _ _ lk_F2 eq_refl lk_D2 Hc). reflexivity.
Qed.
Lemma lk_s3 : forall regs mem,
RiscvSemantics.step frsegs (mkst regs (w64 0x98848) mem (seg_rom frsegs)) =
MachineOk (mkst (regupd regs (12%bv : bv 5) (v_addi (getr regs (10%bv : bv 5)) 4)) (w64 0x9884c) mem (seg_rom frsegs)).
Proof. intros regs mem. rewrite (step_addi frsegs _ _ _ _ _ _ _ _ lk_F3 eq_refl lk_D3). reflexivity. Qed.
Lemma lk_s4 : forall regs mem,
RiscvSemantics.step frsegs (mkst regs (w64 0x9884c) mem (seg_rom frsegs)) =
MachineOk (mkst (regupd regs (13%bv : bv 5) (w64 16)) (w64 0x98850) mem (seg_rom frsegs)).
Proof. intros regs mem. rewrite (step_addi frsegs _ _ _ _ _ _ _ _ lk_F4 eq_refl lk_D4). reflexivity. Qed.
Lemma lk_s5 : forall regs mem a bs, getr regs (12%bv : bv 5) = a -> bv_unsigned a mod 4 = 0 ->
rdn frsegs mem a 4 = Some bs -> bytes_le_to_Z bs = 0 ->
RiscvSemantics.step frsegs (mkst regs (w64 0x98850) mem (seg_rom frsegs)) =
MachineOk (mkst_rv (regupd regs (14%bv : bv 5) (w64 0)) (w64 0x98854) mem (seg_rom frsegs) (Some a)).
Proof.
intros regs mem a bs Ha Hal Hr Hz. subst a.
assert (Hal' : amo_aligned AW (getr regs (12%bv : bv 5)) = true).
{ unfold amo_aligned. change (amo_bytes AW) with 4. rewrite Hal. reflexivity. }
assert (Hz' : bytes_le_to_Z bs = bv_unsigned (w64 0)) by (rewrite Hz; reflexivity).
rewrite (step_lrw_rv frsegs _ _ _ _ _ _ _ _ _ _ _ lk_F5 eq_refl lk_D5 Hal' Hr Hz'). reflexivity.
Qed.
Lemma lk_s6 : forall regs mem rv, getr regs (14%bv : bv 5) = getr regs (11%bv : bv 5) ->
RiscvSemantics.step frsegs (mkst_rv regs (w64 0x98854) mem (seg_rom frsegs) rv) =
MachineOk (mkst_rv regs (w64 0x98858) mem (seg_rom frsegs) rv).
Proof.
intros regs mem rv H.
assert (Hc : branch_taken BC_NE (getr regs (14%bv : bv 5)) (getr regs (11%bv : bv 5)) = false).
{ rewrite H. unfold branch_taken. rewrite bv_eqb_refl. reflexivity. }
rewrite (step_branch_ft_rv frsegs _ _ _ _ _ _ _ _ _ _ lk_F6 eq_refl lk_D6 Hc). reflexivity.
Qed.
Lemma lk_s7 : forall regs mem a v, getr regs (12%bv : bv 5) = a -> getr regs (13%bv : bv 5) = v ->
bv_unsigned a mod 4 = 0 -> store_ok frsegs mem a 4 = true ->
RiscvSemantics.step frsegs (mkst_rv regs (w64 0x98858) mem (seg_rom frsegs) (Some a)) =
MachineOk (mkst (regupd regs (15%bv : bv 5) (w64 0)) (w64 0x9885c) (wbytes mem a (word_to_le_bytes 4 v)) (seg_rom frsegs)).
Proof.
intros regs mem a v Ha Hv Hal Hok. subst a v.
assert (Hal' : amo_aligned AW (getr regs (12%bv : bv 5)) = true).
{ unfold amo_aligned. change (amo_bytes AW) with 4. rewrite Hal. reflexivity. }
rewrite (step_scw_rv frsegs _ _ _ _ _ _ _ _ _ _ lk_F7 eq_refl lk_D7 Hal' Hok). reflexivity.
Qed.
Lemma lk_s8 : forall regs mem, getr regs (15%bv : bv 5) = w64 0 ->
RiscvSemantics.step frsegs (mkst regs (w64 0x9885c) mem (seg_rom frsegs)) =
MachineOk (mkst regs (w64 0x98860) mem (seg_rom frsegs)).
Proof.
intros regs mem H.
assert (Hc : branch_taken BC_NE (getr regs (15%bv : bv 5)) (getr regs (0%bv : bv 5)) = false) by (rewrite H; reflexivity).
rewrite (step_branch_ft_gen frsegs _ _ _ _ _ _ _ _ _ lk_F8 eq_refl lk_D8 Hc). reflexivity.
Qed.
Lemma lk_s9 : forall regs mem, getr regs (14%bv : bv 5) = w64 0 ->
RiscvSemantics.step frsegs (mkst regs (w64 0x98860) mem (seg_rom frsegs)) =
MachineOk (mkst (regupd regs (14%bv : bv 5) (w64 0)) (w64 0x98864) mem (seg_rom frsegs)).
Proof.
intros regs mem H.
assert (Hv : v_addiw (getr regs (14%bv : bv 5)) (bv_signed (0%bv : bv 12)) = w64 0) by (rewrite H; reflexivity).
rewrite (step_addiw_at frsegs _ _ _ _ _ _ _ _ _ lk_F9 eq_refl lk_D9 eq_refl Hv). reflexivity.
Qed.
Lemma lk_s10 : forall regs mem, getr regs (14%bv : bv 5) = w64 0 ->
RiscvSemantics.step frsegs (mkst regs (w64 0x98864) mem (seg_rom frsegs)) =
MachineOk (mkst regs (w64 0x98870) mem (seg_rom frsegs)).
Proof.
intros regs mem H.
assert (Hc : branch_taken BC_EQ (getr regs (14%bv : bv 5)) (getr regs (0%bv : bv 5)) = true) by (rewrite H; reflexivity).
rewrite (step_branch_tk_gen frsegs _ _ _ _ _ _ _ _ _ lk_F10 eq_refl lk_D10 Hc). reflexivity.
Qed.
Lemma lk_s11 : forall regs mem,
RiscvSemantics.step frsegs (mkst regs (w64 0x98870) mem (seg_rom frsegs)) =
MachineOk (mkst (regupd regs (10%bv : bv 5) (w64 0)) (w64 0x98874) mem (seg_rom frsegs)).
Proof. intros regs mem. rewrite (step_addi frsegs _ _ _ _ _ _ _ _ lk_F11 eq_refl lk_D11). reflexivity. Qed.
Lemma lk_s12 : forall regs mem t, getr regs (1%bv : bv 5) = t ->
RiscvSemantics.step frsegs (mkst regs (w64 0x98874) mem (seg_rom frsegs)) =
MachineOk (mkst regs (v_jalr t 0) mem (seg_rom frsegs)).
Proof. intros regs mem t H. rewrite (step_jalr_x0 frsegs _ _ _ _ _ _ _ _ lk_F12 eq_refl lk_D12 H). reflexivity. Qed.

(* The fast path end to end, on the restricted memory m: back at ra, the lock word at A + 4 stored with 16,
   only a0..a5 changed. *)
Lemma lk_run : forall regs (m : word -> option byte) A b,
getr regs (10%bv : bv 5) = w64 A -> 0 < A -> A mod 4 = 0 -> A + 12 <= 2 ^ 63 ->
mbyte frsegs m A = Some b -> bv_unsigned b mod 16 = 0 ->
val_mem frsegs m (A + 4) 4 0 ->
store_ok frsegs m (Z_to_bv 64 (A + 4)) 4 = true ->
exists RF, msteps frsegs (mkst regs (w64 0x9883c) m (seg_rom frsegs))
  (mkst RF (v_jalr (getr regs (1%bv : bv 5)) 0) (wbytes m (Z_to_bv 64 (A + 4)) (word_to_le_bytes 4 (w64 16)))
    (seg_rom frsegs)) /\
  (forall r : bv 5, bv_unsigned r < 10 \/ 15 < bv_unsigned r -> getr RF r = getr regs r).
Proof.
intros regs m A b H10 HA0 HA4 HA12 Hb Hb16 HV0 Hst.
assert (U : bv_unsigned (w64 A) = A) by (apply unsigned_lit_small; lia).
assert (UA4 : bv_unsigned (Z_to_bv 64 (A + 4)) = A + 4) by (apply unsigned_lit_small; lia).
assert (AL : bv_unsigned (Z_to_bv 64 (A + 4)) mod 4 = 0) by (rewrite UA4, Zplus_mod, HA4; reflexivity).
assert (HR0 : rdn frsegs m (getr regs (10%bv : bv 5)) 1 = Some [b]) by (rewrite H10; exact (YN2e.rdn1_mbyte frsegs m A b Hb)).
set (bs0 := [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] : list byte).
assert (RD : rdn frsegs m (Z_to_bv 64 (A + 4)) 4 = Some bs0).
{ apply (proj2 (rdn_mbytes frsegs m 4 (A + 4) bs0)). split; [reflexivity|]. intros i Hi.
  rewrite (HV0 i Hi). destruct i as [|[|[|[|i]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia]. }
set (R1 := regupd regs (11%bv : bv 5) (Z_to_bv 64 (bv_unsigned b))).
set (R2 := regupd R1 (11%bv : bv 5) (v_andi (getr R1 (11%bv : bv 5)) 15)).
set (R3 := regupd R2 (12%bv : bv 5) (v_addi (getr R2 (10%bv : bv 5)) 4)).
set (R4 := regupd R3 (13%bv : bv 5) (w64 16)).
set (R5 := regupd R4 (14%bv : bv 5) (w64 0)).
set (R7 := regupd R5 (15%bv : bv 5) (w64 0)).
set (R8 := regupd R7 (14%bv : bv 5) (w64 0)).
set (R10 := regupd R8 (10%bv : bv 5) (w64 0)).
assert (G2_11 : getr R2 (11%bv : bv 5) = w64 0).
{ unfold R2. rewrite getr_same by discriminate. unfold R1. rewrite getr_same by discriminate.
  pose proof (bv_unsigned_in_range _ b) as Rb. change (bv_modulus 8) with 256 in Rb.
  unfold v_andi, w64. rewrite unsigned_lit_small by lia. f_equal.
  change (bv_wrap 64 15) with (Z.ones 4). rewrite Z.land_ones by lia. exact Hb16. }
assert (G2_10 : getr R2 (10%bv : bv 5) = w64 A) by (unfold R2, R1; rewrite !getr_other by discriminate; exact H10).
assert (G4_12 : getr R4 (12%bv : bv 5) = Z_to_bv 64 (A + 4)).
{ unfold R4. rewrite getr_other by discriminate. unfold R3. rewrite getr_same by discriminate.
  rewrite G2_10. unfold v_addi. rewrite U. reflexivity. }
assert (G5_12 : getr R5 (12%bv : bv 5) = Z_to_bv 64 (A + 4)) by (unfold R5; rewrite getr_other by discriminate; exact G4_12).
assert (G5_13 : getr R5 (13%bv : bv 5) = w64 16) by (unfold R5; rewrite getr_other by discriminate; unfold R4; apply getr_same; discriminate).
assert (G5_14 : getr R5 (14%bv : bv 5) = w64 0) by (unfold R5; apply getr_same; discriminate).
assert (G5_11 : getr R5 (11%bv : bv 5) = w64 0) by (unfold R5, R4, R3; rewrite !getr_other by discriminate; exact G2_11).
assert (G7_15 : getr R7 (15%bv : bv 5) = w64 0) by (unfold R7; apply getr_same; discriminate).
assert (G7_14 : getr R7 (14%bv : bv 5) = w64 0) by (unfold R7; rewrite getr_other by discriminate; exact G5_14).
assert (G8_14 : getr R8 (14%bv : bv 5) = w64 0) by (unfold R8; apply getr_same; discriminate).
assert (G10_1 : getr R10 (1%bv : bv 5) = getr regs (1%bv : bv 5))
by (unfold R10, R8, R7, R5, R4, R3, R2, R1; rewrite !getr_other by discriminate; reflexivity).
exists R10. split.
- eapply mst_step; [reflexivity | exact (lk_s0 regs m b HR0) |].
  eapply mst_step; [reflexivity | exact (lk_s1 R1 m) |].
  eapply mst_step; [reflexivity | exact (lk_s2 R2 m G2_11) |].
  eapply mst_step; [reflexivity | exact (lk_s3 R2 m) |].
  eapply mst_step; [reflexivity | exact (lk_s4 R3 m) |].
  eapply mst_step; [reflexivity | exact (lk_s5 R4 m (Z_to_bv 64 (A + 4)) bs0 G4_12 AL RD eq_refl) |].
  eapply mst_step; [reflexivity | exact (lk_s6 R5 m _ (eq_trans G5_14 (eq_sym G5_11))) |].
  eapply mst_step; [reflexivity | exact (lk_s7 R5 m (Z_to_bv 64 (A + 4)) (w64 16) G5_12 G5_13 AL Hst) |].
  eapply mst_step; [reflexivity | exact (lk_s8 R7 _ G7_15) |].
  eapply mst_step; [reflexivity | exact (lk_s9 R7 _ G7_14) |].
  eapply mst_step; [reflexivity | exact (lk_s10 R8 _ G8_14) |].
  eapply mst_step; [reflexivity | exact (lk_s11 R8 _) |].
  eapply mst_step; [reflexivity | exact (lk_s12 R10 _ (getr regs (1%bv : bv 5)) G10_1) |].
  apply mst_refl.
- intros r Hr. unfold R10, R8, R7, R5, R4, R3, R2, R1.
  rewrite !getr_other_u by (let E := fresh in intros E; rewrite E in Hr; vm_compute in Hr; destruct Hr as [Hr|Hr]; discriminate Hr).
  reflexivity.
Qed.

Theorem rt_pthread_mutex_lock : forall B, AR_laws frsegs B ->
alock_realizes (PI := PB_fr) B (fr_sigma WS_pthread_mutex_lock).
Proof.
intros B LAWS ly S W regs mem md A tb HPRE H10 HA0 HA4 HA12 Htb Htb16 HV0 HIN HDST.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
set (HW := w_H W) in *.
change (option_map (fun b => bv_unsigned b) (mbyte frsegs (mrestrict HW mem) A) = Some tb) in Htb.
destruct (mbyte frsegs (mrestrict HW mem) A) as [b|] eqn:Hb; [|discriminate Htb].
cbn [option_map] in Htb. injection Htb as Htb.
assert (Hb16 : bv_unsigned b mod 16 = 0) by (rewrite Htb; exact Htb16).
assert (Hst : store_ok frsegs (mrestrict HW mem) (Z_to_bv 64 (A + 4)) 4 = true).
{ apply YN2e.store_ok_writable; [lia | lia |]. intros x Hx. exact (proj1 (HDST x Hx)). }
destruct (store_ok_restrict frsegs HW (w_Hoff W) 4 mem (Z_to_bv 64 (A + 4)) Hst) as [_ HRA].
assert (HVIS : forall x, A + 4 <= x < A + 8 -> HW (Z_to_bv 64 x) = false).
{ intros x Hx. pose proof (HRA (Z.to_nat (x - (A + 4))) ltac:(lia)) as E. unfold woff in E.
  rewrite unsigned_lit_small in E by lia. rewrite Z2Nat.id in E by lia.
  replace (A + 4 + (x - (A + 4))) with x in E by lia. exact E. }
destruct (lk_run regs (mrestrict HW mem) A b H10 HA0 HA4 HA12 Hb Hb16 HV0 Hst) as (RF & Hms & HRF).
unfold cfg_at. change (fr_sigma WS_pthread_mutex_lock) with 0x9883c.
eapply (SRr_msteps frsegs fr_wx W); [exact Hms|].
intros md' Hsame _.
set (bs16 := word_to_le_bytes 4 (w64 16)) in *.
set (mF := wbytes (mrestrict HW mem) (Z_to_bv 64 (A + 4)) bs16) in *.
set (mem' := munrestrict HW mem mF).
assert (L16 : length bs16 = 4%nat) by reflexivity.
(* the bytes of the new memory: the lock word at A + 4 is 16, every other byte is as before *)
assert (MB : forall x, 0 <= x < 2 ^ 64 -> mbyte frsegs (mrestrict HW mem') x =
  if (A + 4 <=? x) && (x <? A + 4 + 4) then nth_error bs16 (Z.to_nat (x - (A + 4)))
  else mbyte frsegs (mrestrict HW mem) x).
{ intros x Hx. destruct (HW (Z_to_bv 64 x)) eqn:Hh.
  - destruct ((A + 4 <=? x) && (x <? A + 4 + 4)) eqn:Hr.
    + exfalso. apply andb_prop in Hr as [R1 R2]. apply Z.leb_le in R1. apply Z.ltb_lt in R2.
      rewrite (HVIS x ltac:(lia)) in Hh. discriminate Hh.
    + unfold mbyte, mrestrict, mem', munrestrict. rewrite Hh. reflexivity.
  - transitivity (mbyte frsegs mF x).
    { unfold mbyte, mrestrict, mem', munrestrict. rewrite Hh. reflexivity. }
    unfold mF. rewrite (wbytes_mbyte frsegs bs16 (mrestrict HW mem) (A + 4) x) by (rewrite ?L16; lia).
    rewrite L16. reflexivity. }
assert (AVQ : forall a, 0 <= a < 2 ^ 64 -> ~ (A + 4 <= a < A + 8) ->
  aview frsegs HW mem' a = aview frsegs HW mem a).
{ intros a Ha Hn. unfold aview. rewrite (MB a Ha).
  destruct ((A + 4 <=? a) && (a <? A + 4 + 4)) eqn:E; [|reflexivity].
  exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia. }
assert (AVW : forall k, (k < 4)%nat ->
  mbyte frsegs (mrestrict HW mem') (A + 4 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte 16 4 k))).
{ intros k Hk. rewrite MB by lia.
  replace ((A + 4 <=? A + 4 + Z.of_nat k) && (A + 4 + Z.of_nat k <? A + 4 + 4)) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  replace (A + 4 + Z.of_nat k - (A + 4)) with (Z.of_nat k) by lia. rewrite Nat2Z.id.
  destruct k as [|[|[|[|k]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia]. }
assert (PRES : forall a, apresent HW mem a -> apresent HW mem' a).
{ intros a [Hh [b0 Hb0]]. split; [exact Hh|]. unfold mem', munrestrict. rewrite Hh.
  assert (G : mrestrict HW mem (Z_to_bv 64 a) <> None) by (unfold mrestrict; rewrite Hh, Hb0; discriminate).
  apply (wbytes_grows bs16 (mrestrict HW mem) (Z_to_bv 64 (A + 4))) in G. fold mF in G.
  destruct (mF (Z_to_bv 64 a)) as [b1|]; [exists b1; reflexivity | exfalso; exact (G eq_refl)]. }
assert (HAR' : AR frsegs B ly S W mem' md').
{ pose proof (same_but_materialized_frame md md' Hsame) as MF.
  apply (al_frame _ _ LAWS ly S W mem md mem' md' HAR).
  - intros a Ha Ho. apply AVQ; [exact Ha|]. intros Hin.
    destruct (HDST a ltac:(lia)) as (_ & Hno & _). exact (Hno Ho).
  - intros a Hv. change (w_H W) with HW in Hv |- *. rewrite aview_mod64 in Hv |- *.
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ra. set (a' := a mod 2 ^ 64) in *.
    destruct (Z_le_gt_dec (A + 4) a') as [L1|L1]; [destruct (Z_lt_ge_dec a' (A + 8)) as [L2|L2]|].
    + pose proof (AVW (Z.to_nat (a' - (A + 4))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
      replace (A + 4 + (a' - (A + 4))) with a' in X by lia.
      unfold aview. rewrite X. discriminate.
    + rewrite (AVQ a' Ra ltac:(lia)). exact Hv.
    + rewrite (AVQ a' Ra ltac:(lia)). exact Hv.
  - apply MF.
  - apply MF.
  - apply MF.
  - intros a _ Hh. change (w_H W) with HW in Hh. unfold mem', munrestrict. rewrite Hh. reflexivity. }
assert (RA : v_jalr (getr regs (1%bv : bv 5)) 0 = w64 (raZ regs)).
{ rewrite Hra. unfold raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
rewrite RA.
apply SRr_ret. unfold aentry_post.
split; [reflexivity|]. exists RF, mem', md'.
split; [reflexivity|].
split; [exact HAR'|].
split.
{ intros r Hr. apply HRF. unfold acallee_saved in Hr.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
  rewrite Z.mod_small by lia. lia. }
split; [exact Hsame|].
split; [exact AVW|].
split; [intros a Ha Hn _; exact (AVQ a Ha Hn)|].
exact PRES.
Qed.

End a.
