(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the SEGMENT INTERFACE of the ASan walk of fuzz_reply's drain
   (fuzz_reply.asan 0x830dc .. 0x83de4, 834 instructions), in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (call sites), lib/A/AC8b.v (a loop over concrete cut states) and
   lib/A/ACfj.v (segments joined at cut points), and of this lane's W_send_line_cx.v.
   Nothing is proved here: the file fixes the Section hypotheses, the entry context, the cut predicates over
   concrete machine states and the statement of every segment, so that the segments are proved in parallel.

   drain (s) is relay.c:171-224 with gesture_seen (relay.c:89-121) inlined and the harness's fuzz_recv
   (fuzz_reply.c:240-276) with source_of, reference_feed (217-238) and list_drop (153-158) inlined.
   Its contract is W_contract.v Section s7: dr_spec B MT MMAX RG (BASE + AF_fr_drain), post dr_post.
   The functional half is the plain proof's (lib/Prog/drain_b_c.v drain_run and lib/A/W_drain_model.v, the copy
   of lib/Prog/drain_b.v:22-336 of its pure round model); the memory half is W_journal.v's ajournal_gx at
   G_DR and the allocator's live-state meter MT.

   CUT POINTS (eight shared predicates; the plain proof's are drain_b.v DI/DRB/DRE/DLL/DLN/DLR/DGS):
     DI    0x831f8  the outer loop's head (for (;;)), in the round state s
     DEND  0x83bbc  no pending text: the closed / EAGAIN tail
     DRB   0x8347c  reference_feed's byte loop, after k of the n bytes
     DE    0x835ac  the byte loop left: the harness side of the round done, the drop and the lines to come
     DLL   0x836bc  the line [p, q) found in the relay's buffer
     DGS   0x837c8  gesture_seen's held-array search, for a begin or an end
     DLN   0x836f4  the line done: on to the next
     DLR   0x83a4c  no further line: the rest of the buffer moved down
   and the two ends: the eof store 0x83b64 and the epilogue 0x83b80 (dr_epi_stmt, generic as W_send_line_cx.v's
   sl_epi).  The byte loop gets its own cut (DRB) because it is a loop with a program call (list_push) and needs
   its own induction, exactly like the line loop; without it the segment from DI would be a third of the walk.

   THE MODEL.  A round's requests are the plain model's trace (Prog/RelayRunT.v rev over sptr).  The walk never
   reads a trace address, only the sizes, through the meter; so every cut predicate quantifies the base and the
   addresses (jb, a) existentially and keeps three facts about what is still to come: the requests `tl`, that the
   rounds from here leave drain's final state (dlater), and the budget (dbud: what the meter has already spent,
   what the rest costs, the live bytes and the largest request). *)
(* ARx FORM (route (b), step 3): Section cx proves dr_epi_x and dr_end_x, W_drain_cx_x.v's dr_epi_stmt_x and
   dr_end_stmt_x at the room texts, over any allocator relation ARx, its journal at W_contract_x.v's DRAIN_STK_x; the
   AR walk (Section c: dr_epi, dr_end) is unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx.
Import ListNotations.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_drain_cx_x W_w7_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* The trace type of the plain model (Prog/RelayRunF.v trF / adrF), named here without importing RelayRunF
   (whose ContractT chain redefines getr / mkst). *)
#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).
#[local] Notation dadrF := (RelayRunT.addr YO0i.sptr).
#[local] Notation dnret := (RelayRunT.nret YO0i.sptr).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* ---- The walk's program counters (listing slot = (addr - 0x822ec) / 4; AF_fr_drain = 0xdf0). ---- *)
Definition A_drain : Z := AF_fr_drain.                (* 0x830dc, the entry *)
Definition A_drainP : Z := BASE + A_drain.
Definition A_dr_top : Z := AF_fr_drain + 0x11c.       (* 0x831f8, the outer loop's head *)
Definition A_dr_feed : Z := AF_fr_drain + 0x3a0.      (* 0x8347c, reference_feed's byte loop *)
Definition A_dr_fed : Z := AF_fr_drain + 0x4d0.       (* 0x835ac, the byte loop left *)
Definition A_dr_line : Z := AF_fr_drain + 0x5e0.      (* 0x836bc, the line loop's head *)
Definition A_dr_next : Z := AF_fr_drain + 0x618.      (* 0x836f4, on to the next line *)
Definition A_dr_seen : Z := AF_fr_drain + 0x6ec.      (* 0x837c8, gesture_seen's held search *)
Definition A_dr_rest : Z := AF_fr_drain + 0x970.      (* 0x83a4c, no further line *)
Definition A_dr_end : Z := AF_fr_drain + 0xae0.       (* 0x83bbc, no pending text: closed / EAGAIN *)
Definition A_dr_eof : Z := AF_fr_drain + 0xa88.       (* 0x83b64, s->eof = 1 *)
Definition A_dr_epi : Z := AF_fr_drain + 0xaa4.       (* 0x83b80, the epilogue *)

(* The callee-saved registers in their frame slots 232(sp) (s11) .. 328(sp) (ra). *)
Definition DR_SAVED : list (bv 5) :=
[27%bv; 26%bv; 25%bv; 24%bv; 23%bv; 22%bv; 21%bv; 20%bv; 19%bv; 18%bv; 9%bv; 8%bv; 1%bv].

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the instance's laws *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* the runtime entries drain calls, at their SIGMA pcs (W_sites.v / the donor's YG0d.v) *)
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
(* the allocator's site rules (W_journal.v), at the trampolines the program calls *)
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis ASTRNDUP : astrndup_cf_rule SEGS B MT MMAX (SIGMA WS_strndup).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 -> aview SEGS (w_H W) mem a <> None.
(* the callees drain calls as a program: send_line (W7) and list_push (W2, in its G-generic form; drain
   instantiates it at list_push's own globals, the 16 bytes of h->expected at HA + 64, and lifts the callee's
   journal to G_DR with ajournal_gx_G_mono) *)
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
(* instance facts: errno is tp - 164 (W_sites.v aerrno_realizes) and its 4 bytes have zero shadow *)
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
(* the 4 * 96 bytes of g_s are a zero-shadow range of the image (a plain global, no redzone between the slots) *)
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
(* placement: g_s is reached by PAddHi (A_OBJ 22), so no rebase is needed for it *)
Hypothesis HVS : VAL (A_OBJ 22) = rg_s RG.
(* the string literals of gesture_seen (W_drain_cx.v dlit_at: their bytes, in .rodata, and ashp) *)
Hypothesis HLIT5 : dlit_at B 21 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 23 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 24 (W_END ++ [0]).
(* placement: the cells drain reads or writes are pairwise disjoint ((lo, hi) extents, as extent_of_region makes
   them; the pinned placement decides it by vm_compute).  G_DR's cells are g_s (4 * 96 bytes), the six of G_SL
   and errno; the runtime's two static cells (the GOT slot of the shadow base and the cell) are read, never
   written; the three literals are read-only. *)
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 21), VAL (A_OBJ 21) + 14); (VAL (A_OBJ 23), VAL (A_OBJ 23) + 6); (VAL (A_OBJ 24), VAL (A_OBJ 24) + 4)].
(* g_s lies in the image band (the walk computes shadow addresses of its fields) *)
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
(* the instance's request bound: the largest request drain makes is the expected list's vector, 32 * cap bytes
   with cap < 2 ^ 26; MMAX <= 2 ^ 30 gives list_push's growth premise `lp_vbytes l < MMAX` directly *)
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---- EPI: the epilogue 0x83b80 (ld ra/s0..s11, addi sp,sp,336, ret).  It writes nothing: the caller's
   continuation gets the same restricted memory and the same journal.  This copies W_send_line_cx.v sl_epi,
   with the drain frame (336) and the saved-register slots (232(sp) .. 328(sp)). ---- *)
Definition dBxX : sv := SOff 45 0.
Definition depi_regions : smem :=
[ YP09.mkRegion (Some 2%nat) 232 DRAIN_FRAME 232 232
  (map (fun i => YP09.mkChunk (232 + 8 * Z.of_nat i) (CVal 8 (SOff (32 + i) 0))) (seq 0 13)) ].
Definition depi_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (45%nat, mkAF SB SB 0) ] [] [].
Definition dss_epi : sstate := mkSS A_dr_epi sr_atoms depi_regions None depi_facts.
Definition depi_extra (regsE : bvmap 5 word) : list word := map (getr regsE) DR_SAVED ++ [Z_to_bv 64 SB].
Lemma nth_depi_extra : forall regsE i, (i < 13)%nat ->
  nth i (depi_extra regsE) (Z_to_bv 64 0) = getr regsE (nth i DR_SAVED 0%bv).
Proof.
intros regsE i Hi. unfold depi_extra. rewrite app_nth1 by (rewrite length_map; cbn; lia).
rewrite (nth_indep _ _ (getr regsE 0%bv)) by (rewrite length_map; cbn; lia). rewrite List.map_nth. reflexivity.
Qed.
Lemma dr_epi_entry : forall W regsX memX regsE,
alloc_ceiling <= spZ regsX -> spZ regsX + DRAIN_FRAME <= 2 ^ 47 -> 2 ^ 46 <= spZ regsX -> spZ regsX mod 16 = 0 ->
dr_saved W memX (spZ regsX) regsE ->
st_ok_pi SEGS VAL (Eimg (Ereg regsX (depi_extra regsE))) dss_epi
(restrict (w_H W) (mkst regsX (Z_to_bv 64 (BASE + A_dr_epi)) memX (seg_rom SEGS))).
Proof.
intros W regsX memX regsE Hceil Htop Hlo Hal HSV.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsX (depi_extra regsE))).
assert (E2 : ew E 2 = getr regsX 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsX _ 2 2%bv eq_refl)).
assert (E45 : ew E 45 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsX _ 13)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsX) by (rewrite E2; reflexivity).
unfold dss_epi, A_dr_epi. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold depi_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_map. apply Forall_forall. intros i Hi. apply in_seq in Hi. cbn [Nat.add] in Hi.
  apply (chunk_ok_val SEGS E _ (spZ regsX) (232 + 8 * Z.of_nat i) 8 _ (bv_unsigned (getr regsE (nth i DR_SAVED 0%bv)))).
  + cbn [sv_denot]. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite ew_Ereg_extra, nth_depi_extra by lia.
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + pose proof (bv_unsigned_in_range 64 (getr regsE (nth i DR_SAVED 0%bv))) as R. change (bv_modulus 64) with (2 ^ 64) in R. zside.
  + zside.
  + replace (spZ regsX + (232 + 8 * Z.of_nat i)) with (spZ regsX + 232 + 8 * Z.of_nat i) by lia. exact (HSV i ltac:(lia)).
- cbn [pairwise_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [depi_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E45, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold DRAIN_FRAME in Htop. revert Hceil Htop Hlo Hal. clear. unfold SB. intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia).
Qed.

Theorem dr_epi : dr_epi_stmt B RG.
Proof.
unfold dr_epi_stmt. intros cx ly1 S1 W1 m1 md1 k1 regs1 Q HJ HspX H3 H4 HraE HSV HQ.
unfold cfg_at.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi, Hstk0.
assert (HDS : DRAIN_STK = 16848) by reflexivity.
pose proof (dr_epi_entry W1 regs1 m1 (dxregs cx) ltac:(unfold DRAIN_FRAME in *; lia) ltac:(unfold DRAIN_FRAME in *; lia)
  ltac:(unfold DRAIN_FRAME in *; lia) ltac:(unfold DRAIN_FRAME in *; rewrite HspX; rewrite Zminus_mod, Hal16; reflexivity)
  ltac:(rewrite HspX; exact HSV)) as HS.
remember (Eimg (Ereg regs1 (depi_extra (dxregs cx)))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EX : forall i, (i < 13)%nat -> ew E (32 + i) = getr (dxregs cx) (nth i DR_SAVED 0%bv)).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (nth_depi_extra (dxregs cx) i Hi). }
assert (E2 : ew E 2 = getr regs1 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs1 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs1 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 4 4%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs1) by (rewrite E2; reflexivity).
assert (SHOK : sh_ok SEGS dBxX [] E (mrestrict (w_H W1) m1)) by constructor.
clear HE.
paj_run_tok RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19.
prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
eapply (RET W1 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
assert (RA : getr (ms_regs ms) 1 = getr (dxregs cx) 1) by (rewrite R1; exact (EX 12%nat ltac:(lia))).
rewrite RA, HraE. apply HQ.
- intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R2, Usp, HspX. replace (dsp0 cx - DRAIN_FRAME + 336) with (dsp0 cx) by (unfold DRAIN_FRAME; lia).
    unfold dsp0, spZ. apply Z_to_bv_bv_unsigned.
  + replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R3, E3. exact H3.
  + replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R4, E4. exact H4.
  + replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R8. exact (EX 11%nat ltac:(lia)).
  + replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R9. exact (EX 10%nat ltac:(lia)).
  + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R18. exact (EX 9%nat ltac:(lia)).
  + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R19. exact (EX 8%nat ltac:(lia)).
  + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R20. exact (EX 7%nat ltac:(lia)).
  + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R21. exact (EX 6%nat ltac:(lia)).
  + replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R22. exact (EX 5%nat ltac:(lia)).
  + replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R23. exact (EX 4%nat ltac:(lia)).
  + replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R24. exact (EX 3%nat ltac:(lia)).
  + replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R25. exact (EX 2%nat ltac:(lia)).
  + replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R26. exact (EX 1%nat ltac:(lia)).
  + replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R27. exact (EX 0%nat ltac:(lia)).
- unfold arm. intros x. apply HFr. intros (r & Hin & Hr). cbn [ss_mem dss_epi depi_regions In] in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia.
- apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

Definition dend_regions (cl : Z) : smem :=
[ YP09.mkRegion (Some 23%nat) 8 12 8 8 [YP09.mkChunk 8 (CVal 4 (SLit cl))] ].
Definition dend_facts (j : nat) : facts :=
mkFacts [ (18%nat, mkAF 0x10000 0x5fb000 3); (21%nat, mkAF SB SB 0); (22%nat, mkAF 4096 0x7fffff800000 0);
  (24%nat, mkAF (SB + 12 * Z.of_nat j) (SB + 12 * Z.of_nat j) 0) ] [] [].
Definition dss_end (j : nat) (cl : Z) : sstate := mkSS A_dr_end sr_atoms (dend_regions cl) None (dend_facts j).
Definition dBx1 : sv := SOff 24 0.
Definition dBx2 : sv := SOff 21 0.
Definition dSH1 : list shent := [ mkSHE 18 0 96 ].

Lemma dend_entry : forall (W : world SEGS) regs m (j : nat) cl SA,
(j < 4)%nat ->
getr regs 18 = w64 (rg_s RG) -> getr regs 21 = w64 SHADOW_OFF -> getr regs 22 = w64 SA ->
getr regs 23 = w64 (rg_s RG + ASRC * Z.of_nat j) -> getr regs 24 = w64 (SHADOW_OFF + 12 * Z.of_nat j) ->
4096 <= SA <= 0x7fffff800000 ->
val_mem SEGS (arm W m) (rg_s RG + ASRC * Z.of_nat j + 8) 4 cl -> 0 <= cl <= 1 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (dss_end j cl)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_end)) m (seg_rom SEGS))).
Proof.
intros W regs m j cl SA Hj R18 R21 R22 R23 R24 HSA Hcl Rcl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof HGSB as (G1 & G2 & G3).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs [])).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ n r Hr)).
assert (U18 : bv_unsigned (ew E 18) = rg_s RG)
  by (rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); rewrite R18; apply unsigned_lit_small; unfold ASRC in *; lia).
assert (U21 : bv_unsigned (ew E 21) = SB)
  by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); rewrite R21, unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity).
assert (U22 : bv_unsigned (ew E 22) = SA)
  by (rewrite (EREG 22%nat 22%bv) by (first [lia | reflexivity]); rewrite R22; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = rg_s RG + ASRC * Z.of_nat j)
  by (rewrite (EREG 23%nat 23%bv) by (first [lia | reflexivity]); rewrite R23; apply unsigned_lit_small; unfold ASRC in *; lia).
assert (U24 : bv_unsigned (ew E 24) = SB + 12 * Z.of_nat j)
  by (rewrite (EREG 24%nat 24%bv) by (first [lia | reflexivity]); rewrite R24, unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold dend_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U23.
  split; [unfold ASRC in *; lia|]. split; [unfold ASRC in *; lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ _ 8 4 (SLit cl) cl); [reflexivity | cbn; lia | cbn; lia | exact Hcl].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [dend_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U18, U21, U22, U24. unfold SB, ASRC in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity
    | change (2 ^ 3) with 8; lia].
Qed.

Lemma dend_shent1 : forall ly S (W : world SEGS) mem md E (j : nat),
AR SEGS B ly S W mem md -> (j < 4)%nat ->
U E dBx1 = SHADOW_OFF + 12 * Z.of_nat j -> U E (SOff 18 0) = rg_s RG ->
shent_ok SEGS dBx1 E (mrestrict (w_H W) mem) (mkSHE 18 0 96).
Proof.
intros ly S W mem md E j HAR Hj HB Hm.
pose proof HGSB as (G1 & G2 & G3).
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. rewrite <- (aview_rd_of SEGS).
pose proof (azs_range_addressable B LAWS ly S W mem md (rg_s RG) (4 * ASRC) HAR HGSZ) as HRA.
split.
- intros x Hx. destruct (HRA (x + ASRC * Z.of_nat j) ltac:(unfold ASRC in *; lia)) as (s & Hs & Hok).
  exists s. split.
  + unfold shadow_of_addr in *. replace (SHADOW_OFF + 12 * Z.of_nat j + x / 8)
      with (SHADOW_OFF + (x + ASRC * Z.of_nat j) / 8); [exact Hs|].
    unfold ASRC. replace (x + 96 * Z.of_nat j) with (x + (12 * Z.of_nat j) * 8) by lia.
    rewrite Z.div_add by lia. lia.
  + unfold saddr_ok in *. unfold ASRC in Hok.
    replace ((x + 96 * Z.of_nat j) mod 8) with (x mod 8) in Hok; [exact Hok|].
    replace (x + 96 * Z.of_nat j) with (x + (12 * Z.of_nat j) * 8) by lia. rewrite Z.mod_add by lia. reflexivity.
- intros a Ha. unfold SHADOW_OFF, ASRC in *. lia.
Qed.

Definition dr_eof_region : YP09.region := YP09.mkRegion (Some 22%nat) 4 8 4 8 [].
Definition dSH2 : list shent := [ mkSHE 22 4 8 ].

Lemma dend_closed : forall cx ly1 S1 W1 m1 md1 k1 regs1 (Q : world SEGS -> config -> Prop),
DBASE B MT MMAX RG cx ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m1 md1 k1 ->
In (dxG cx, ATABLE) (ablocks B ly1 S1) ->
awr W1 m1 (dxSA cx) AENT ->
getr regs1 22 = w64 (dxSA cx) -> getr regs1 18 = w64 (rg_s RG) -> getr regs1 21 = w64 SHADOW_OFF ->
getr regs1 23 = w64 (dHA RG cx) -> getr regs1 24 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) ->
val_mem SEGS (arm W1 m1) (dHA RG cx + 8) 4 1 ->
(forall regsF mF mdF,
  getr regsF 2 = getr regs1 2 -> getr regsF 3 = getr regs1 3 -> getr regsF 4 = getr regs1 4 ->
  @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 mF mdF k1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (dxSA cx + 4 <= a < dxSA cx + 8) ->
     aview SEGS (w_H W1) mF a = aview SEGS (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mF a) ->
  val_mem SEGS (arm W1 mF) (dxSA cx + 4) 4 1 ->
  SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_epi) regsF mF mdF) Q) ->
SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_end) regs1 m1 md1) Q.
Proof.
intros cx ly1 S1 W1 m1 md1 k1 regs1 Q HB HJ HGin HAW R22 R18 R21 R23 R24 Hcl KC.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (_ & _ & _ & HGle & HSAle & _ & _ & _ & Hj & _).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR HGin) as (_ & HG4 & HGc & Hap & _).
assert (RQT : req_size ATABLE = 896) by reflexivity.
rewrite RQT in HGc, Hap.
assert (HSA : 4096 <= dxSA cx <= 0x7fffff800000) by (unfold AENT, ATABLE in *; lia).
unfold dHA in R23, Hcl.
pose proof (dend_entry W1 regs1 m1 (dxj cx) 1 (dxSA cx) Hj R18 R21 R22 R23 R24 HSA Hcl ltac:(lia)) as HS.
remember (Eimg (Ereg regs1 [])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (UB1 : U E dBx1 = SHADOW_OFF + 12 * Z.of_nat (dxj cx))
  by (unfold dBx1; apply U_atom; [rewrite (EREG 24%nat 24%bv) by (first [lia | reflexivity]); exact R24 | unfold SHADOW_OFF; lia]).
assert (U18 : U E (SOff 18 0) = rg_s RG)
  by (apply U_atom; [rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); exact R18 | pose proof HGSB; unfold ASRC in *; lia]).
assert (UB2 : U E dBx2 = SHADOW_OFF)
  by (unfold dBx2; apply U_atom; [rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21 | unfold SHADOW_OFF; lia]).
assert (U22 : U E (SOff 22 0) = dxSA cx)
  by (apply U_atom; [rewrite (EREG 22%nat 22%bv) by (first [lia | reflexivity]); exact R22 | lia]).
assert (B22 : bv_unsigned (ew E 22) = dxSA cx)
  by (rewrite (EREG 22%nat 22%bv) by (first [lia | reflexivity]); rewrite R22; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS dBx1 dSH1 E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor]. exact (dend_shent1 ly1 S1 W1 m1 md1 E (dxj cx) HAR Hj UB1 U18). }
clear HE.
unfold cfg_at. change (w64 (BASE + A_dr_end)) with (Z_to_bv 64 (BASE + A_dr_end)).
set (j := dxj cx) in *. clearbody j.
destruct j as [|[|[|[|jj]]]]; [| | | | exfalso; lia].
all: paj_run_to_tok RUNTO HS HJ SHOK Bspan A_dr_eof; [apply awr_ok_x_of0; awr_ok_tac|].
all: rename HFr into FR1; rename HG0 into GR1; clear HF.
all: pose proof (st_ok_pi_submem _ _ _ [] HS ltac:(submem_tac) eq_refl) as HS0; clear HS.
all: assert (RGOK : region_ok SEGS E (ms_mem (restrict (w_H W1) ms)) dr_eof_region);
  [ unfold region_ok, dr_eof_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
    rewrite B22; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (writable_kept (w_H W1) m1 (ms_mem ms)); [apply (apresent_grows _ _ _ _ GR1)|];
    exact (HAW o ltac:(unfold AENT; lia)) |].
all: pose proof (st_ok_pi_add_region _ _ _ dr_eof_region HS0 eq_refl RGOK I) as HS1; clear HS0;
  cbn [ss_pc ss_regs ss_resv ss_facts ss_mem] in HS1.
all: assert (SHOK2 : sh_ok SEGS dBx2 dSH2 E (mrestrict (w_H W1) (ms_mem ms)));
  [ unfold sh_ok, dSH2; apply Forall_cons; [|apply Forall_nil];
    eapply (shent_ok_of_range SEGS (w_H W1) (ms_mem ms) E dBx2 22%nat (dxSA cx + 4) 4 (dxSA cx) 4 8);
    [ eapply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms) _ (dxG cx) ATABLE);
      [ exact (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) | exact HGin | lia
      | rewrite RQT; unfold AENT, ATABLE in *; lia ]
    | exact UB2 | exact U22 | lia | lia
    | intros x Hx; rewrite Z.min_l, Z.max_r in Hx by lia;
      unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, AENT, ATABLE in *; lia ] |].
all: paj_run_to_tok RUNTO HS1 HJ SHOK2 Bspan A_dr_epi;
  [ cbn [ss_mem]; apply awr_ok_x_cons; [|apply awr_ok_x_nil];
    unfold dr_eof_region; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite B22;
    intros x Hx; left; split; [|lia];
    unfold awr_byte; right; left; split;
    [ exists (dxSA cx, dxSA cx + AENT); split; [left; reflexivity | cbn [fst snd]; unfold AENT; lia]
    | exists (dxG cx), ATABLE; split; [exact HGin | rewrite RQT; unfold AENT, ATABLE in *; lia] ] |].
all: rename HFr into FR2; rename HG0 into GR2; clear HF.
all: prreg HS1 (2%bv : bv 5) X2; prreg HS1 (3%bv : bv 5) X3; prreg HS1 (4%bv : bv 5) X4.
all: pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS1 eq_refl) as RF; cbn [ms_mem restrict] in RF.
all: pmkst HS1.
all: apply KC;
  [ rewrite X2; apply EREG; [lia | reflexivity]
  | rewrite X3; apply EREG; [lia | reflexivity]
  | rewrite X4; apply EREG; [lia | reflexivity]
  | exact HJ
  | intros a Ha Hn;
    rewrite (aview_kept_out _ _ (w_H W1) (ms_mem ms) (ms_mem ms0) FR2 a Ha);
    [ apply (aview_kept_out _ _ (w_H W1) m1 (ms_mem ms) FR1 a Ha);
      intros (r & Hin & Hr); cbn in Hin; destruct Hin as [<- | []]; cbn in Hr; lia
    | intros (r & Hin & Hr); cbn in Hin; destruct Hin as [<- | []];
      cbn [dr_eof_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite B22 in Hr; lia ]
  | intros a Hp; apply (apresent_grows _ _ _ _ GR2); apply (apresent_grows _ _ _ _ GR1); exact Hp
  | unfold arm; eapply (field_of_region _ _ 22%nat (dxSA cx) _ 4 8 4 8 4 4%N (SLit 1) 1 RF);
    [ rewrite !ew_ewset_other by lia; exact B22 | left; reflexivity | reflexivity | cbn; lia | cbn; lia ] ].
Qed.

Lemma dend_eagain : forall cx ly1 S1 W1 m1 md1 k1 regs1 (Q : world SEGS -> config -> Prop),
DBASE B MT MMAX RG cx ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m1 md1 k1 ->
In (dxG cx, ATABLE) (ablocks B ly1 S1) ->
awr W1 m1 (as_errno B) 4 ->
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
getr regs1 3 = getr (dxregs cx) 3 -> getr regs1 4 = getr (dxregs cx) 4 ->
getr regs1 22 = w64 (dxSA cx) -> getr regs1 18 = w64 (rg_s RG) -> getr regs1 21 = w64 SHADOW_OFF ->
getr regs1 23 = w64 (dHA RG cx) -> getr regs1 24 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) ->
val_mem SEGS (arm W1 m1) (dHA RG cx + 8) 4 0 ->
(forall regsF mF mdF,
  getr regsF 2 = getr regs1 2 -> getr regsF 3 = getr regs1 3 -> getr regsF 4 = getr regs1 4 ->
  @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 mF mdF k1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= a < dsp0 cx - DRAIN_FRAME) ->
     aview SEGS (w_H W1) mF a = aview SEGS (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mF a) ->
  val_mem SEGS (arm W1 mF) (as_errno B) 4 11 ->
  SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_epi) regsF mF mdF) Q) ->
SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_end) regs1 m1 md1) Q.
Proof.
intros cx ly1 S1 W1 m1 md1 k1 regs1 Q HB HJ HGin HAWE Hsp H3 H4 R22 R18 R21 R23 R24 Hcl KC.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HPRE0 & _ & _ & HGle & HSAle & _ & _ & _ & Hj & _).
pose proof HPRE0 as (_ & _ & _ & Hgp & Htp & _).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR HGin) as (_ & HG4 & HGc & Hap & _).
assert (RQT : req_size ATABLE = 896) by reflexivity.
rewrite RQT in HGc, Hap.
assert (HSA : 4096 <= dxSA cx <= 0x7fffff800000) by (unfold AENT, ATABLE in *; lia).
unfold dHA in R23, Hcl.
pose proof (dend_entry W1 regs1 m1 (dxj cx) 0 (dxSA cx) Hj R18 R21 R22 R23 R24 HSA Hcl ltac:(lia)) as HS.
remember (Eimg (Ereg regs1 [])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (UB1 : U E dBx1 = SHADOW_OFF + 12 * Z.of_nat (dxj cx))
  by (unfold dBx1; apply U_atom; [rewrite (EREG 24%nat 24%bv) by (first [lia | reflexivity]); exact R24 | unfold SHADOW_OFF; lia]).
assert (U18 : U E (SOff 18 0) = rg_s RG)
  by (apply U_atom; [rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); exact R18 | pose proof HGSB; unfold ASRC in *; lia]).
assert (SHOK : sh_ok SEGS dBx1 dSH1 E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor]. exact (dend_shent1 ly1 S1 W1 m1 md1 E (dxj cx) HAR Hj UB1 U18). }
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
clear HE.
unfold cfg_at. change (w64 (BASE + A_dr_end)) with (Z_to_bv 64 (BASE + A_dr_end)).
set (j := dxj cx) in *. clearbody j.
destruct j as [|[|[|[|jj]]]]; [| | | | exfalso; lia].
all: paj_run_tok RUN HS HJ SHOK Bspan; [apply awr_ok_x_of0; awr_ok_tac|].
all: rename HFr into FR1; rename HG0 into GR1; clear HF.
all: pmkst HS.
all: prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4.
all: eapply SRr_bind;
  [ eapply (aj_gx_entry_at B LAWS (G_DR B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_errno_location)
      (fun _ => False) (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 (as_tp B - 164))
      W1 (ms_regs ms) (ms_mem ms) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx)
      ([] : list (Z * Z)) ly1 S1 _ k1 (- DRAIN_FRAME) _ HG eq_refl HJ);
    [ unfold spZ at 1; rewrite Q2, Usp; lia
    | reflexivity
    | unfold DRAIN_FRAME; lia
    | lia
    | unfold ESTACK, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia
    | rewrite Q3, (EREG 3%nat 3%bv), H3 by (first [lia | reflexivity]); exact Hgp
    | rewrite Q4, (EREG 4%nat 4%bv), H4 by (first [lia | reflexivity]); exact Htp
    | exact Q1
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | intros _; right; intros []
    | intros a []
    | intros a []
    | intros HPRE _; exact (AERRNO ly1 S1 W1 (ms_regs ms) (ms_mem ms) _ HPRE) ] |].
all: cbv beta; intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Herr & Hfr2 & Hpres2).
all: jafter_call_keep_pi HS 32%nat regs2 (mrestrict (w_H W1) mem2) HP2 ([] : list nat) HS2.
all: specialize (HS2 (Forall_nil _)); clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS.
all: remember (havoc E 32 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
all: assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
all: assert (OLDa : forall m, (m < 32)%nat -> ew Ea m = ew E m)
  by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
all: clear HEa.
all: prreg HS (10%bv : bv 5) R10.
all: assert (HERRI : 0x10000 <= as_errno B /\ as_errno B + 4 <= 0x5fb000);
  [ assert (HI4 : forall i, 0 <= i < 4 -> in_img SEGS (as_errno B + i));
    [ intros i Hi; apply (proj1 (HG (as_errno B + i) ltac:(unfold G_DR, G_SL, inG; cbn [In];
        repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ])))
    | pose proof (pa_img_range _ (HI4 0 ltac:(lia))) as P0; pose proof (pa_img_range _ (HI4 3 ltac:(lia))) as P3; lia ] |].
all: assert (F36 : ew Ea 36 = Z_to_bv 64 (as_errno B)) by (rewrite <- R10, Herr, HERRNO; reflexivity).
all: assert (B36 : bv_unsigned (ew Ea 36) = as_errno B) by (rewrite F36; apply unsigned_lit_small; lia).
all: apply (st_ok_pi_add_fact _ _ _ 36%nat (mkAF 0x10000 0x5fb000 0)) in HS;
  [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite B36, Z.pow_0_r, Z.mod_1_r; lia ].
all: apply (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 36%nat) 0 4 0 4 [])) in HS;
  [ | vm_compute; reflexivity
    | unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite B36; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
      intros o Ho; apply (writable_kept (w_H W1) m1 mem2);
      [ intros Hp; apply Hpres2; apply (apresent_grows _ _ _ _ GR1); exact Hp | exact (HAWE o Ho) ]
    | cbn; exact I ].
all: assert (UB : U Ea dBx2 = SHADOW_OFF)
  by (unfold dBx2; apply U_atom; [rewrite (OLDa 21%nat) by lia; rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21
      | unfold SHADOW_OFF; lia]).
all: assert (UE36 : U Ea (SOff 36 0) = as_errno B) by (apply U_atom; [exact F36 | lia]).
all: assert (SHOK3 : sh_ok SEGS dBx2 [mkSHE 36 0 4] Ea (mrestrict (w_H W1) mem2));
  [ unfold sh_ok; apply Forall_cons; [|apply Forall_nil];
    eapply (shent_ok_of_range SEGS (w_H W1) mem2 Ea dBx2 36%nat (as_errno B) 4 (as_errno B) 0 4);
    [ apply (azs_range_addressable B LAWS ly1 S1 W1 mem2 md2 (as_errno B) 4);
      [ exact (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) | exact HERRZ ]
    | exact UB | exact UE36 | lia | lia
    | intros x Hx; rewrite Z.min_l, Z.max_r in Hx by lia; unfold SHADOW_OFF; lia ] |].
all: paj_run_to_tok RUNTO HS HJ2 SHOK3 Bspan A_dr_epi;
  [ cbn [ss_mem]; apply awr_ok_x_cons_g; [|apply awr_ok_x_nil];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite B36;
    intros a Ha; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ] |].
all: rename HFr into FR3; rename HG0 into GR3; clear HF.
all: prreg HS (2%bv : bv 5) X2; prreg HS (3%bv : bv 5) X3; prreg HS (4%bv : bv 5) X4.
all: pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RF; cbn [ms_mem restrict] in RF.
all: pmkst HS.
all: apply KC;
  [ rewrite X2, OLDa by lia; apply EREG; [lia | reflexivity]
  | rewrite X3, OLDa by lia; apply EREG; [lia | reflexivity]
  | rewrite X4, OLDa by lia; apply EREG; [lia | reflexivity]
  | exact HJ2
  | intros a Ha Hn Hsc;
    rewrite (aview_kept_out _ _ (w_H W1) mem2 (ms_mem ms0) FR3 a Ha);
    [ rewrite (Hfr2 a Ha (fun x => x)); [|intros Hs; apply Hsc; lia];
      apply (aview_kept_out _ _ (w_H W1) m1 (ms_mem ms) FR1 a Ha);
      intros (r & Hin & Hr); cbn in Hin; destruct Hin as [<- | []]; cbn in Hr; lia
    | intros (r & Hin & Hr); cbn in Hin; destruct Hin as [<- | []];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite B36 in Hr; lia ]
  | intros a Hp; apply (apresent_grows _ _ _ _ GR3); apply Hpres2; apply (apresent_grows _ _ _ _ GR1); exact Hp
  | unfold arm; pose proof (field_of_region _ _ 36%nat (as_errno B) _ 0 4 0 4 0 4%N (SLit 11) 11 RF) as VF;
    rewrite Z.add_0_r in VF; apply VF;
    [ rewrite !ew_ewset_other by lia; exact B36 | left; reflexivity | reflexivity | cbn; lia | cbn; lia ] ].
Qed.

Definition dset_eof (e : rentry) (v : Z) : rentry :=
RE (re_fd e) v (re_skip e) (re_pad1 e) (re_buf e) (re_used e) (re_cap e) (re_hp e) (re_kh e)
  (re_pad2 e) (re_keys e) (re_U e) (re_junk e).

Lemma dset_eof_id : forall e, dset_eof e (re_eof e) = e.
Proof. intros []. reflexivity. Qed.

Lemma dend_aentry_eof : forall ly S (W : world SEGS) m e v,
aentry_ok B ly S W m e -> v = 0 \/ v = 1 -> aentry_ok B ly S W m (dset_eof e v).
Proof. intros ly S W m e v (_ & H) Hv. split; [exact Hv | exact H]. Qed.

Lemma dend_garr8_one4 : forall m a, val_mem SEGS m a 4 1 -> garr8 SEGS m a [1; 0; 0; 0].
Proof.
intros m a H j Hj. cbn [length] in Hj.
split; [|destruct j as [|[|[|[|j]]]]; cbn; lia].
intros k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
rewrite (H j Hj). f_equal. destruct j as [|[|[|[|j]]]]; try (vm_compute; reflexivity). lia.
Qed.

Lemma dend_garr8_eof : forall (W : world SEGS) m m' SA e,
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
(forall x, SA <= x < SA + AENT -> ~ (SA + 4 <= x < SA + 8) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
val_mem SEGS (arm W m') (SA + 4) 4 1 ->
garr8 SEGS (arm W m') SA (bzs (entry_bytes (dset_eof e 1))).
Proof.
intros W m m' SA e HE0 KV Hp1 Hp2 VM.
unfold entry_bytes, dset_eof, re_nheld in HE0 |- *.
cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk] in HE0 |- *.
unfold bzs in HE0 |- *. rewrite !map_app in HE0 |- *.
apply (garr8_app SEGS) in HE0 as [HA HE0]. apply (garr8_app SEGS) in HE0 as [_ HC].
apply (garr8_app SEGS). split.
- eapply (garr8_frame SEGS); [exact HA|]. intros x Hx. unfold arm. apply (mbyte_of_aview SEGS).
  rewrite length_map, Mem.length_le4 in Hx. apply KV; unfold AENT; lia.
- apply (garr8_app SEGS). rewrite !length_map, !Mem.length_le4 in HC |- *. split.
  + lazymatch goal with |- garr8 _ _ _ (map bz ?l) => replace (map bz l) with [1; 0; 0; 0] by (vm_compute; reflexivity) end.
    apply dend_garr8_one4. replace (SA + Z.of_nat 4) with (SA + 4) by lia. exact VM.
  + eapply (garr8_frame SEGS); [exact HC|]. intros x Hx. unfold arm. apply (mbyte_of_aview SEGS).
    rewrite !length_app, !length_map, !Mem.length_le4, !Mem.length_le8, Hp1, Hp2 in Hx.
    apply KV; unfold AENT; lia.
Qed.

Lemma dend_bk : forall (W : world SEGS) m m' (P : Z -> Prop) a,
(forall x, 0 <= x < 2 ^ 64 -> ~ P x -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
(forall x, apresent (w_H W) m x -> apresent (w_H W) m' x) ->
0 <= a < 2 ^ 64 -> ~ P a -> abyte_kept W m W m' a.
Proof.
intros W m m' P a KV PR Ha HP. split; [exact (KV a Ha HP)|].
unfold arm. apply writable_kept. apply PR.
Qed.

Definition dlow (cx : dcx) (a : Z) : Prop := 0 <= a < alloc_ceiling /\ ~ (dxG cx <= a < dxG cx + ATABLE).

Lemma dend_zall : forall a l j d, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l d).
Proof.
intros a l. induction l as [|b l IH]; intros j d H Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma dend_zpw : forall l i j d, zpairwise_disjoint l -> (i < j)%nat -> (j < length l)%nat ->
zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|a l IH]; intros i j d H Hij Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct i as [|i].
- destruct j as [|j]; [lia|]. cbn [nth]. apply dend_zall; [exact H1 | lia].
- destruct j as [|j]; [lia|]. cbn [nth]. apply IH; [exact H2 | lia | lia].
Qed.

Lemma dend_errno_sep : forall a,
(rg_s RG <= a < rg_s RG + 4 * ASRC \/ rg_client RG <= a < rg_client RG + 4 \/
 rg_client_broken RG <= a < rg_client_broken RG + 1 \/ rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/
 rg_send_dead RG <= a < rg_send_dead RG + 1 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_nout RG <= a < rg_nout RG + 8 \/ rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8) ->
~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha He.
pose proof (dend_zpw _ 2 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D2.
pose proof (dend_zpw _ 3 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D3.
pose proof (dend_zpw _ 4 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D4.
pose proof (dend_zpw _ 5 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D5.
pose proof (dend_zpw _ 6 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D6.
pose proof (dend_zpw _ 7 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D7.
pose proof (dend_zpw _ 8 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D8.
pose proof (dend_zpw _ 9 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D9.
pose proof (dend_zpw _ 10 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D10.
cbn [nth] in D2, D3, D4, D5, D6, D7, D8, D9, D10. unfold zdisj in *. cbn [fst snd] in *. lia.
Qed.

Lemma dend_low_img : forall cx ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> In (dxG cx, ATABLE) (ablocks B ly S) -> 0x10000 <= a < 0x5fb000 -> dlow cx a.
Proof.
intros cx ly S W mem md a HAR Hin Ha.
pose proof (blk_off_imgP B ly S W mem md _ _ HAR Hin) as Ho. unfold off_img in Ho.
pose proof asan_consts as (C1 & _).
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in Ho.
unfold dlow, ATABLE in *. lia.
Qed.

Lemma dend_low_blk : forall cx ly S (W : world SEGS) mem md L p n a,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
In (p, n) L -> p <= a < p + req_size n ->
dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S W mem md L p n a HAR HP HL Ha.
assert (Hin : In (p, n) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); right; exact HL).
destruct (al_blocks SEGS B LAWS ly S W mem md p n HAR Hin) as (_ & H4 & Hc & _).
destruct (in_split _ _ HL) as (l1 & l2 & ->).
assert (HP2 : Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: (p, n) :: l1 ++ l2))
  by (eapply Permutation_trans; [exact HP | apply perm_skip; apply Permutation_sym, Permutation_middle]).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR HP2) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in Hd.
split; [unfold dlow, ATABLE; lia|].
intros He. apply (blk_img SEGS B LAWS ly S W mem md p n a HAR Hin ltac:(lia)).
apply (proj1 (HG a ltac:(unfold G_DR, G_SL, inG; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))).
Qed.

Lemma dend_gs_ok : forall cx ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> In (dxG cx, ATABLE) (ablocks B ly S) -> rg_s RG <= a < rg_s RG + 4 * ASRC ->
dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S W mem md a HAR Hin Ha. pose proof HGSB as (G1 & G2 & _).
split; [apply (dend_low_img cx ly S W mem md a HAR Hin); unfold ASRC in *; lia|].
apply dend_errno_sep. left. exact Ha.
Qed.

Lemma dend_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.

Lemma dend_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Lemma dend_fp_entry : forall cx ly S (W : world SEGS) mem md e L,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (aentry_blks e) -> In b L) -> aentry_ok B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S W mem md e L HAR HP HB HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & _ & Hbuf & _ & Hhp & _ & _ & Hks).
assert (BLK : forall p n, In (p, n) (aentry_blks e) -> 0 <= n -> p <= a < p + n ->
  dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros p n Hin Hn Hpa. pose proof (req_size_pos n Hn) as (_ & Hrq).
  exact (dend_low_blk cx ly S W mem md L p n a HAR HP (HB _ Hin) ltac:(lia)). }
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  apply (BLK (re_buf e) (re_cap e)); [| lia | lia].
  unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
- cbn [In] in Hr. destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. unfold bzs, key_ptrs in Ha. cbn [map concat length] in Ha. lia.
    * unfold bzs in Ha. rewrite length_map, dend_key_ptrs_len in Ha. unfold re_nheld in Hk1.
      apply (BLK (re_hp e) (re_kh e)); [| lia | lia].
      unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
      rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (BLK (key_addr k) (Z.of_nat (length (key_text k)) + 1)); [| lia | lia].
    unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
    apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
Qed.

Lemma dend_fp_list : forall cx ly S (W : world SEGS) mem md L LA l lines,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (alist_blks l) -> In b L) -> In (dxG cx, ATABLE) (ablocks B ly S) ->
alist_at B ly S W mem LA l lines -> rg_s RG <= LA -> LA + 16 <= rg_s RG + 4 * ASRC ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S W mem md L LA l lines HAR HP HB HGin HL Hlo Hhi r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
assert (BLK : forall p n, In (p, n) (alist_blks l) -> 0 <= n -> p <= a < p + n ->
  dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros p n Hin Hn0 Hpa. pose proof (req_size_pos n Hn0) as (_ & Hrq).
  exact (dend_low_blk cx ly S W mem md L p n a HAR HP (HB _ Hin) ltac:(lia)). }
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (dend_gs_ok cx ly S W mem md a HAR HGin). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, dend_recs_len in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (BLK (hl_v l) (AREC * hl_cap l)); [| unfold AREC; lia | unfold hl_n, AREC in *; lia].
    unfold alist_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (BLK (fst q) (Z.of_nat (length (snd q)) + 1)); [| lia | lia].
    unfold alist_blks. apply in_or_app. right.
    apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hq.
Qed.

Lemma dend_fp_src : forall cx ly S (W : world SEGS) mem md L h,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (asrc_blks h) -> In b L) -> In (dxG cx, ATABLE) (ablocks B ly S) -> (dxj cx < 4)%nat ->
asrc_at B ly S W mem (dHA RG cx) h ->
forall r, In r (asrc_fp (dHA RG cx) h) -> forall a, fst r <= a < snd r ->
dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S W mem md L h HAR HP HB HGin Hj HS r Hr a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (unfold dHA, ASRC; lia).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (dend_gs_ok cx ly S W mem md a HAR HGin). lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq).
  apply (dend_low_blk cx ly S W mem md L (hs_partial h) APARTIAL a HAR HP); [apply HB; left; reflexivity | lia].
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + exact (dend_fp_list cx ly S W mem md L (dHA RG cx + 16) (hs_pending h) false HAR HP
      (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_introl Hb)))) HGin Hpend
      ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * exact (dend_fp_list cx ly S W mem md L (dHA RG cx + 64) (hs_expected h) true HAR HP
        (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hb)))))) HGin Hexp
        ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
    * exact (dend_fp_list cx ly S W mem md L (dHA RG cx + 80) (hs_held h) true HAR HP
        (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hb)))))) HGin Hheld
        ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
Qed.

Lemma dend_fp_out : forall cx ly S (W : world SEGS) mem md c O mx no cap out L,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (aout_blks cap out) -> In b L) ->
aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
dlow cx a /\ (r <> (as_errno B, as_errno B + 4) -> ~ (as_errno B <= a < as_errno B + 4)).
Proof.
intros cx ly S W mem md c O mx no cap out L HAR HP HB HOUT r Hr a Ha.
assert (GT : In (dxG cx, ATABLE) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
assert (IMG : forall x, 0x10000 <= x < 0x5fb000 -> dlow cx x)
  by (intros x Hx; exact (dend_low_img cx ly S W mem md x HAR GT Hx)).
assert (GDR : forall x, inG (G_DR B RG) x -> 0x10000 <= x < 0x5fb000)
  by (intros x Hx; exact (pa_img_range _ (proj1 (HG x Hx)))).
pose proof (pa_obj_img 9 ltac:(lia)) as P9. rewrite HV9 in P9.
pose proof (pa_obj_img 12 ltac:(lia)) as P12. rewrite HV12 in P12.
pose proof HSM as (Hs1 & Hs2).
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- split; [apply IMG; lia | intros _; apply dend_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep; tauto].
- split; [apply IMG; lia | intros _; apply dend_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep; tauto].
- split; [apply IMG; lia | intros _; apply dend_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros Hne; exfalso; apply Hne; reflexivity].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq).
  destruct (dend_low_blk cx ly S W mem md L out cap a HAR HP) as [D1 D2];
    [apply HB; unfold aout_blks; rewrite Hc0; left; reflexivity | lia |].
  split; [exact D1 | intros _; exact D2].
Qed.

Lemma dend_aout_ev : forall ly S (W : world SEGS) m m' c O mx no cap out ev,
aout_at B RG ly S W m c O mx no cap out ->
(forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
   ~ (as_errno B <= a < as_errno B + 4) -> abyte_kept W m W m' a) ->
(cap <> 0 -> forall a, out <= a < out + cap -> ~ (as_errno B <= a < as_errno B + 4)) ->
val_mem SEGS (arm W m') (as_errno B) 4 ev -> awr W m' (as_errno B) 4 -> 0 <= ev < 2 ^ 32 ->
aout_at B RG ly S W m' (CTL (ct_cl c) (ct_br c) (ct_dd c) (ct_ei c) ev) O mx no cap out.
Proof.
intros ly S W m m' c O mx no cap out ev
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
   H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) HK HOB VE WE Hev.
assert (KC : forall a n, In (a, a + n) (aout_fp B RG cap out) -> forall x, a <= x < a + n ->
  ~ (as_errno B <= x < as_errno B + 4) -> abyte_kept W m W m' x)
  by (intros a n Hin x Hx Hne; exact (HK (a, a + n) Hin x Hx Hne)).
unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_max RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H1]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_max RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H2]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_nout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H3]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_nout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H4]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_capout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H5]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_capout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H6]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_out RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H7]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_out RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H8]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_client RG) 4); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H9]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_client RG) 4); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H10]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_client_broken RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H11]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_client_broken RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H12]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_dead RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H13]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_dead RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H14]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_eintr RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H15]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_eintr RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H16]|].
split; [exact VE|]. split; [exact WE|]. split; [exact Hev|].
do 6 (split; [assumption|]).
destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin|].
exists junk. split; [exact Hj|].
apply (akept_garr8 W m); [|exact Hg].
intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
apply (KC out cap); [unfold aout_fp; rewrite Ec; repeat (first [left; reflexivity | right]) | lia | apply (HOB ltac:(lia)); lia].
Qed.

Lemma dperm_mv : forall (x : Z * Z) l1 l2 l3 r, Permutation (x :: l1 ++ l2 ++ l3 ++ r) (l1 ++ l2 ++ l3 ++ x :: r).
Proof. intros. rewrite !app_assoc. apply Permutation_middle. Qed.

Lemma dend_post : forall cx s1 D ly1 S1 W1 m' md' k1 regs' e1 e' h1 out1 ev' LB1 spent jb a tl,
DBASE B MT MMAX RG cx ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m' md' k1 ->
aregs_preserved (dxregs cx) regs' ->
apres_kept B (dxW cx) (dxmem cx) W1 m' ->
e' = dset_eof e1 (if hs_closed h1 =? 1 then 1 else re_eof e1) ->
garr8 SEGS (arm W1 m') (dxSA cx) (bzs (entry_bytes e')) -> awr W1 m' (dxSA cx) AENT ->
aentry_ok B ly1 S1 W1 m' e' ->
asrc_at B ly1 S1 W1 m' (dHA RG cx) h1 ->
(forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= x < dHA RG cx + ASRC) ->
   abyte_kept (dxW cx) (dxmem cx) W1 m' x) ->
aout_at B RG ly1 S1 W1 m' (dctl cx (Z.of_nat (length (with_nul (lines (dSTR cx) D)))) ev')
  (if dlive cx then dxO cx ++ LB1 else dxO cx) (dxmx cx)
  (if dlive cx then drain_b_c.ds_no s1 else dxno cx) (drain_b_c.ds_ocap s1) out1 ->
(dlive cx = false -> out1 = dxout cx /\ drain_b_c.ds_ocap s1 = dxcap cx) ->
Permutation (ablocks B ly1 S1)
  ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) ->
DLINK s1 e1 h1 -> DSAME cx e1 h1 -> DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 ->
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) ->
drain_b_c.ds_pend s1 = [] -> drain_b_c.ds_eintr s1 = false -> 4096 <= drain_b_c.ds_cap s1 - ulen s1 ->
dlater cx s1 jb a tl -> dbud MT MMAX cx S1 spent tl ->
dPOST B MT RG cx W1 (mkCfg (mkst regs' (getr (dxregs cx) 1) m' (seg_rom SEGS)) md').
Proof.
intros cx s1 D ly1 S1 W1 m' md' k1 regs' e1 e' h1 out1 ev' LB1 spent jb a tl HB HJ HRP HAPK He' HEB HEW HEOK
  HSRC HGK HOUT HDEAD HPERM HDL HDS HDH HJ1 HPE HEIN HROOM HLAT HBUD.
destruct HLAT as (fuel & Hn & Hwf & Ht & Hf).
destruct fuel as [|f]; [unfold dneed in Hn; lia|].
rewrite (drun_end f (dlive cx) (dxmx cx) s1 jb a HROOM HEIN HPE) in Ht, Hf. cbn [fst snd] in Ht, Hf. subst tl.
pose proof HDH as (HPS & HREF & HEXP & HFST & HCAP & HNO & HLB & HND & HSS & _ & _).
assert (HD : D = dPS cx) by (rewrite HPS; unfold pstream, prest; rewrite HPE; symmetry; apply app_nil_r).
subst D.
pose proof HDL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & _).
pose proof HDS as (S1' & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
pose proof HBUD as (Bmo & Bsp & Bcost & _ & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPB & _).
pose proof HSRC as (_ & _ & _ & _ & _ & Hcl01 & _ & _ & _ & _ & _ & _ & _ & _ & Hoff & _ & Hov01 & _).
assert (HCAPX : (if dlive cx then drain_b_c.ds_ocap s1 else dxcap cx) = drain_b_c.ds_ocap s1)
  by (revert HDEAD; destruct (dlive cx); intros HDEAD; [reflexivity | symmetry; exact (proj2 (HDEAD eq_refl))]).
assert (HNOX : (if dlive cx then drain_b_c.ds_no s1 else dxno cx) =
  (if dlive cx then dxno cx + dr_tot (dxh cx) else dxno cx))
  by (destruct (dlive cx); [exact HNO | reflexivity]).
assert (HRECS : hl_recs (hs_pending h1) = []) by (rewrite HPE in L7; exact (map_eq_nil _ _ L7)).
subst e'.
unfold dPOST, dr_post.
exists ly1, S1, regs', m', md', k1, (dset_eof e1 (if hs_closed h1 =? 1 then 1 else re_eof e1)), h1, out1, ev', LB1,
  ((dxG cx, ATABLE) :: dxrest cx).
cbv zeta.
change (dr_fin (dxc cx) (dxmx cx) (dxno cx) (dxcap cx) (dxe cx) (dxh cx)) with (dfin cx).
change (dr_live (dxc cx) (dxh cx)) with (dlive cx).
rewrite <- Hf, HCAPX.
split; [reflexivity|].
split; [exact HJ|].
split; [exact HRP|].
split; [exact HAPK|].
split.
{ change (dr_cost MT (dxc cx) (dxmx cx) (dxno cx) (dxcap cx) (dxe cx) (dxh cx)) with (dcost MT cx).
  apply (mle_weaken MT _ _ spent _ MTL Bmo). unfold tr_cost in Bcost. cbn [fold_right] in Bcost. lia. }
split; [exact (Permutation_trans HPB (dperm_mv _ _ _ _ _))|].
split; [exact (Permutation_trans HPERM (dperm_mv _ _ _ _ _))|].
split; [exact HEB|]. split; [exact HEW|]. split; [exact HEOK|].
cbn [dset_eof re_fd re_eof re_cap re_U re_skip re_keys re_hp re_kh].
split; [exact S1'|].
split; [rewrite S5, S2; reflexivity|].
split; [rewrite L1; unfold ulen in HROOM; lia|].
split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|].
split; [exact L5|].
split; [exact S10|].
split; [rewrite L4; exact HND|].
split; [rewrite L4; exact HSS|].
split; [exact HSRC|].
split; [exact HGK|].
split; [exact L11|].
split; [exact HCAP|].
split; [exact S3|]. split; [exact S5|].
split; [rewrite L6, HEIN; reflexivity|].
split; [exact HRECS|].
split; [destruct Hoff as [(_ & Ho) | (r & rs & Hr & _)]; [exact Ho | rewrite HRECS in Hr; discriminate]|].
split; [exact S6|]. split; [exact S7|]. split; [exact S8|].
split; [rewrite L9, HREF; reflexivity|].
split; [exact HEXP|].
split; [exact HFST|].
split; [exact S9|].
split.
{ rewrite L3. destruct HJ1 as (JK & _). rewrite JK, <- L9. unfold hs_state. cbn [ls_k].
  destruct Hov01 as [-> | ->]; reflexivity. }
split.
{ intros H0. rewrite L2. destruct HJ1 as (JK & JW & _).
  assert (Hs : drain_b_c.ds_skip s1 = false)
    by (rewrite L3 in H0; destruct (drain_b_c.ds_skip s1); [discriminate | reflexivity]).
  rewrite (JW Hs), <- L9. reflexivity. }
split; [exact HLB|].
rewrite HNOX in HOUT. exact HOUT.
Qed.

(* ---- END: DEND 0x83bbc -> h->closed ? (s->eof = 1 at 0x83b64) : (errno = EAGAIN at 0x83b44), then dr_epi. ---- *)
Theorem dr_end : dr_end_stmt B MT MMAX RG.
Proof.
intros HEPI cx s1 D W1 c1 HB HDE.
destruct HDE as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & tl &
  -> & Hsp & H3 & H4 & R22 & R18 & R21 & R23 & R24 & HFRM & HDM & HNZ & HUS & HDL & HDS & HDH & HJ1 & HPE & HEIN &
  HROOM & HLAT & HBUD).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HDM as (HJ & HROM & HAPK & HFRS & _ & HEB & HEW & HEX & HSRC & HOTH & HGK & HOUT & HDEAD & HPERM).
pose proof HB as (HPRE0 & _ & _ & HGle & HSAle & _ & _ & _ & Hj & _).
pose proof HPRE0 as (_ & Hra & _).
pose proof HFRM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSV).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
assert (HGin : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi, Hstk0.
assert (HDS0 : DRAIN_STK = 16848) by reflexivity.
assert (RQT : req_size ATABLE = 896) by reflexivity.
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR HGin) as (_ & HG4 & HGc & _).
rewrite RQT in HGc.
assert (HERRI : 0x10000 <= as_errno B /\ as_errno B + 4 <= 0x5fb000).
{ assert (HI4 : forall i, 0 <= i < 4 -> in_img SEGS (as_errno B + i)).
  { intros i Hi. apply (proj1 (HG (as_errno B + i) ltac:(unfold G_DR, G_SL, inG; cbn [In];
      repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))). }
  pose proof (pa_img_range _ (HI4 0 ltac:(lia))) as P0. pose proof (pa_img_range _ (HI4 3 ltac:(lia))) as P3. lia. }
assert (TBE : forall x, dxSA cx <= x < dxSA cx + AENT -> ~ (as_errno B <= x < as_errno B + 4)).
{ intros x Hx He. apply (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE x HAR HGin);
    [rewrite RQT; unfold AENT, ATABLE in *; lia|].
  apply (proj1 (HG x ltac:(unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))). }
assert (HEOK : aentry_ok B ly1 S1 W1 m1 e1).
{ destruct HEX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & _ & X9 & X10 & X11 & X12 & X13 & X14).
  exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 (conj HUS (conj HNZ
    (conj X9 (conj X10 (conj X11 (conj X12 (conj X13 X14)))))))))))))). }
pose proof HEOK as (_ & _ & Hp1 & Hp2 & _).
pose proof HSRC as (_ & _ & Vcl & _ & _ & Hcl01 & _).
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAWE & _).
set (L := aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) in HPERM.
assert (INL : forall b, In b L -> In b (ablocks B ly1 S1))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; exact Hb).
assert (FE : forall r, In r (aentry_fp e1) -> forall x, fst r <= x < snd r ->
  dlow cx x /\ ~ (as_errno B <= x < as_errno B + 4)).
{ apply (dend_fp_entry cx ly1 S1 W1 m1 md1 e1 L HAR HPERM); [|exact HEOK].
  intros b Hb. unfold L. apply in_or_app. left. exact Hb. }
assert (FS : forall r, In r (asrc_fp (dHA RG cx) h1) -> forall x, fst r <= x < snd r ->
  dlow cx x /\ ~ (as_errno B <= x < as_errno B + 4)).
{ apply (dend_fp_src cx ly1 S1 W1 m1 md1 L h1 HAR HPERM); [| exact HGin | exact Hj | exact HSRC].
  intros b Hb. unfold L. apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (FO : forall r, In r (aout_fp B RG (drain_b_c.ds_ocap s1) out1) -> forall x, fst r <= x < snd r ->
  dlow cx x /\ (r <> (as_errno B, as_errno B + 4) -> ~ (as_errno B <= x < as_errno B + 4))).
{ eapply (dend_fp_out cx ly1 S1 W1 m1 md1 _ _ _ _ _ _ L HAR HPERM); [| exact HOUT].
  intros b Hb. unfold L. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (FB : drain_b_c.ds_ocap s1 <> 0 -> forall x, out1 <= x < out1 + drain_b_c.ds_ocap s1 ->
  ~ (as_errno B <= x < as_errno B + 4)).
{ intros Hc x Hx. pose proof (req_size_pos (drain_b_c.ds_ocap s1)) as Hrq.
  pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
  destruct Hblk as [(Hc0 & _) | (Hcp & _ & _)]; [lia|].
  destruct (Hrq ltac:(lia)) as (_ & Hrq').
  refine (proj2 (dend_low_blk cx ly1 S1 W1 m1 md1 L out1 (drain_b_c.ds_ocap s1) x HAR HPERM _ ltac:(lia))).
  unfold L. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
  unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity. }
assert (FG : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> dlow cx x /\ ~ (as_errno B <= x < as_errno B + 4))
  by (intros x Hx; exact (dend_gs_ok cx ly1 S1 W1 m1 md1 x HAR HGin Hx)).
destruct Hcl01 as [Hc0 | Hc1].
- apply (dend_eagain cx ly1 S1 W1 m1 md1 k1 regs1 _ HB HJ HGin HAWE Hsp H3 H4 R22 R18 R21 R23 R24
    ltac:(rewrite <- Hc0; exact Vcl)).
  intros regsF mF mdF F2 F3 F4 HJF KV PR VE.
  apply (HEPI cx ly1 S1 W1 mF mdF k1 regsF (dPOST B MT RG cx) HJF).
  + unfold spZ in *. rewrite F2. exact Hsp.
  + rewrite F3. exact H3.
  + rewrite F4. exact H4.
  + exact Hra.
  + intros i Hi. eapply val_mem_kept; [|exact (HSV i Hi)]. intros k Hk.
    apply KV; unfold DRAIN_FRAME, ESTACK in *; lia.
  + intros regs' m' md' HRP Harm HJ'.
    set (P := fun x => as_errno B <= x < as_errno B + 4 \/ dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME).
    assert (KVP : forall x, 0 <= x < 2 ^ 64 -> ~ P x -> aview SEGS (w_H W1) m' x = aview SEGS (w_H W1) m1 x).
    { intros x Hx HP. rewrite (aview_eq_of SEGS _ mF m' x (Harm _)).
      apply KV; [exact Hx | intros H; apply HP; left; exact H | intros H; apply HP; right; exact H]. }
    assert (PR' : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m' x).
    { intros x Hp. destruct (PR x Hp) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
      specialize (Harm (Z_to_bv 64 x)). unfold arm, mrestrict in Harm. rewrite Hh in Harm. rewrite Harm. exact Hb. }
    assert (VE' : val_mem SEGS (arm W1 m') (as_errno B) 4 11).
    { eapply val_mem_kept; [|exact VE]. intros k Hk. apply aview_eq_of. apply Harm. }
    assert (BK : forall x, 0 <= x < alloc_ceiling -> ~ (as_errno B <= x < as_errno B + 4) ->
      abyte_kept W1 m1 W1 m' x).
    { intros x Hx Hne. apply (dend_bk W1 m1 m' P x KVP PR'); [lia|].
      intros [H | H]; [exact (Hne H) | unfold DRAIN_FRAME, ESTACK in *; lia]. }
    apply (dend_post cx s1 D ly1 S1 W1 m' md' k1 regs' e1 e1 h1 out1 11 LB1 spent jb a tl HB HJ' HRP).
    * intros x Hi Hno He Hp. apply PR'. exact (HAPK x Hi Hno He Hp).
    * rewrite Hc0. change (0 =? 1) with false. cbv iota. symmetry. apply dset_eof_id.
    * apply (akept_garr8 W1 m1); [|exact HEB]. intros x Hx. unfold bzs in Hx.
      rewrite length_map in Hx. apply BK; [| apply TBE]; unfold AENT, ATABLE in *;
      unfold entry_bytes, re_nheld in Hx; rewrite !length_app, !Mem.length_le4, !Mem.length_le8, Hp1, Hp2 in Hx; lia.
    * intros i Hi. unfold arm. apply (writable_kept (w_H W1) m1 m'); [apply PR' | exact (HEW i Hi)].
    * apply (aentry_ok_kept B ly1 S1 W1 m1 ly1 S1 W1 m' e1 HEOK);
        [|intros b Hb; apply INL; unfold L; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (FE r Hr x Hx) as [[Hl _] Hne]. exact (BK x Hl Hne).
    * apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m' (dHA RG cx) h1 HSRC);
        [|intros b Hb; apply INL; unfold L; apply in_or_app; right; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (FS r Hr x Hx) as [[Hl _] Hne]. exact (BK x Hl Hne).
    * intros x Hx Hn. pose proof (HGK x Hx Hn) as K1. destruct (FG x Hx) as [[Hl _] Hne].
      pose proof (BK x Hl Hne) as K2. split; [rewrite (proj1 K2); exact (proj1 K1)|].
      intros Hw. apply (proj2 K2). apply (proj2 K1). exact Hw.
    * apply (dend_aout_ev ly1 S1 W1 m1 m' _ _ _ _ _ _ 11 HOUT).
      -- intros r Hr x Hx Hne. destruct (FO r Hr x Hx) as [[Hl _] _]. exact (BK x Hl Hne).
      -- exact FB.
      -- exact VE'.
      -- intros i Hi. unfold arm. apply (writable_kept (w_H W1) m1 m'); [apply PR' | exact (HAWE i Hi)].
      -- lia.
    * exact HDEAD.
    * exact HPERM.
    * exact HDL.
    * exact HDS.
    * exact HDH.
    * exact HJ1.
    * exact HPE.
    * exact HEIN.
    * exact HROOM.
    * exact HLAT.
    * exact HBUD.
- apply (dend_closed cx ly1 S1 W1 m1 md1 k1 regs1 _ HB HJ HGin HEW R22 R18 R21 R23 R24
    ltac:(rewrite <- Hc1; exact Vcl)).
  intros regsF mF mdF F2 F3 F4 HJF KV PR VE.
  apply (HEPI cx ly1 S1 W1 mF mdF k1 regsF (dPOST B MT RG cx) HJF).
  + unfold spZ in *. rewrite F2. exact Hsp.
  + rewrite F3. exact H3.
  + rewrite F4. exact H4.
  + exact Hra.
  + intros i Hi. eapply val_mem_kept; [|exact (HSV i Hi)]. intros k Hk.
    apply KV; unfold DRAIN_FRAME, AENT, ATABLE in *; lia.
  + intros regs' m' md' HRP Harm HJ'.
    set (P := fun x => dxSA cx + 4 <= x < dxSA cx + 8).
    assert (KVP : forall x, 0 <= x < 2 ^ 64 -> ~ P x -> aview SEGS (w_H W1) m' x = aview SEGS (w_H W1) m1 x).
    { intros x Hx HP. rewrite (aview_eq_of SEGS _ mF m' x (Harm _)). exact (KV x Hx HP). }
    assert (PR' : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m' x).
    { intros x Hp. destruct (PR x Hp) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
      specialize (Harm (Z_to_bv 64 x)). unfold arm, mrestrict in Harm. rewrite Hh in Harm. rewrite Harm. exact Hb. }
    assert (VE' : val_mem SEGS (arm W1 m') (dxSA cx + 4) 4 1).
    { eapply val_mem_kept; [|exact VE]. intros k Hk. apply aview_eq_of. apply Harm. }
    assert (BK : forall x, dlow cx x -> abyte_kept W1 m1 W1 m' x).
    { intros x [Hx Hnt]. apply (dend_bk W1 m1 m' P x KVP PR'); [lia|].
      intros H. apply Hnt. unfold P, AENT, ATABLE in *. lia. }
    apply (dend_post cx s1 D ly1 S1 W1 m' md' k1 regs' e1 (dset_eof e1 1) h1 out1 ev1 LB1 spent jb a tl HB HJ' HRP).
    * intros x Hi Hno He Hp. apply PR'. exact (HAPK x Hi Hno He Hp).
    * rewrite Hc1. reflexivity.
    * apply (dend_garr8_eof W1 m1 m' (dxSA cx) e1 HEB); [| exact Hp1 | exact Hp2 | exact VE'].
      intros x Hx Hn. apply KVP; [unfold AENT, ATABLE in *; lia | exact Hn].
    * intros i Hi. unfold arm. apply (writable_kept (w_H W1) m1 m'); [apply PR' | exact (HEW i Hi)].
    * apply dend_aentry_eof; [|right; reflexivity].
      apply (aentry_ok_kept B ly1 S1 W1 m1 ly1 S1 W1 m' e1 HEOK);
        [|intros b Hb; apply INL; unfold L; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (FE r Hr x Hx) as [Hl _]. exact (BK x Hl).
    * apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m' (dHA RG cx) h1 HSRC);
        [|intros b Hb; apply INL; unfold L; apply in_or_app; right; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (FS r Hr x Hx) as [Hl _]. exact (BK x Hl).
    * intros x Hx Hn. pose proof (HGK x Hx Hn) as K1. destruct (FG x Hx) as [Hl _].
      pose proof (BK x Hl) as K2. split; [rewrite (proj1 K2); exact (proj1 K1)|].
      intros Hw. apply (proj2 K2). apply (proj2 K1). exact Hw.
    * apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m' _ _ _ _ _ _ HOUT);
        [|intros b Hb; apply INL; unfold L; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (FO r Hr x Hx) as [Hl _]. exact (BK x Hl).
    * exact HDEAD.
    * exact HPERM.
    * exact HDL.
    * exact HDS.
    * exact HDH.
    * exact HJ1.
    * exact HPE.
    * exact HEIN.
    * exact HROOM.
    * exact HLAT.
    * exact HBUD.
Qed.

End c.

(* ---- THE GENERIC WALK (route (b), step 3): the epilogue (dr_epi_stmt_x) and the end (dr_end_stmt_x) over any
   allocator relation ARx with its laws, at the room texts (the room record RP, the entry's budget kr).  The Section is W_drain_cx_x.v's Section c - its variables
   B PST ARx MT RP MMAX RG in that order, each hypothesis that file's text - with the three allocator rules in their
   caller-context forms (W_journal_x.v Section hc, one context table per allocator entry; these segments call no
   allocator, so no call-site fact HCTX_* is stated), and after LAWS the generic-relation facts the walk reads:
     HP0 (no hidden head in any ARx state, a Theorem Labs lane's ruling: the table's shadow facts are W_journal_x.v's
     range_addressable_of_block_hp0_x).  An image byte lies in no live block (YCbqG.v blk_img_x, the laws'
     client-image field): the image's cells (g_s, G_DR, HGO's three) are apart from the table without a numeric image
     band.  The room: dr_post_x's rp_RM RP S' kr is the cut's room (dbud_x) with the requests' count dropped (RMM).
   The AR walk above (Section c) is unchanged.  Its Definitions are cited; its lemmas are restated here with an _x
   suffix (each over ARx where it reads the relation), so no lemma's Section generalization is relied on. ---- *)
Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes_x B ARx (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM_x SEGS B ARx 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes_x B ARx (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes_x B ARx (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_S (SIGMA WS_strndup).
Hypothesis ALLOC_TAIL : forall ly S Hp W mem md p n a,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_list_push).
Hypothesis RMM : forall S k k', (k' <= k)%nat -> rp_RM RP S k -> rp_RM RP S k'.
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 22) = rg_s RG.
Hypothesis HLIT5 : dlit_at_x ARx 21 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at_x ARx 23 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at_x ARx 24 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 21), VAL (A_OBJ 21) + 14); (VAL (A_OBJ 23), VAL (A_OBJ 23) + 6); (VAL (A_OBJ 24), VAL (A_OBJ 24) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Let RUN := paj_run_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---- EPI: the epilogue 0x83b80 (ld ra/s0..s11, addi sp,sp,336, ret).  It writes nothing: the caller's
   continuation gets the same restricted memory and the same journal.  This copies W_send_line_cx.v sl_epi,
   with the drain frame (336) and the saved-register slots (232(sp) .. 328(sp)). ---- *)
Lemma nth_depi_extra_x : forall regsE i, (i < 13)%nat ->
  nth i (depi_extra regsE) (Z_to_bv 64 0) = getr regsE (nth i DR_SAVED 0%bv).
Proof.
intros regsE i Hi. unfold depi_extra. rewrite app_nth1 by (rewrite length_map; cbn; lia).
rewrite (nth_indep _ _ (getr regsE 0%bv)) by (rewrite length_map; cbn; lia). rewrite List.map_nth. reflexivity.
Qed.
Lemma dr_epi_entry_x : forall W regsX memX regsE,
alloc_ceiling <= spZ regsX -> spZ regsX + DRAIN_FRAME <= 2 ^ 47 -> 2 ^ 46 <= spZ regsX -> spZ regsX mod 16 = 0 ->
dr_saved W memX (spZ regsX) regsE ->
st_ok_pi SEGS VAL (Eimg (Ereg regsX (depi_extra regsE))) dss_epi
(restrict (w_H W) (mkst regsX (Z_to_bv 64 (BASE + A_dr_epi)) memX (seg_rom SEGS))).
Proof.
intros W regsX memX regsE Hceil Htop Hlo Hal HSV.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsX (depi_extra regsE))).
assert (E2 : ew E 2 = getr regsX 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsX _ 2 2%bv eq_refl)).
assert (E45 : ew E 45 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsX _ 13)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsX) by (rewrite E2; reflexivity).
unfold dss_epi, A_dr_epi. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold depi_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_map. apply Forall_forall. intros i Hi. apply in_seq in Hi. cbn [Nat.add] in Hi.
  apply (chunk_ok_val SEGS E _ (spZ regsX) (232 + 8 * Z.of_nat i) 8 _ (bv_unsigned (getr regsE (nth i DR_SAVED 0%bv)))).
  + cbn [sv_denot]. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite ew_Ereg_extra, nth_depi_extra_x by lia.
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + pose proof (bv_unsigned_in_range 64 (getr regsE (nth i DR_SAVED 0%bv))) as R. change (bv_modulus 64) with (2 ^ 64) in R. zside.
  + zside.
  + replace (spZ regsX + (232 + 8 * Z.of_nat i)) with (spZ regsX + 232 + 8 * Z.of_nat i) by lia. exact (HSV i ltac:(lia)).
- cbn [pairwise_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [depi_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E45, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold DRAIN_FRAME in Htop. revert Hceil Htop Hlo Hal. clear. unfold SB. intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia).
Qed.


Lemma dend_entry_x : forall (W : world SEGS) regs m (j : nat) cl SA,
(j < 4)%nat ->
getr regs 18 = w64 (rg_s RG) -> getr regs 21 = w64 SHADOW_OFF -> getr regs 22 = w64 SA ->
getr regs 23 = w64 (rg_s RG + ASRC * Z.of_nat j) -> getr regs 24 = w64 (SHADOW_OFF + 12 * Z.of_nat j) ->
4096 <= SA <= 0x7fffff800000 ->
val_mem SEGS (arm W m) (rg_s RG + ASRC * Z.of_nat j + 8) 4 cl -> 0 <= cl <= 1 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (dss_end j cl)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_end)) m (seg_rom SEGS))).
Proof.
intros W regs m j cl SA Hj R18 R21 R22 R23 R24 HSA Hcl Rcl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof HGSB as (G1 & G2 & G3).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs [])).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ n r Hr)).
assert (U18 : bv_unsigned (ew E 18) = rg_s RG)
  by (rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); rewrite R18; apply unsigned_lit_small; unfold ASRC in *; lia).
assert (U21 : bv_unsigned (ew E 21) = SB)
  by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); rewrite R21, unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity).
assert (U22 : bv_unsigned (ew E 22) = SA)
  by (rewrite (EREG 22%nat 22%bv) by (first [lia | reflexivity]); rewrite R22; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = rg_s RG + ASRC * Z.of_nat j)
  by (rewrite (EREG 23%nat 23%bv) by (first [lia | reflexivity]); rewrite R23; apply unsigned_lit_small; unfold ASRC in *; lia).
assert (U24 : bv_unsigned (ew E 24) = SB + 12 * Z.of_nat j)
  by (rewrite (EREG 24%nat 24%bv) by (first [lia | reflexivity]); rewrite R24, unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold dend_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U23.
  split; [unfold ASRC in *; lia|]. split; [unfold ASRC in *; lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ _ 8 4 (SLit cl) cl); [reflexivity | cbn; lia | cbn; lia | exact Hcl].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [dend_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U18, U21, U22, U24. unfold SB, ASRC in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity
    | change (2 ^ 3) with 8; lia].
Qed.

Lemma dend_shent1_x : forall ly S Hp (W : world SEGS) mem md E (j : nat),
ARx ly S Hp W mem md -> (j < 4)%nat ->
U E dBx1 = SHADOW_OFF + 12 * Z.of_nat j -> U E (SOff 18 0) = rg_s RG ->
shent_ok SEGS dBx1 E (mrestrict (w_H W) mem) (mkSHE 18 0 96).
Proof.
intros ly S Hp W mem md E j HAR Hj HB Hm.
pose proof HGSB as (G1 & G2 & G3).
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. rewrite <- (aview_rd_of SEGS).
pose proof (azs_range_addressable_x B ARx LAWS ly S Hp W mem md (rg_s RG) (4 * ASRC) HAR HGSZ) as HRA.
split.
- intros x Hx. destruct (HRA (x + ASRC * Z.of_nat j) ltac:(unfold ASRC in *; lia)) as (s & Hs & Hok).
  exists s. split.
  + unfold shadow_of_addr in *. replace (SHADOW_OFF + 12 * Z.of_nat j + x / 8)
      with (SHADOW_OFF + (x + ASRC * Z.of_nat j) / 8); [exact Hs|].
    unfold ASRC. replace (x + 96 * Z.of_nat j) with (x + (12 * Z.of_nat j) * 8) by lia.
    rewrite Z.div_add by lia. lia.
  + unfold saddr_ok in *. unfold ASRC in Hok.
    replace ((x + 96 * Z.of_nat j) mod 8) with (x mod 8) in Hok; [exact Hok|].
    replace (x + 96 * Z.of_nat j) with (x + (12 * Z.of_nat j) * 8) by lia. rewrite Z.mod_add by lia. reflexivity.
- intros a Ha. unfold SHADOW_OFF, ASRC in *. lia.
Qed.



Lemma dset_eof_id_x : forall e, dset_eof e (re_eof e) = e.
Proof. intros []. reflexivity. Qed.

Lemma dend_aentry_eof_x : forall ly S (W : world SEGS) m e v,
aentry_ok B ly S W m e -> v = 0 \/ v = 1 -> aentry_ok B ly S W m (dset_eof e v).
Proof. intros ly S W m e v (_ & H) Hv. split; [exact Hv | exact H]. Qed.

Lemma dend_garr8_one4_x : forall m a, val_mem SEGS m a 4 1 -> garr8 SEGS m a [1; 0; 0; 0].
Proof.
intros m a H j Hj. cbn [length] in Hj.
split; [|destruct j as [|[|[|[|j]]]]; cbn; lia].
intros k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
rewrite (H j Hj). f_equal. destruct j as [|[|[|[|j]]]]; try (vm_compute; reflexivity). lia.
Qed.

Lemma dend_garr8_eof_x : forall (W : world SEGS) m m' SA e,
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
(forall x, SA <= x < SA + AENT -> ~ (SA + 4 <= x < SA + 8) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
val_mem SEGS (arm W m') (SA + 4) 4 1 ->
garr8 SEGS (arm W m') SA (bzs (entry_bytes (dset_eof e 1))).
Proof.
intros W m m' SA e HE0 KV Hp1 Hp2 VM.
unfold entry_bytes, dset_eof, re_nheld in HE0 |- *.
cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk] in HE0 |- *.
unfold bzs in HE0 |- *. rewrite !map_app in HE0 |- *.
apply (garr8_app SEGS) in HE0 as [HA HE0]. apply (garr8_app SEGS) in HE0 as [_ HC].
apply (garr8_app SEGS). split.
- eapply (garr8_frame SEGS); [exact HA|]. intros x Hx. unfold arm. apply (mbyte_of_aview SEGS).
  rewrite length_map, Mem.length_le4 in Hx. apply KV; unfold AENT; lia.
- apply (garr8_app SEGS). rewrite !length_map, !Mem.length_le4 in HC |- *. split.
  + lazymatch goal with |- garr8 _ _ _ (map bz ?l) => replace (map bz l) with [1; 0; 0; 0] by (vm_compute; reflexivity) end.
    apply dend_garr8_one4_x. replace (SA + Z.of_nat 4) with (SA + 4) by lia. exact VM.
  + eapply (garr8_frame SEGS); [exact HC|]. intros x Hx. unfold arm. apply (mbyte_of_aview SEGS).
    rewrite !length_app, !length_map, !Mem.length_le4, !Mem.length_le8, Hp1, Hp2 in Hx.
    apply KV; unfold AENT; lia.
Qed.

Lemma dend_bk_x : forall (W : world SEGS) m m' (P : Z -> Prop) a,
(forall x, 0 <= x < 2 ^ 64 -> ~ P x -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
(forall x, apresent (w_H W) m x -> apresent (w_H W) m' x) ->
0 <= a < 2 ^ 64 -> ~ P a -> abyte_kept W m W m' a.
Proof.
intros W m m' P a KV PR Ha HP. split; [exact (KV a Ha HP)|].
unfold arm. apply writable_kept. apply PR.
Qed.

Lemma dend_zall_x : forall a l j d, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l d).
Proof.
intros a l. induction l as [|b l IH]; intros j d H Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma dend_zpw_x : forall l i j d, zpairwise_disjoint l -> (i < j)%nat -> (j < length l)%nat ->
zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|a l IH]; intros i j d H Hij Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct i as [|i].
- destruct j as [|j]; [lia|]. cbn [nth]. apply dend_zall_x; [exact H1 | lia].
- destruct j as [|j]; [lia|]. cbn [nth]. apply IH; [exact H2 | lia | lia].
Qed.

Lemma dend_errno_sep_x : forall a,
(rg_s RG <= a < rg_s RG + 4 * ASRC \/ rg_client RG <= a < rg_client RG + 4 \/
 rg_client_broken RG <= a < rg_client_broken RG + 1 \/ rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/
 rg_send_dead RG <= a < rg_send_dead RG + 1 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_nout RG <= a < rg_nout RG + 8 \/ rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8) ->
~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha He.
pose proof (dend_zpw_x _ 2 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D2.
pose proof (dend_zpw_x _ 3 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D3.
pose proof (dend_zpw_x _ 4 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D4.
pose proof (dend_zpw_x _ 5 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D5.
pose proof (dend_zpw_x _ 6 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D6.
pose proof (dend_zpw_x _ 7 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D7.
pose proof (dend_zpw_x _ 8 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D8.
pose proof (dend_zpw_x _ 9 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D9.
pose proof (dend_zpw_x _ 10 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D10.
cbn [nth] in D2, D3, D4, D5, D6, D7, D8, D9, D10. unfold zdisj in *. cbn [fst snd] in *. lia.
Qed.

(* an image byte is no byte of the table block (YCbqG.v blk_img_x, the laws' client-image field) *)
Lemma dend_low_img_x : forall cx ly S Hp (W : world SEGS) mem md a,
ARx ly S Hp W mem md -> In (dxG cx, ATABLE) (ablocks B ly S) -> in_img SEGS a -> dlow cx a.
Proof.
intros cx ly S Hp W mem md a HAR Hin Ha.
pose proof (pa_img_range a Ha) as Hr.
pose proof asan_consts as (C1 & _).
assert (NT : ~ (dxG cx <= a < dxG cx + req_size ATABLE))
  by (intros Ht; exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ a HAR Hin Ht Ha)).
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in NT.
unfold dlow, ATABLE in *. lia.
Qed.

Lemma dend_low_blk_x : forall cx ly S Hp (W : world SEGS) mem md L p n a,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
In (p, n) L -> p <= a < p + req_size n ->
dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S Hp W mem md L p n a HAR HP HL Ha.
assert (Hin : In (p, n) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); right; exact HL).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (_ & H4 & Hc & _).
destruct (in_split _ _ HL) as (l1 & l2 & ->).
assert (HP2 : Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: (p, n) :: l1 ++ l2))
  by (eapply Permutation_trans; [exact HP | apply perm_skip; apply Permutation_sym, Permutation_middle]).
pose proof (sep_blocks_perm_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ HAR HP2) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in Hd.
split; [unfold dlow, ATABLE; lia|].
intros He. apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md p n a HAR Hin ltac:(lia)).
apply (proj1 (HG a ltac:(unfold G_DR, G_SL, inG; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))).
Qed.

Lemma dend_gs_ok_x : forall cx ly S Hp (W : world SEGS) mem md a,
ARx ly S Hp W mem md -> In (dxG cx, ATABLE) (ablocks B ly S) -> rg_s RG <= a < rg_s RG + 4 * ASRC ->
dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S Hp W mem md a HAR Hin Ha. pose proof HGSB as (G1 & G2 & _).
split; [apply (dend_low_img_x cx ly S Hp W mem md a HAR Hin); refine (proj1 (HG a _)); unfold inG, G_DR;
  apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Ha|].
apply dend_errno_sep_x. left. exact Ha.
Qed.

Lemma dend_key_ptrs_len_x : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.

Lemma dend_recs_len_x : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Lemma dend_fp_entry_x : forall cx ly S Hp (W : world SEGS) mem md e L,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (aentry_blks e) -> In b L) -> aentry_ok B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S Hp W mem md e L HAR HP HB HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & _ & Hbuf & _ & Hhp & _ & _ & Hks).
assert (BLK : forall p n, In (p, n) (aentry_blks e) -> 0 <= n -> p <= a < p + n ->
  dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros p n Hin Hn Hpa. pose proof (req_size_pos n Hn) as (_ & Hrq).
  exact (dend_low_blk_x cx ly S Hp W mem md L p n a HAR HP (HB _ Hin) ltac:(lia)). }
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  apply (BLK (re_buf e) (re_cap e)); [| lia | lia].
  unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
- cbn [In] in Hr. destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. unfold bzs, key_ptrs in Ha. cbn [map concat length] in Ha. lia.
    * unfold bzs in Ha. rewrite length_map, dend_key_ptrs_len_x in Ha. unfold re_nheld in Hk1.
      apply (BLK (re_hp e) (re_kh e)); [| lia | lia].
      unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
      rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (BLK (key_addr k) (Z.of_nat (length (key_text k)) + 1)); [| lia | lia].
    unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
    apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
Qed.

Lemma dend_fp_list_x : forall cx ly S Hp (W : world SEGS) mem md L LA l lines,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (alist_blks l) -> In b L) -> In (dxG cx, ATABLE) (ablocks B ly S) ->
alist_at B ly S W mem LA l lines -> rg_s RG <= LA -> LA + 16 <= rg_s RG + 4 * ASRC ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S Hp W mem md L LA l lines HAR HP HB HGin HL Hlo Hhi r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
assert (BLK : forall p n, In (p, n) (alist_blks l) -> 0 <= n -> p <= a < p + n ->
  dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros p n Hin Hn0 Hpa. pose proof (req_size_pos n Hn0) as (_ & Hrq).
  exact (dend_low_blk_x cx ly S Hp W mem md L p n a HAR HP (HB _ Hin) ltac:(lia)). }
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (dend_gs_ok_x cx ly S Hp W mem md a HAR HGin). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, dend_recs_len_x in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (BLK (hl_v l) (AREC * hl_cap l)); [| unfold AREC; lia | unfold hl_n, AREC in *; lia].
    unfold alist_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (BLK (fst q) (Z.of_nat (length (snd q)) + 1)); [| lia | lia].
    unfold alist_blks. apply in_or_app. right.
    apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hq.
Qed.

Lemma dend_fp_src_x : forall cx ly S Hp (W : world SEGS) mem md L h,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (asrc_blks h) -> In b L) -> In (dxG cx, ATABLE) (ablocks B ly S) -> (dxj cx < 4)%nat ->
asrc_at B ly S W mem (dHA RG cx) h ->
forall r, In r (asrc_fp (dHA RG cx) h) -> forall a, fst r <= a < snd r ->
dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S Hp W mem md L h HAR HP HB HGin Hj HS r Hr a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (unfold dHA, ASRC; lia).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (dend_gs_ok_x cx ly S Hp W mem md a HAR HGin). lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq).
  apply (dend_low_blk_x cx ly S Hp W mem md L (hs_partial h) APARTIAL a HAR HP); [apply HB; left; reflexivity | lia].
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + exact (dend_fp_list_x cx ly S Hp W mem md L (dHA RG cx + 16) (hs_pending h) false HAR HP
      (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_introl Hb)))) HGin Hpend
      ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * exact (dend_fp_list_x cx ly S Hp W mem md L (dHA RG cx + 64) (hs_expected h) true HAR HP
        (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hb)))))) HGin Hexp
        ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
    * exact (dend_fp_list_x cx ly S Hp W mem md L (dHA RG cx + 80) (hs_held h) true HAR HP
        (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hb)))))) HGin Hheld
        ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
Qed.

Lemma dend_fp_out_x : forall cx ly S Hp (W : world SEGS) mem md c O mx no cap out L,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (aout_blks cap out) -> In b L) ->
aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
dlow cx a /\ (r <> (as_errno B, as_errno B + 4) -> ~ (as_errno B <= a < as_errno B + 4)).
Proof.
intros cx ly S Hp W mem md c O mx no cap out L HAR HP HB HOUT r Hr a Ha.
assert (GT : In (dxG cx, ATABLE) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
assert (IMG : forall x, in_img SEGS x -> dlow cx x)
  by (intros x Hx; exact (dend_low_img_x cx ly S Hp W mem md x HAR GT Hx)).
assert (GDR : forall x, inG (G_DR B RG) x -> in_img SEGS x) by (intros x Hx; exact (proj1 (HG x Hx))).
assert (GO : forall x, inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] x -> in_img SEGS x)
  by (intros x Hx; exact (proj1 (HGO x Hx))).
pose proof (pa_obj_img 9 ltac:(lia)) as P9. rewrite HV9 in P9.
pose proof (pa_obj_img 12 ltac:(lia)) as P12. rewrite HV12 in P12.
pose proof HSM as (Hs1 & Hs2).
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- split; [apply IMG, GO; unfold inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep_x; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep_x; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep_x; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep_x; tauto].
- split; [apply IMG, GO; unfold inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep_x; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep_x; tauto].
- split; [apply IMG, GO; unfold inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep_x; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep_x; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros Hne; exfalso; apply Hne; reflexivity].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq).
  destruct (dend_low_blk_x cx ly S Hp W mem md L out cap a HAR HP) as [D1 D2];
    [apply HB; unfold aout_blks; rewrite Hc0; left; reflexivity | lia |].
  split; [exact D1 | intros _; exact D2].
Qed.

Lemma dend_aout_ev_x : forall ly S (W : world SEGS) m m' c O mx no cap out ev,
aout_at B RG ly S W m c O mx no cap out ->
(forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
   ~ (as_errno B <= a < as_errno B + 4) -> abyte_kept W m W m' a) ->
(cap <> 0 -> forall a, out <= a < out + cap -> ~ (as_errno B <= a < as_errno B + 4)) ->
val_mem SEGS (arm W m') (as_errno B) 4 ev -> awr W m' (as_errno B) 4 -> 0 <= ev < 2 ^ 32 ->
aout_at B RG ly S W m' (CTL (ct_cl c) (ct_br c) (ct_dd c) (ct_ei c) ev) O mx no cap out.
Proof.
intros ly S W m m' c O mx no cap out ev
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
   H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) HK HOB VE WE Hev.
assert (KC : forall a n, In (a, a + n) (aout_fp B RG cap out) -> forall x, a <= x < a + n ->
  ~ (as_errno B <= x < as_errno B + 4) -> abyte_kept W m W m' x)
  by (intros a n Hin x Hx Hne; exact (HK (a, a + n) Hin x Hx Hne)).
unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_max RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H1]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_max RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H2]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_nout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H3]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_nout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H4]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_capout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H5]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_capout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H6]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_out RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H7]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_out RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H8]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_client RG) 4); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H9]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_client RG) 4); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H10]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_client_broken RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H11]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_client_broken RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H12]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_dead RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H13]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_dead RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H14]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_eintr RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H15]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_eintr RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H16]|].
split; [exact VE|]. split; [exact WE|]. split; [exact Hev|].
do 6 (split; [assumption|]).
destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin|].
exists junk. split; [exact Hj|].
apply (akept_garr8 W m); [|exact Hg].
intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
apply (KC out cap); [unfold aout_fp; rewrite Ec; repeat (first [left; reflexivity | right]) | lia | apply (HOB ltac:(lia)); lia].
Qed.

Lemma dperm_mv_x : forall (x : Z * Z) l1 l2 l3 r, Permutation (x :: l1 ++ l2 ++ l3 ++ r) (l1 ++ l2 ++ l3 ++ x :: r).
Proof. intros. rewrite !app_assoc. apply Permutation_middle. Qed.




(* ---- route R: the R twin of each piece of Section cx whose statement names the journal, SRr, a carrier or
   a statement: the strict text with the journal and SRr at R and each carrier / statement / engine lemma at its R
   twin (W_drain_cx_x.v Section wR). The strict lemmas above are unchanged. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Let RUNR := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).

Theorem dr_epi_xR : dr_epi_stmt_xR B PST ARx RG R.
Proof.
unfold dr_epi_stmt_xR. intros cx Hp ly1 S1 Hp1 W1 m1 md1 k1 regs1 Q HJ HspX H3 H4 HraE HSV HQ.
unfold cfg_at.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi, Hstk0.
assert (HDS : DRAIN_STK_x = 16976) by reflexivity.
pose proof (dr_epi_entry_x W1 regs1 m1 (dxregs cx) ltac:(unfold DRAIN_FRAME in *; lia) ltac:(unfold DRAIN_FRAME in *; lia)
  ltac:(unfold DRAIN_FRAME in *; lia) ltac:(unfold DRAIN_FRAME in *; rewrite HspX; rewrite Zminus_mod, Hal16; reflexivity)
  ltac:(rewrite HspX; exact HSV)) as HS.
remember (Eimg (Ereg regs1 (depi_extra (dxregs cx)))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EX : forall i, (i < 13)%nat -> ew E (32 + i) = getr (dxregs cx) (nth i DR_SAVED 0%bv)).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (nth_depi_extra_x (dxregs cx) i Hi). }
assert (E2 : ew E 2 = getr regs1 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs1 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs1 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 4 4%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs1) by (rewrite E2; reflexivity).
assert (SHOK : sh_ok SEGS dBxX [] E (mrestrict (w_H W1) m1)) by constructor.
clear HE.
paj_run_tok_xR RUNR HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19.
prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
apply (SRr_SRrG _ _ WLE_R); eapply (RET W1 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
assert (RA : getr (ms_regs ms) 1 = getr (dxregs cx) 1) by (rewrite R1; exact (EX 12%nat ltac:(lia))).
rewrite RA, HraE. apply HQ.
- intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R2, Usp, HspX. replace (dsp0 cx - DRAIN_FRAME + 336) with (dsp0 cx) by (unfold DRAIN_FRAME; lia).
    unfold dsp0, spZ. apply Z_to_bv_bv_unsigned.
  + replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R3, E3. exact H3.
  + replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R4, E4. exact H4.
  + replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R8. exact (EX 11%nat ltac:(lia)).
  + replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R9. exact (EX 10%nat ltac:(lia)).
  + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R18. exact (EX 9%nat ltac:(lia)).
  + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R19. exact (EX 8%nat ltac:(lia)).
  + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R20. exact (EX 7%nat ltac:(lia)).
  + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R21. exact (EX 6%nat ltac:(lia)).
  + replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R22. exact (EX 5%nat ltac:(lia)).
  + replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R23. exact (EX 4%nat ltac:(lia)).
  + replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R24. exact (EX 3%nat ltac:(lia)).
  + replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R25. exact (EX 2%nat ltac:(lia)).
  + replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R26. exact (EX 1%nat ltac:(lia)).
  + replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R27. exact (EX 0%nat ltac:(lia)).
- unfold arm. intros x. apply HFr. intros (r & Hin & Hr). cbn [ss_mem dss_epi depi_regions In] in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia.
- apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS pa_segs_low). exact HJ.
Qed.

Lemma dend_closed_xR : forall cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 regs1 (Q : world SEGS -> config -> Prop),
DBASE_x B ARx MT RP MMAX RG cx Hpe kr ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m1 md1 k1 ->
In (dxG cx, ATABLE) (ablocks B ly1 S1) ->
awr W1 m1 (dxSA cx) AENT ->
getr regs1 22 = w64 (dxSA cx) -> getr regs1 18 = w64 (rg_s RG) -> getr regs1 21 = w64 SHADOW_OFF ->
getr regs1 23 = w64 (dHA RG cx) -> getr regs1 24 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) ->
val_mem SEGS (arm W1 m1) (dHA RG cx + 8) 4 1 ->
(forall regsF mF mdF,
  getr regsF 2 = getr regs1 2 -> getr regsF 3 = getr regs1 3 -> getr regsF 4 = getr regs1 4 ->
  @ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 mF mdF k1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (dxSA cx + 4 <= a < dxSA cx + 8) ->
     aview SEGS (w_H W1) mF a = aview SEGS (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mF a) ->
  val_mem SEGS (arm W1 mF) (dxSA cx + 4) 4 1 ->
  SRrG SEGS R W1 (cfg_at SEGS (BASE + A_dr_epi) regsF mF mdF) Q) ->
SRrG SEGS R W1 (cfg_at SEGS (BASE + A_dr_end) regs1 m1 md1) Q.
Proof.
intros cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 regs1 Q HB HJ HGin HAW R22 R18 R21 R23 R24 Hcl KC.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (_ & _ & _ & HGle & HSAle & _ & _ & _ & Hj & _).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR HGin) as (_ & HG4 & HGc & Hap & _).
assert (RQT : req_size ATABLE = 896) by reflexivity.
rewrite RQT in HGc, Hap.
assert (HSA : 4096 <= dxSA cx <= 0x7fffff800000) by (unfold AENT, ATABLE in *; lia).
unfold dHA in R23, Hcl.
pose proof (dend_entry_x W1 regs1 m1 (dxj cx) 1 (dxSA cx) Hj R18 R21 R22 R23 R24 HSA Hcl ltac:(lia)) as HS.
remember (Eimg (Ereg regs1 [])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (UB1 : U E dBx1 = SHADOW_OFF + 12 * Z.of_nat (dxj cx))
  by (unfold dBx1; apply U_atom; [rewrite (EREG 24%nat 24%bv) by (first [lia | reflexivity]); exact R24 | unfold SHADOW_OFF; lia]).
assert (U18 : U E (SOff 18 0) = rg_s RG)
  by (apply U_atom; [rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); exact R18 | pose proof HGSB; unfold ASRC in *; lia]).
assert (UB2 : U E dBx2 = SHADOW_OFF)
  by (unfold dBx2; apply U_atom; [rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21 | unfold SHADOW_OFF; lia]).
assert (U22 : U E (SOff 22 0) = dxSA cx)
  by (apply U_atom; [rewrite (EREG 22%nat 22%bv) by (first [lia | reflexivity]); exact R22 | lia]).
assert (B22 : bv_unsigned (ew E 22) = dxSA cx)
  by (rewrite (EREG 22%nat 22%bv) by (first [lia | reflexivity]); rewrite R22; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS dBx1 dSH1 E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor]. exact (dend_shent1_x ly1 S1 Hp1 W1 m1 md1 E (dxj cx) HAR Hj UB1 U18). }
clear HE.
unfold cfg_at. change (w64 (BASE + A_dr_end)) with (Z_to_bv 64 (BASE + A_dr_end)).
set (j := dxj cx) in *. clearbody j.
destruct j as [|[|[|[|jj]]]]; [| | | | exfalso; lia].
all: paj_run_to_tok_xR RUNTOR HS HJ SHOK Bspan A_dr_eof; [apply awr_ok_x_of0; awr_ok_tac|].
all: rename HFr into FR1; rename HG0 into GR1; clear HF.
all: pose proof (st_ok_pi_submem _ _ _ [] HS ltac:(submem_tac) eq_refl) as HS0; clear HS.
all: assert (RGOK : region_ok SEGS E (ms_mem (restrict (w_H W1) ms)) dr_eof_region);
  [ unfold region_ok, dr_eof_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
    rewrite B22; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (writable_kept (w_H W1) m1 (ms_mem ms)); [apply (apresent_grows _ _ _ _ GR1)|];
    exact (HAW o ltac:(unfold AENT; lia)) |].
all: pose proof (st_ok_pi_add_region _ _ _ dr_eof_region HS0 eq_refl RGOK I) as HS1; clear HS0;
  cbn [ss_pc ss_regs ss_resv ss_facts ss_mem] in HS1.
all: assert (SHOK2 : sh_ok SEGS dBx2 dSH2 E (mrestrict (w_H W1) (ms_mem ms)));
  [ unfold sh_ok, dSH2; apply Forall_cons; [|apply Forall_nil];
    eapply (shent_ok_of_range SEGS (w_H W1) (ms_mem ms) E dBx2 22%nat (dxSA cx + 4) 4 (dxSA cx) 4 8);
    [ eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms) _ (dxG cx) ATABLE);
      [ eapply ajournal_gx_AR_xR; exact HJ | exact HGin | lia
      | rewrite RQT; unfold AENT, ATABLE in *; lia ]
    | exact UB2 | exact U22 | lia | lia
    | intros x Hx; rewrite Z.min_l, Z.max_r in Hx by lia;
      unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, AENT, ATABLE in *; lia ] |].
all: paj_run_to_tok_xR RUNTOR HS1 HJ SHOK2 Bspan A_dr_epi;
  [ cbn [ss_mem]; apply awr_ok_x_cons; [|apply awr_ok_x_nil];
    unfold dr_eof_region; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite B22;
    intros x Hx; left; split; [|lia];
    unfold awr_byte; right; left; split;
    [ exists (dxSA cx, dxSA cx + AENT); split; [left; reflexivity | cbn [fst snd]; unfold AENT; lia]
    | exists (dxG cx), ATABLE; split; [exact HGin | rewrite RQT; unfold AENT, ATABLE in *; lia] ] |].
all: rename HFr into FR2; rename HG0 into GR2; clear HF.
all: prreg HS1 (2%bv : bv 5) X2; prreg HS1 (3%bv : bv 5) X3; prreg HS1 (4%bv : bv 5) X4.
all: pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS1 eq_refl) as RF; cbn [ms_mem restrict] in RF.
all: pmkst HS1.
all: apply KC;
  [ rewrite X2; apply EREG; [lia | reflexivity]
  | rewrite X3; apply EREG; [lia | reflexivity]
  | rewrite X4; apply EREG; [lia | reflexivity]
  | exact HJ
  | intros a Ha Hn;
    rewrite (aview_kept_out _ _ (w_H W1) (ms_mem ms) (ms_mem ms0) FR2 a Ha);
    [ apply (aview_kept_out _ _ (w_H W1) m1 (ms_mem ms) FR1 a Ha);
      intros (r & Hin & Hr); cbn in Hin; destruct Hin as [<- | []]; cbn in Hr; lia
    | intros (r & Hin & Hr); cbn in Hin; destruct Hin as [<- | []];
      cbn [dr_eof_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite B22 in Hr; lia ]
  | intros a Hp; apply (apresent_grows _ _ _ _ GR2); apply (apresent_grows _ _ _ _ GR1); exact Hp
  | unfold arm; eapply (field_of_region _ _ 22%nat (dxSA cx) _ 4 8 4 8 4 4%N (SLit 1) 1 RF);
    [ rewrite !ew_ewset_other by lia; exact B22 | left; reflexivity | reflexivity | cbn; lia | cbn; lia ] ].
Qed.

Lemma dend_eagain_xR : forall cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 regs1 (Q : world SEGS -> config -> Prop),
DBASE_x B ARx MT RP MMAX RG cx Hpe kr ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m1 md1 k1 ->
In (dxG cx, ATABLE) (ablocks B ly1 S1) ->
awr W1 m1 (as_errno B) 4 ->
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
getr regs1 3 = getr (dxregs cx) 3 -> getr regs1 4 = getr (dxregs cx) 4 ->
getr regs1 22 = w64 (dxSA cx) -> getr regs1 18 = w64 (rg_s RG) -> getr regs1 21 = w64 SHADOW_OFF ->
getr regs1 23 = w64 (dHA RG cx) -> getr regs1 24 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) ->
val_mem SEGS (arm W1 m1) (dHA RG cx + 8) 4 0 ->
(forall regsF mF mdF,
  getr regsF 2 = getr regs1 2 -> getr regsF 3 = getr regs1 3 -> getr regsF 4 = getr regs1 4 ->
  @ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 mF mdF k1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= a < dsp0 cx - DRAIN_FRAME) ->
     aview SEGS (w_H W1) mF a = aview SEGS (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mF a) ->
  val_mem SEGS (arm W1 mF) (as_errno B) 4 11 ->
  SRrG SEGS R W1 (cfg_at SEGS (BASE + A_dr_epi) regsF mF mdF) Q) ->
SRrG SEGS R W1 (cfg_at SEGS (BASE + A_dr_end) regs1 m1 md1) Q.
Proof.
intros cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 regs1 Q HB HJ HGin HAWE Hsp H3 H4 R22 R18 R21 R23 R24 Hcl KC.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HPRE0 & _ & _ & HGle & HSAle & _ & _ & _ & Hj & _).
pose proof HPRE0 as (_ & _ & _ & Hgp & Htp & _).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR HGin) as (_ & HG4 & HGc & Hap & _).
assert (RQT : req_size ATABLE = 896) by reflexivity.
rewrite RQT in HGc, Hap.
assert (HSA : 4096 <= dxSA cx <= 0x7fffff800000) by (unfold AENT, ATABLE in *; lia).
unfold dHA in R23, Hcl.
pose proof (dend_entry_x W1 regs1 m1 (dxj cx) 0 (dxSA cx) Hj R18 R21 R22 R23 R24 HSA Hcl ltac:(lia)) as HS.
remember (Eimg (Ereg regs1 [])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (UB1 : U E dBx1 = SHADOW_OFF + 12 * Z.of_nat (dxj cx))
  by (unfold dBx1; apply U_atom; [rewrite (EREG 24%nat 24%bv) by (first [lia | reflexivity]); exact R24 | unfold SHADOW_OFF; lia]).
assert (U18 : U E (SOff 18 0) = rg_s RG)
  by (apply U_atom; [rewrite (EREG 18%nat 18%bv) by (first [lia | reflexivity]); exact R18 | pose proof HGSB; unfold ASRC in *; lia]).
assert (SHOK : sh_ok SEGS dBx1 dSH1 E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor]. exact (dend_shent1_x ly1 S1 Hp1 W1 m1 md1 E (dxj cx) HAR Hj UB1 U18). }
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
clear HE.
unfold cfg_at. change (w64 (BASE + A_dr_end)) with (Z_to_bv 64 (BASE + A_dr_end)).
set (j := dxj cx) in *. clearbody j.
destruct j as [|[|[|[|jj]]]]; [| | | | exfalso; lia].
all: paj_run_tok_xR RUNR HS HJ SHOK Bspan; [apply awr_ok_x_of0; awr_ok_tac|].
all: rename HFr into FR1; rename HG0 into GR1; clear HF.
all: pmkst HS.
all: prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4.
all: eapply (SRrG_bind SEGS R R_trans);
  [ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_DR B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_errno_location)
      (fun _ => False) (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 (as_tp B - 164))
      W1 (ms_regs ms) (ms_mem ms) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx)
      ([] : list (Z * Z)) ly1 S1 Hp1 _ k1 (- DRAIN_FRAME) _ HG eq_refl HJ);
    [ unfold spZ at 1; rewrite Q2, Usp; lia
    | reflexivity
    | unfold DRAIN_FRAME; lia
    | lia
    | unfold ESTACK, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia
    | rewrite Q3, (EREG 3%nat 3%bv), H3 by (first [lia | reflexivity]); exact Hgp
    | rewrite Q4, (EREG 4%nat 4%bv), H4 by (first [lia | reflexivity]); exact Htp
    | exact Q1
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | intros _; right; intros []
    | intros a []
    | intros a []
    | intros HPRE _; exact (AERRNO ly1 S1 Hp1 W1 (ms_regs ms) (ms_mem ms) _ HPRE) ] |].
all: cbv beta; intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Herr & Hfr2 & Hpres2).
all: jafter_call_keep_pi HS 32%nat regs2 (mrestrict (w_H W1) mem2) HP2 ([] : list nat) HS2.
all: specialize (HS2 (Forall_nil _)); clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS.
all: remember (havoc E 32 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
all: assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
all: assert (OLDa : forall m, (m < 32)%nat -> ew Ea m = ew E m)
  by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
all: clear HEa.
all: prreg HS (10%bv : bv 5) R10.
all: assert (HERRI : 0x10000 <= as_errno B /\ as_errno B + 4 <= 0x5fb000);
  [ assert (HI4 : forall i, 0 <= i < 4 -> in_img SEGS (as_errno B + i));
    [ intros i Hi; apply (proj1 (HG (as_errno B + i) ltac:(unfold G_DR, G_SL, inG; cbn [In];
        repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ])))
    | pose proof (pa_img_range _ (HI4 0 ltac:(lia))) as P0; pose proof (pa_img_range _ (HI4 3 ltac:(lia))) as P3; lia ] |].
all: assert (F36 : ew Ea 36 = Z_to_bv 64 (as_errno B)) by (rewrite <- R10, Herr, HERRNO; reflexivity).
all: assert (B36 : bv_unsigned (ew Ea 36) = as_errno B) by (rewrite F36; apply unsigned_lit_small; lia).
all: apply (st_ok_pi_add_fact _ _ _ 36%nat (mkAF 0x10000 0x5fb000 0)) in HS;
  [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite B36, Z.pow_0_r, Z.mod_1_r; lia ].
all: apply (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 36%nat) 0 4 0 4 [])) in HS;
  [ | vm_compute; reflexivity
    | unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite B36; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
      intros o Ho; apply (writable_kept (w_H W1) m1 mem2);
      [ intros Hp; apply Hpres2; apply (apresent_grows _ _ _ _ GR1); exact Hp | exact (HAWE o Ho) ]
    | cbn; exact I ].
all: assert (UB : U Ea dBx2 = SHADOW_OFF)
  by (unfold dBx2; apply U_atom; [rewrite (OLDa 21%nat) by lia; rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21
      | unfold SHADOW_OFF; lia]).
all: assert (UE36 : U Ea (SOff 36 0) = as_errno B) by (apply U_atom; [exact F36 | lia]).
all: assert (SHOK3 : sh_ok SEGS dBx2 [mkSHE 36 0 4] Ea (mrestrict (w_H W1) mem2));
  [ unfold sh_ok; apply Forall_cons; [|apply Forall_nil];
    eapply (shent_ok_of_range SEGS (w_H W1) mem2 Ea dBx2 36%nat (as_errno B) 4 (as_errno B) 0 4);
    [ apply (azs_range_addressable_x B ARx LAWS ly1 S1 Hp1 W1 mem2 md2 (as_errno B) 4);
      [ eapply ajournal_gx_AR_xR; exact HJ2 | exact HERRZ ]
    | exact UB | exact UE36 | lia | lia
    | intros x Hx; rewrite Z.min_l, Z.max_r in Hx by lia; unfold SHADOW_OFF; lia ] |].
all: paj_run_to_tok_xR RUNTOR HS HJ2 SHOK3 Bspan A_dr_epi;
  [ cbn [ss_mem]; apply awr_ok_x_cons_g; [|apply awr_ok_x_nil];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite B36;
    intros a Ha; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ] |].
all: rename HFr into FR3; rename HG0 into GR3; clear HF.
all: prreg HS (2%bv : bv 5) X2; prreg HS (3%bv : bv 5) X3; prreg HS (4%bv : bv 5) X4.
all: pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RF; cbn [ms_mem restrict] in RF.
all: pmkst HS.
all: apply KC;
  [ rewrite X2, OLDa by lia; apply EREG; [lia | reflexivity]
  | rewrite X3, OLDa by lia; apply EREG; [lia | reflexivity]
  | rewrite X4, OLDa by lia; apply EREG; [lia | reflexivity]
  | exact HJ2
  | intros a Ha Hn Hsc;
    rewrite (aview_kept_out _ _ (w_H W1) mem2 (ms_mem ms0) FR3 a Ha);
    [ rewrite (Hfr2 a Ha (fun x => x)); [|intros Hs; apply Hsc; lia];
      apply (aview_kept_out _ _ (w_H W1) m1 (ms_mem ms) FR1 a Ha);
      intros (r & Hin & Hr); cbn in Hin; destruct Hin as [<- | []]; cbn in Hr; lia
    | intros (r & Hin & Hr); cbn in Hin; destruct Hin as [<- | []];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite B36 in Hr; lia ]
  | intros a Hp; apply (apresent_grows _ _ _ _ GR3); apply Hpres2; apply (apresent_grows _ _ _ _ GR1); exact Hp
  | unfold arm; pose proof (field_of_region _ _ 36%nat (as_errno B) _ 0 4 0 4 0 4%N (SLit 11) 11 RF) as VF;
    rewrite Z.add_0_r in VF; apply VF;
    [ rewrite !ew_ewset_other by lia; exact B36 | left; reflexivity | reflexivity | cbn; lia | cbn; lia ] ].
Qed.

Lemma dend_post_xR : forall cx Hp kr s1 D ly1 S1 Hp1 W1 m' md' k1 regs' e1 e' h1 out1 ev' LB1 spent jb a tl,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m' md' k1 ->
aregs_preserved (dxregs cx) regs' ->
apres_kept B (dxW cx) (dxmem cx) W1 m' ->
e' = dset_eof e1 (if hs_closed h1 =? 1 then 1 else re_eof e1) ->
garr8 SEGS (arm W1 m') (dxSA cx) (bzs (entry_bytes e')) -> awr W1 m' (dxSA cx) AENT ->
aentry_ok B ly1 S1 W1 m' e' ->
asrc_at B ly1 S1 W1 m' (dHA RG cx) h1 ->
(forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= x < dHA RG cx + ASRC) ->
   abyte_kept (dxW cx) (dxmem cx) W1 m' x) ->
aout_at B RG ly1 S1 W1 m' (dctl cx (Z.of_nat (length (with_nul (lines (dSTR cx) D)))) ev')
  (if dlive cx then dxO cx ++ LB1 else dxO cx) (dxmx cx)
  (if dlive cx then drain_b_c.ds_no s1 else dxno cx) (drain_b_c.ds_ocap s1) out1 ->
(dlive cx = false -> out1 = dxout cx /\ drain_b_c.ds_ocap s1 = dxcap cx) ->
Permutation (ablocks B ly1 S1)
  ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) ->
DLINK s1 e1 h1 -> DSAME cx e1 h1 -> DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 ->
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) ->
drain_b_c.ds_pend s1 = [] -> drain_b_c.ds_eintr s1 = false -> 4096 <= drain_b_c.ds_cap s1 - ulen s1 ->
dlater cx s1 jb a tl -> dbud_x B MT RP MMAX cx kr ly1 S1 spent tl ->
dPOST_xR B PST ARx MT RP RG R cx Hp kr W1 (mkCfg (mkst regs' (getr (dxregs cx) 1) m' (seg_rom SEGS)) md').
Proof.
intros cx Hp kr s1 D ly1 S1 Hp1 W1 m' md' k1 regs' e1 e' h1 out1 ev' LB1 spent jb a tl HB HJ HRP HAPK He' HEB HEW HEOK
  HSRC HGK HOUT HDEAD HPERM HDL HDS HDH HJ1 HPE HEIN HROOM HLAT HBUD.
destruct HLAT as (fuel & Hn & Hwf & Ht & Hf).
destruct fuel as [|f]; [unfold dneed in Hn; lia|].
rewrite (drun_end f (dlive cx) (dxmx cx) s1 jb a HROOM HEIN HPE) in Ht, Hf. cbn [fst snd] in Ht, Hf. subst tl.
pose proof HDH as (HPS & HREF & HEXP & HFST & HCAP & HNO & HLB & HND & HSS & _ & _).
assert (HD : D = dPS cx) by (rewrite HPS; unfold pstream, prest; rewrite HPE; symmetry; apply app_nil_r).
subst D.
pose proof HDL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & _).
pose proof HDS as (S1' & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
pose proof HBUD as ((Bmo & Bsp & Bcost & _ & _) & Brm & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPB & _).
pose proof HSRC as (_ & _ & _ & _ & _ & Hcl01 & _ & _ & _ & _ & _ & _ & _ & _ & Hoff & _ & Hov01 & _).
assert (HCAPX : (if dlive cx then drain_b_c.ds_ocap s1 else dxcap cx) = drain_b_c.ds_ocap s1)
  by (revert HDEAD; destruct (dlive cx); intros HDEAD; [reflexivity | symmetry; exact (proj2 (HDEAD eq_refl))]).
assert (HNOX : (if dlive cx then drain_b_c.ds_no s1 else dxno cx) =
  (if dlive cx then dxno cx + dr_tot (dxh cx) else dxno cx))
  by (destruct (dlive cx); [exact HNO | reflexivity]).
assert (HRECS : hl_recs (hs_pending h1) = []) by (rewrite HPE in L7; exact (map_eq_nil _ _ L7)).
subst e'.
unfold dPOST_xR, dr_post_x.
exists ly1, S1, Hp1, regs', m', md', k1, (dset_eof e1 (if hs_closed h1 =? 1 then 1 else re_eof e1)), h1, out1, ev', LB1,
  ((dxG cx, ATABLE) :: dxrest cx).
cbv zeta.
change (dr_fin (dxc cx) (dxmx cx) (dxno cx) (dxcap cx) (dxe cx) (dxh cx)) with (dfin cx).
change (dr_live (dxc cx) (dxh cx)) with (dlive cx).
rewrite <- Hf, HCAPX.
split; [reflexivity|].
split; [exact HJ|].
split; [exact HRP|].
split; [exact HAPK|].
split.
{ change (dr_cost MT (dxc cx) (dxmx cx) (dxno cx) (dxcap cx) (dxe cx) (dxh cx)) with (dcost MT cx).
  apply (mle_weaken MT _ _ spent _ MTL Bmo). unfold tr_cost in Bcost. cbn [fold_right] in Bcost. lia. }
(* the room left: the entry's kr under the cut's room (RMM drops the requests' own count) *)
split; [eapply (RMM S1); [|exact Brm]; lia|].
split; [exact (Permutation_trans HPB (dperm_mv_x _ _ _ _ _))|].
split; [exact (Permutation_trans HPERM (dperm_mv_x _ _ _ _ _))|].
split; [exact HEB|]. split; [exact HEW|]. split; [exact HEOK|].
cbn [dset_eof re_fd re_eof re_cap re_U re_skip re_keys re_hp re_kh].
split; [exact S1'|].
split; [rewrite S5, S2; reflexivity|].
split; [rewrite L1; unfold ulen in HROOM; lia|].
split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|].
split; [exact L5|].
split; [exact S10|].
split; [rewrite L4; exact HND|].
split; [rewrite L4; exact HSS|].
split; [exact HSRC|].
split; [exact HGK|].
split; [exact L11|].
split; [exact HCAP|].
split; [exact S3|]. split; [exact S5|].
split; [rewrite L6, HEIN; reflexivity|].
split; [exact HRECS|].
split; [destruct Hoff as [(_ & Ho) | (r & rs & Hr & _)]; [exact Ho | rewrite HRECS in Hr; discriminate]|].
split; [exact S6|]. split; [exact S7|]. split; [exact S8|].
split; [rewrite L9, HREF; reflexivity|].
split; [exact HEXP|].
split; [exact HFST|].
split; [exact S9|].
split.
{ rewrite L3. destruct HJ1 as (JK & _). rewrite JK, <- L9. unfold hs_state. cbn [ls_k].
  destruct Hov01 as [-> | ->]; reflexivity. }
split.
{ intros H0. rewrite L2. destruct HJ1 as (JK & JW & _).
  assert (Hs : drain_b_c.ds_skip s1 = false)
    by (rewrite L3 in H0; destruct (drain_b_c.ds_skip s1); [discriminate | reflexivity]).
  rewrite (JW Hs), <- L9. reflexivity. }
split; [exact HLB|].
rewrite HNOX in HOUT. exact HOUT.
Qed.

Theorem dr_end_xR : dr_end_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros HEPI cx Hpe kr s1 D W1 c1 HB HDE.
destruct HDE as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & tl &
  -> & Hsp & H3 & H4 & R22 & R18 & R21 & R23 & R24 & HFRM & HDM & HNZ & HUS & HDL & HDS & HDH & HJ1 & HPE & HEIN &
  HROOM & HLAT & HBUD).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HDM as (HJ & HROM & HAPK & HFRS & _ & HEB & HEW & HEX & HSRC & HOTH & HGK & HOUT & HDEAD & HPERM).
pose proof HB as (HPRE0 & _ & _ & HGle & HSAle & _ & _ & _ & Hj & _).
pose proof HPRE0 as (_ & Hra & _).
pose proof HFRM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSV).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (HGin : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi, Hstk0.
assert (HDS0 : DRAIN_STK_x = 16976) by reflexivity.
assert (RQT : req_size ATABLE = 896) by reflexivity.
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR HGin) as (_ & HG4 & HGc & _).
rewrite RQT in HGc.
assert (HERRI : 0x10000 <= as_errno B /\ as_errno B + 4 <= 0x5fb000).
{ assert (HI4 : forall i, 0 <= i < 4 -> in_img SEGS (as_errno B + i)).
  { intros i Hi. apply (proj1 (HG (as_errno B + i) ltac:(unfold G_DR, G_SL, inG; cbn [In];
      repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))). }
  pose proof (pa_img_range _ (HI4 0 ltac:(lia))) as P0. pose proof (pa_img_range _ (HI4 3 ltac:(lia))) as P3. lia. }
assert (TBE : forall x, dxSA cx <= x < dxSA cx + AENT -> ~ (as_errno B <= x < as_errno B + 4)).
{ intros x Hx He. apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE x HAR HGin);
    [rewrite RQT; unfold AENT, ATABLE in *; lia|].
  apply (proj1 (HG x ltac:(unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))). }
assert (HEOK : aentry_ok B ly1 S1 W1 m1 e1).
{ destruct HEX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & _ & X9 & X10 & X11 & X12 & X13 & X14).
  exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 (conj HUS (conj HNZ
    (conj X9 (conj X10 (conj X11 (conj X12 (conj X13 X14)))))))))))))). }
pose proof HEOK as (_ & _ & Hpd1 & Hpd2 & _).
pose proof HSRC as (_ & _ & Vcl & _ & _ & Hcl01 & _).
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAWE & _).
set (L := aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) in HPERM.
assert (INL : forall b, In b L -> In b (ablocks B ly1 S1))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; exact Hb).
assert (FE : forall r, In r (aentry_fp e1) -> forall x, fst r <= x < snd r ->
  dlow cx x /\ ~ (as_errno B <= x < as_errno B + 4)).
{ apply (dend_fp_entry_x cx ly1 S1 Hp1 W1 m1 md1 e1 L HAR HPERM); [|exact HEOK].
  intros b Hb. unfold L. apply in_or_app. left. exact Hb. }
assert (FS : forall r, In r (asrc_fp (dHA RG cx) h1) -> forall x, fst r <= x < snd r ->
  dlow cx x /\ ~ (as_errno B <= x < as_errno B + 4)).
{ apply (dend_fp_src_x cx ly1 S1 Hp1 W1 m1 md1 L h1 HAR HPERM); [| exact HGin | exact Hj | exact HSRC].
  intros b Hb. unfold L. apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (FO : forall r, In r (aout_fp B RG (drain_b_c.ds_ocap s1) out1) -> forall x, fst r <= x < snd r ->
  dlow cx x /\ (r <> (as_errno B, as_errno B + 4) -> ~ (as_errno B <= x < as_errno B + 4))).
{ eapply (dend_fp_out_x cx ly1 S1 Hp1 W1 m1 md1 _ _ _ _ _ _ L HAR HPERM); [| exact HOUT].
  intros b Hb. unfold L. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (FB : drain_b_c.ds_ocap s1 <> 0 -> forall x, out1 <= x < out1 + drain_b_c.ds_ocap s1 ->
  ~ (as_errno B <= x < as_errno B + 4)).
{ intros Hc x Hx. pose proof (req_size_pos (drain_b_c.ds_ocap s1)) as Hrq.
  pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
  destruct Hblk as [(Hc0 & _) | (Hcp & _ & _)]; [lia|].
  destruct (Hrq ltac:(lia)) as (_ & Hrq').
  refine (proj2 (dend_low_blk_x cx ly1 S1 Hp1 W1 m1 md1 L out1 (drain_b_c.ds_ocap s1) x HAR HPERM _ ltac:(lia))).
  unfold L. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
  unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity. }
assert (FG : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> dlow cx x /\ ~ (as_errno B <= x < as_errno B + 4))
  by (intros x Hx; exact (dend_gs_ok_x cx ly1 S1 Hp1 W1 m1 md1 x HAR HGin Hx)).
destruct Hcl01 as [Hc0 | Hc1].
- apply (dend_eagain_xR cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 regs1 _ HB HJ HGin HAWE Hsp H3 H4 R22 R18 R21 R23 R24
    ltac:(rewrite <- Hc0; exact Vcl)).
  intros regsF mF mdF F2 F3 F4 HJF KV PR VE.
  apply (HEPI cx Hpe ly1 S1 Hp1 W1 mF mdF k1 regsF (dPOST_xR B PST ARx MT RP RG R cx Hpe kr) HJF).
  + unfold spZ in *. rewrite F2. exact Hsp.
  + rewrite F3. exact H3.
  + rewrite F4. exact H4.
  + exact Hra.
  + intros i Hi. eapply val_mem_kept; [|exact (HSV i Hi)]. intros k Hk.
    apply KV; unfold DRAIN_FRAME, ESTACK in *; lia.
  + intros regs' m' md' HRP Harm HJ'.
    set (P := fun x => as_errno B <= x < as_errno B + 4 \/ dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME).
    assert (KVP : forall x, 0 <= x < 2 ^ 64 -> ~ P x -> aview SEGS (w_H W1) m' x = aview SEGS (w_H W1) m1 x).
    { intros x Hx HP. rewrite (aview_eq_of SEGS _ mF m' x (Harm _)).
      apply KV; [exact Hx | intros H; apply HP; left; exact H | intros H; apply HP; right; exact H]. }
    assert (PR' : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m' x).
    { intros x Hp. destruct (PR x Hp) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
      specialize (Harm (Z_to_bv 64 x)). unfold arm, mrestrict in Harm. rewrite Hh in Harm. rewrite Harm. exact Hb. }
    assert (VE' : val_mem SEGS (arm W1 m') (as_errno B) 4 11).
    { eapply val_mem_kept; [|exact VE]. intros k Hk. apply aview_eq_of. apply Harm. }
    assert (BK : forall x, 0 <= x < alloc_ceiling -> ~ (as_errno B <= x < as_errno B + 4) ->
      abyte_kept W1 m1 W1 m' x).
    { intros x Hx Hne. apply (dend_bk_x W1 m1 m' P x KVP PR'); [lia|].
      intros [H | H]; [exact (Hne H) | unfold DRAIN_FRAME, ESTACK in *; lia]. }
    apply (dend_post_xR cx Hpe kr s1 D ly1 S1 Hp1 W1 m' md' k1 regs' e1 e1 h1 out1 11 LB1 spent jb a tl HB HJ' HRP).
    * intros x Hi Hno He Hp. apply PR'. exact (HAPK x Hi Hno He Hp).
    * rewrite Hc0. change (0 =? 1) with false. cbv iota. symmetry. apply dset_eof_id_x.
    * apply (akept_garr8 W1 m1); [|exact HEB]. intros x Hx. unfold bzs in Hx.
      rewrite length_map in Hx. apply BK; [| apply TBE]; unfold AENT, ATABLE in *;
      unfold entry_bytes, re_nheld in Hx; rewrite !length_app, !Mem.length_le4, !Mem.length_le8, Hpd1, Hpd2 in Hx; lia.
    * intros i Hi. unfold arm. apply (writable_kept (w_H W1) m1 m'); [apply PR' | exact (HEW i Hi)].
    * apply (aentry_ok_kept B ly1 S1 W1 m1 ly1 S1 W1 m' e1 HEOK);
        [|intros b Hb; apply INL; unfold L; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (FE r Hr x Hx) as [[Hl _] Hne]. exact (BK x Hl Hne).
    * apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m' (dHA RG cx) h1 HSRC);
        [|intros b Hb; apply INL; unfold L; apply in_or_app; right; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (FS r Hr x Hx) as [[Hl _] Hne]. exact (BK x Hl Hne).
    * intros x Hx Hn. pose proof (HGK x Hx Hn) as K1. destruct (FG x Hx) as [[Hl _] Hne].
      pose proof (BK x Hl Hne) as K2. split; [rewrite (proj1 K2); exact (proj1 K1)|].
      intros Hw. apply (proj2 K2). apply (proj2 K1). exact Hw.
    * apply (dend_aout_ev_x ly1 S1 W1 m1 m' _ _ _ _ _ _ 11 HOUT).
      -- intros r Hr x Hx Hne. destruct (FO r Hr x Hx) as [[Hl _] _]. exact (BK x Hl Hne).
      -- exact FB.
      -- exact VE'.
      -- intros i Hi. unfold arm. apply (writable_kept (w_H W1) m1 m'); [apply PR' | exact (HAWE i Hi)].
      -- lia.
    * exact HDEAD.
    * exact HPERM.
    * exact HDL.
    * exact HDS.
    * exact HDH.
    * exact HJ1.
    * exact HPE.
    * exact HEIN.
    * exact HROOM.
    * exact HLAT.
    * exact HBUD.
- apply (dend_closed_xR cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 regs1 _ HB HJ HGin HEW R22 R18 R21 R23 R24
    ltac:(rewrite <- Hc1; exact Vcl)).
  intros regsF mF mdF F2 F3 F4 HJF KV PR VE.
  apply (HEPI cx Hpe ly1 S1 Hp1 W1 mF mdF k1 regsF (dPOST_xR B PST ARx MT RP RG R cx Hpe kr) HJF).
  + unfold spZ in *. rewrite F2. exact Hsp.
  + rewrite F3. exact H3.
  + rewrite F4. exact H4.
  + exact Hra.
  + intros i Hi. eapply val_mem_kept; [|exact (HSV i Hi)]. intros k Hk.
    apply KV; unfold DRAIN_FRAME, AENT, ATABLE in *; lia.
  + intros regs' m' md' HRP Harm HJ'.
    set (P := fun x => dxSA cx + 4 <= x < dxSA cx + 8).
    assert (KVP : forall x, 0 <= x < 2 ^ 64 -> ~ P x -> aview SEGS (w_H W1) m' x = aview SEGS (w_H W1) m1 x).
    { intros x Hx HP. rewrite (aview_eq_of SEGS _ mF m' x (Harm _)). exact (KV x Hx HP). }
    assert (PR' : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m' x).
    { intros x Hp. destruct (PR x Hp) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
      specialize (Harm (Z_to_bv 64 x)). unfold arm, mrestrict in Harm. rewrite Hh in Harm. rewrite Harm. exact Hb. }
    assert (VE' : val_mem SEGS (arm W1 m') (dxSA cx + 4) 4 1).
    { eapply val_mem_kept; [|exact VE]. intros k Hk. apply aview_eq_of. apply Harm. }
    assert (BK : forall x, dlow cx x -> abyte_kept W1 m1 W1 m' x).
    { intros x [Hx Hnt]. apply (dend_bk_x W1 m1 m' P x KVP PR'); [lia|].
      intros H. apply Hnt. unfold P, AENT, ATABLE in *. lia. }
    apply (dend_post_xR cx Hpe kr s1 D ly1 S1 Hp1 W1 m' md' k1 regs' e1 (dset_eof e1 1) h1 out1 ev1 LB1 spent jb a tl HB HJ' HRP).
    * intros x Hi Hno He Hp. apply PR'. exact (HAPK x Hi Hno He Hp).
    * rewrite Hc1. reflexivity.
    * apply (dend_garr8_eof_x W1 m1 m' (dxSA cx) e1 HEB); [| exact Hpd1 | exact Hpd2 | exact VE'].
      intros x Hx Hn. apply KVP; [unfold AENT, ATABLE in *; lia | exact Hn].
    * intros i Hi. unfold arm. apply (writable_kept (w_H W1) m1 m'); [apply PR' | exact (HEW i Hi)].
    * apply dend_aentry_eof_x; [|right; reflexivity].
      apply (aentry_ok_kept B ly1 S1 W1 m1 ly1 S1 W1 m' e1 HEOK);
        [|intros b Hb; apply INL; unfold L; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (FE r Hr x Hx) as [Hl _]. exact (BK x Hl).
    * apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m' (dHA RG cx) h1 HSRC);
        [|intros b Hb; apply INL; unfold L; apply in_or_app; right; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (FS r Hr x Hx) as [Hl _]. exact (BK x Hl).
    * intros x Hx Hn. pose proof (HGK x Hx Hn) as K1. destruct (FG x Hx) as [Hl _].
      pose proof (BK x Hl) as K2. split; [rewrite (proj1 K2); exact (proj1 K1)|].
      intros Hw. apply (proj2 K2). apply (proj2 K1). exact Hw.
    * apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m' _ _ _ _ _ _ HOUT);
        [|intros b Hb; apply INL; unfold L; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (FO r Hr x Hx) as [Hl _]. exact (BK x Hl).
    * exact HDEAD.
    * exact HPERM.
    * exact HDL.
    * exact HDS.
    * exact HDH.
    * exact HJ1.
    * exact HPE.
    * exact HEIN.
    * exact HROOM.
    * exact HLAT.
    * exact HBUD.
Qed.

End wR.

(* ---- the strict pieces: each is its R twin at R := @wle SEGS ---- *)
Theorem dr_epi_x : dr_epi_stmt_x B PST ARx RG.
Proof.
eapply (dr_epi_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Lemma dend_closed_x : forall cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 regs1 (Q : world SEGS -> config -> Prop),
DBASE_x B ARx MT RP MMAX RG cx Hpe kr ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m1 md1 k1 ->
In (dxG cx, ATABLE) (ablocks B ly1 S1) ->
awr W1 m1 (dxSA cx) AENT ->
getr regs1 22 = w64 (dxSA cx) -> getr regs1 18 = w64 (rg_s RG) -> getr regs1 21 = w64 SHADOW_OFF ->
getr regs1 23 = w64 (dHA RG cx) -> getr regs1 24 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) ->
val_mem SEGS (arm W1 m1) (dHA RG cx + 8) 4 1 ->
(forall regsF mF mdF,
  getr regsF 2 = getr regs1 2 -> getr regsF 3 = getr regs1 3 -> getr regsF 4 = getr regs1 4 ->
  @ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 mF mdF k1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (dxSA cx + 4 <= a < dxSA cx + 8) ->
     aview SEGS (w_H W1) mF a = aview SEGS (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mF a) ->
  val_mem SEGS (arm W1 mF) (dxSA cx + 4) 4 1 ->
  SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_epi) regsF mF mdF) Q) ->
SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_end) regs1 m1 md1) Q.
Proof.
eapply (dend_closed_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Lemma dend_eagain_x : forall cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 regs1 (Q : world SEGS -> config -> Prop),
DBASE_x B ARx MT RP MMAX RG cx Hpe kr ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m1 md1 k1 ->
In (dxG cx, ATABLE) (ablocks B ly1 S1) ->
awr W1 m1 (as_errno B) 4 ->
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
getr regs1 3 = getr (dxregs cx) 3 -> getr regs1 4 = getr (dxregs cx) 4 ->
getr regs1 22 = w64 (dxSA cx) -> getr regs1 18 = w64 (rg_s RG) -> getr regs1 21 = w64 SHADOW_OFF ->
getr regs1 23 = w64 (dHA RG cx) -> getr regs1 24 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) ->
val_mem SEGS (arm W1 m1) (dHA RG cx + 8) 4 0 ->
(forall regsF mF mdF,
  getr regsF 2 = getr regs1 2 -> getr regsF 3 = getr regs1 3 -> getr regsF 4 = getr regs1 4 ->
  @ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 mF mdF k1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= a < dsp0 cx - DRAIN_FRAME) ->
     aview SEGS (w_H W1) mF a = aview SEGS (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mF a) ->
  val_mem SEGS (arm W1 mF) (as_errno B) 4 11 ->
  SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_epi) regsF mF mdF) Q) ->
SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_end) regs1 m1 md1) Q.
Proof.
eapply (dend_eagain_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Lemma dend_post_x : forall cx Hp kr s1 D ly1 S1 Hp1 W1 m' md' k1 regs' e1 e' h1 out1 ev' LB1 spent jb a tl,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m' md' k1 ->
aregs_preserved (dxregs cx) regs' ->
apres_kept B (dxW cx) (dxmem cx) W1 m' ->
e' = dset_eof e1 (if hs_closed h1 =? 1 then 1 else re_eof e1) ->
garr8 SEGS (arm W1 m') (dxSA cx) (bzs (entry_bytes e')) -> awr W1 m' (dxSA cx) AENT ->
aentry_ok B ly1 S1 W1 m' e' ->
asrc_at B ly1 S1 W1 m' (dHA RG cx) h1 ->
(forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= x < dHA RG cx + ASRC) ->
   abyte_kept (dxW cx) (dxmem cx) W1 m' x) ->
aout_at B RG ly1 S1 W1 m' (dctl cx (Z.of_nat (length (with_nul (lines (dSTR cx) D)))) ev')
  (if dlive cx then dxO cx ++ LB1 else dxO cx) (dxmx cx)
  (if dlive cx then drain_b_c.ds_no s1 else dxno cx) (drain_b_c.ds_ocap s1) out1 ->
(dlive cx = false -> out1 = dxout cx /\ drain_b_c.ds_ocap s1 = dxcap cx) ->
Permutation (ablocks B ly1 S1)
  ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) ->
DLINK s1 e1 h1 -> DSAME cx e1 h1 -> DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 ->
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) ->
drain_b_c.ds_pend s1 = [] -> drain_b_c.ds_eintr s1 = false -> 4096 <= drain_b_c.ds_cap s1 - ulen s1 ->
dlater cx s1 jb a tl -> dbud_x B MT RP MMAX cx kr ly1 S1 spent tl ->
dPOST_x B PST ARx MT RP RG cx Hp kr W1 (mkCfg (mkst regs' (getr (dxregs cx) 1) m' (seg_rom SEGS)) md').
Proof.
eapply (dend_post_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

(* ---- END: DEND 0x83bbc -> h->closed ? (s->eof = 1 at 0x83b64) : (errno = EAGAIN at 0x83b44), then dr_epi_x. ---- *)
Theorem dr_end_x : dr_end_stmt_x B PST ARx MT RP MMAX RG.
Proof.
eapply (dr_end_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

End cx.
End b.
End a.
