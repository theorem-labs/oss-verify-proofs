(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_crt1_kcrt: the call of check_round_trip at +0x68c of image B's
   LLVMFuzzerTestOneInput segment crt1, then the run +0x690 .. +0x6bc up to the call of check_braid:
   c1k_crt proves lib/B/Prog/LLVMFuzzerTestOneInput_segX_crt1_defs.v c1_K_crt from c1_K_braid.
   The shape is the sibling call sites' (LLVMFuzzerTestOneInput_segX_crt1_stage.v c1k_braid / c1k_memset):
   the call is discharged by LLVMFuzzerTestOneInput_segX_crt1_calls.v c1e_crt_call (every premise of
   check_round_trip's contract), the bytes it keeps by LLVMFuzzerTestOneInput_segX_crt1_glue.v c1g_keep_acall
   (from the post's acall_kept), the frame invariant and the memory clauses by
   LLVMFuzzerTestOneInput_segX_crt1_cut.v c1_step, the code by
   LLVMFuzzerTestOneInput_segX_crt1_runs.v c1_run_acrt carried into SRr by
   LLVMFuzzerTestOneInput_segX_crt1_fevt.v c1f_run (the inner journal re-established across the run by
   lib/Reusable/YCbq.v:636 ajournal_exec with no written byte: the run stores nothing), and the braid relation
   the callee reads by LLVMFuzzerTestOneInput_segX_crt1_braid.v c1b_braid_of_garr8.
   The one new piece is the meter and the event count across the call: c1k_cost_le / c1k_spent / c1k_rest /
   c1k_cost_rest below, each proved in an empty context (dec_crt_cost at this call's geometry is at most
   dec_crt_cost_max, which is what the 5cc -> 6f0 step of the ladder of
   lib/B/Prog/LLVMFuzzerTestOneInput_segs.v charges).
   NOTE on arithmetic: lia zifies the whole context, which is large here, so every numeric goal is closed under
   `clear - HN` with HN the one conjunction of the numbers the proof uses (c1k_braid's rule). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP09 YI00 YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Regs6ss ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr check_round_trip_cg
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segX_crt1_cut
  LLVMFuzzerTestOneInput_segX_crt1_glue LLVMFuzzerTestOneInput_segX_crt1_geo
  LLVMFuzzerTestOneInput_segX_crt1_braid LLVMFuzzerTestOneInput_segX_crt1_calls
  LLVMFuzzerTestOneInput_segX_crt1_runs LLVMFuzzerTestOneInput_segX_crt1_fevt
  LLVMFuzzerTestOneInput_segX_crt1_defs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LeafCgKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import LiaTwx2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* lib/Reusable/YM03.v:182-189 redefines lia globally; the donor proofs were built under lib/Lib/LiaTwx2.v's
   (zify_prune first), which this file takes back (LiaTwx2.v:187-190). *)
Local Ltac Lia.lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.

(* ---- the meter and the events of one check_round_trip call, in an empty context ---- *)

(* This call's three allocations are at most the largest geometry the ladder charges
   (LLVMFuzzerTestOneInput_cg.v:211-212 dec_crt_cost_max: 4 * 480, 8 * 127 and 3 * 480 bytes). *)
Lemma c1k_cost_le : forall (MT : ameter_ops) (nch ns : Z),
  ameter_laws MT -> 0 < nch <= 127 -> 0 < ns -> nch * ns <= 480 ->
  dec_crt_cost MT nch ns <= dec_crt_cost_max MT.
Proof.
intros MT nch ns MTL Hn Hs Hp.
assert (B1 : 0 <= 4 * (nch * ns) <= 1920) by (clear - Hn Hs Hp; nia).
assert (B2 : 0 <= 8 * nch <= 1016) by (clear - Hn; nia).
assert (B3 : 0 <= 3 * (nch * ns) <= 1440) by (clear - Hn Hs Hp; nia).
pose proof (mo_malloc_mono MT MTL (4 * (nch * ns)) 1920 B1) as M1.
pose proof (mo_malloc_mono MT MTL (8 * nch) 1016 B2) as M2.
pose proof (mo_malloc_mono MT MTL (3 * (nch * ns)) 1440 B3) as M3.
unfold dec_crt_cost, dec_crt_cost_max. clear - M1 M2 M3. lia.
Qed.

(* What the walk has spent at +0x6f0 covers what it had spent at +0x5cc plus this call. *)
Lemma c1k_spent : forall (MT : ameter_ops) (n nch ns : Z),
  ameter_laws MT -> 0 < nch <= 127 -> 0 < ns -> nch * ns <= 480 ->
  dec_spent_5cc MT n + dec_crt_cost MT nch ns <= dec_spent_6f0 MT n.
Proof.
intros MT n nch ns MTL Hn Hs Hp.
pose proof (c1k_cost_le MT nch ns MTL Hn Hs Hp) as HL.
unfold dec_spent_6f0. clear - HL. lia.
Qed.

(* What is still available at +0x5cc covers this call plus what is still available at +0x6f0. *)
Lemma c1k_rest : forall (MT : ameter_ops) (nch ns : Z),
  ameter_laws MT -> 0 < nch <= 127 -> 0 < ns -> nch * ns <= 480 ->
  dec_crt_cost MT nch ns + dec_rest_6f0 MT <= dec_rest_5cc MT.
Proof.
intros MT nch ns MTL Hn Hs Hp.
pose proof (c1k_cost_le MT nch ns MTL Hn Hs Hp) as HL.
unfold dec_rest_5cc. clear - HL. lia.
Qed.

(* ... so the budget the contract asks for is inside the one the cut point states. *)
Lemma c1k_cost_rest : forall (MT : ameter_ops) (nch ns : Z),
  ameter_laws MT -> 0 < nch <= 127 -> 0 < ns -> nch * ns <= 480 ->
  dec_crt_cost MT nch ns <= dec_rest_5cc MT.
Proof.
intros MT nch ns MTL Hn Hs Hp.
pose proof (c1k_rest MT nch ns MTL Hn Hs Hp) as HL.
pose proof (mo_malloc_nonneg MT MTL 1920 ltac:(clear; lia)) as N1.
pose proof (mo_malloc_nonneg MT MTL 1016 ltac:(clear; lia)) as N2.
pose proof (mo_malloc_nonneg MT MTL 1440 ltac:(clear; lia)) as N3.
pose proof (mo_free_nonneg MT MTL) as N4.
unfold dec_rest_6f0, dec_rest_840, dec_rest_96c, dec_crt_cost_max in HL.
clear - HL N1 N2 N3 N4. lia.
Qed.

(* The call's six model events take the journal count of +0x5cc to the one of +0x6f0. *)
Lemma c1k_ev : dec_ev_5cc + DEC_CRT_EV = dec_ev_6f0.
Proof. reflexivity. Qed.

(* ---- the call site ---- *)
Theorem c1k_crt : forall (rc : YM05.RunCeil) (B : asyms) (MT : ameter_ops) (RA_LLVMF : Z),
  dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  @AR_laws rc decodesegsB0 B -> ameter_laws MT ->
  (forall fx : YK11.FPState,
     @dec_check_round_trip_cg fx rc B MT (decodeb_sigma DB_check_round_trip) (CTX_check_round_trip RA_LLVMF)) ->
  @c1_K_braid rc B MT RA_LLVMF -> @c1_K_crt rc B MT RA_LLVMF.
Proof.
intros rc B MT RA_LLVMF HCELLS HROS HRNE LAWS MTL ICRT KBRAID.
intros cx res out mode nch ns fx' ly' S' W' regs' mem' md' HPRE HST HR Hdok Hns12 HBR R22 R1 R10 R11 R12 R13.
pose proof HPRE as (Hret & Hra & Hra4 & Hgp & Htp & Hstk & Hch & Hpay & Hn1 & Hn2 & Hnev & Hlive & Hrom).
pose proof HST as (Hfrm & Hcore & HP & Hres4 & Hout4 & Hmle & Hmok & Hmem & Hs80).
pose proof HR as (R19 & R20 & R21 & R23 & R24 & R26 & R27).
pose proof Hcore as (HJ & Hfrs & R8 & R9 & Hsp & Hsp1r & Hsp1al & Hgp' & Htp' & Hsaved & HF1 & HF2 & HFpres &
  HFL & Hpayb & Hgarr).
pose proof (proj1 HJ) as HAR.
pose proof (c1g_layout B LAWS cx ly' S' W' regs' mem' md' dec_ev_5cc res out nch ns Hcore HP Hn2 Hpay) as
  (Hsp0 & Hsp1 & H47 & Hinr & Hino & Ho4096 & Hoc & Hoapp & Hr4096 & Hrc & Hro & Hpo & Hof).
pose proof (c1g_body_len cx Hn2) as Hbl.
pose proof (@YM05.alloc_ceiling_val rc) as HCEIL.
pose proof Hmem as (Hfrs' & Hmode & Hfsh & Hgb & S24 & S32 & S40 & S56 & S64 & S72 & S88 & S112).
pose proof Hmode as (Hsrc & Hnch & Hns & V4 & V8).
pose proof (c1g_mode B LAWS cx ly' S' W' regs' mem' md' dec_ev_5cc mode nch ns HCELLS HROS HRNE Hrom Hcore Hmode
              Hfsh) as
  (Hm0 & Hmc & Hm4 & Hmapp & Hmvis & Hmra).
(* what the decode check gives (c1k_braid's reading of CDec.decode_ok) *)
assert (HD : CInsp.inspect_wf (dec_b_len (d_n cx)) (d_body cx) = true /\ 0 < nch /\ nch mod 2 = 0 /\
             0 < ns /\ nch * ns <= 480).
{ unfold CDec.decode_ok in Hdok. rewrite !andb_true_iff in Hdok.
  destruct Hdok as ((((Hw & P1) & P2) & P3) & P4).
  apply Z.ltb_lt in P1. apply Z.eqb_eq in P2. apply Z.ltb_lt in P3. apply Z.leb_le in P4.
  exact (conj Hw (conj P1 (conj P2 (conj P3 P4)))). }
destruct HD as (Hwf & Hn0 & Hev & Hs0 & Hprod).
assert (Hlen1492 : dec_b_len (d_n cx) = 1492).
{ unfold CInsp.inspect_wf in Hwf. rewrite !andb_true_iff in Hwf.
  destruct Hwf as ((((He & _) & _) & _) & _). apply Z.eqb_eq in He. exact He. }
assert (Holen : dec_b_olen nch ns = 3 * nch * ns).
{ unfold dec_b_olen.
  rewrite (proj2 (andb_true_iff _ _) (conj (proj2 (Z.ltb_lt 0 nch) Hn0) (proj2 (Z.ltb_lt 0 ns) Hs0))).
  reflexivity. }
assert (H1440 : 3 * nch * ns <= 1440)
  by (clear - Hprod; replace (3 * nch * ns) with (3 * (nch * ns)) by ring; lia).
pose proof (req_size_pos (dec_b_len (d_n cx)) ltac:(clear - Hlen1492; lia)) as [Hq1 Hq2].
pose proof (req_size_pos (dec_b_olen nch ns) ltac:(clear - Holen Hn0 Hs0; nia)) as [Hqo1 Hqo2].
assert (PW : 2 ^ 64 = 18446744073709551616 /\ 2 ^ 26 = 67108864 /\ 2 ^ 47 = 140737488355328 /\
             2 ^ 32 = 4294967296 /\ 2 ^ 33 = 8589934592 /\ 2 ^ 34 = 17179869184 /\ 2 ^ 13 = 8192)
  by (clear; repeat split; vm_compute; reflexivity).
assert (HN : 2 ^ 64 = 18446744073709551616 /\ 2 ^ 26 = 67108864 /\ 2 ^ 47 = 140737488355328 /\
             2 ^ 32 = 4294967296 /\ 2 ^ 33 = 8589934592 /\ 2 ^ 34 = 17179869184 /\ 2 ^ 13 = 8192 /\
             dec_b_len (d_n cx) = 1492 /\ Z.of_nat (length (d_body cx)) = 1492 /\
             1492 <= req_size (dec_b_len (d_n cx)) /\
             dec_b_olen nch ns = 3 * nch * ns /\ 3 * nch * ns <= 1440 /\
             3 * nch * ns <= req_size (dec_b_olen nch ns) /\
             0 < mode /\ mode + 12 <= YM05.alloc_ceiling /\
             0 < nch <= 127 /\ 0 < ns <= 12 /\ nch * ns <= 480 /\ nch mod 2 = 0 /\
             4096 <= res /\ res + req_size (dec_b_len (d_n cx)) <= YM05.alloc_ceiling /\
             4096 <= out /\ out + req_size (dec_b_olen nch ns) <= YM05.alloc_ceiling /\
             (res + req_size (dec_b_len (d_n cx)) <= out \/ out + req_size (dec_b_olen nch ns) <= res) /\
             YM05.alloc_ceiling + 32768 <= d_sp0 cx /\ d_sp0 cx - 240 <= d_sp1 cx <= d_sp0 cx - 224 /\
             d_sp0 cx <= 2 ^ 47 /\ d_sp1 cx mod 32 = 0 /\ d_sp0 cx mod 16 = 0 /\
             140735332483072 <= YM05.alloc_ceiling <= 140737479966720).
{ pose proof (proj1 Hstk) as Hal0. repeat split; try assumption; try (clear - PW; lia);
    try (clear - Hlen1492 Hbl PW; lia); try (clear - Hlen1492 Hq2 PW; lia);
    try (clear - Holen Hqo2 PW; lia); try (clear - Holen PW; lia); try (clear - H1440 PW; lia);
    try (clear - Hn0 Hnch PW; lia); try (clear - Hs0 Hns12 PW; lia); try (clear - Hprod PW; lia);
    try (clear - Hev PW; lia); try (clear - Hm0 PW; lia); try (clear - Hmc PW; lia);
    try (clear - Hsp0 PW; lia); try (clear - Hsp1 PW; lia); try (clear - H47 PW; lia);
    try (clear - Hr4096 PW; lia); try (clear - Hrc PW; lia); try (clear - Ho4096 PW; lia);
    try (clear - Hoc PW; lia); try (clear - Hro PW; lia); try (clear - HCEIL PW; lia);
    try (clear - Hsp1r PW; lia); try (clear - Hsp1al PW; lia); try (clear - Hal0 PW; lia). }
(* the two saved words below the entry sp that the call's frame-pointer chain is built from *)
unfold dec_b_saved, dec_b_saved_at in Hsaved.
apply Forall_cons_iff in Hsaved as [Hsv8 Hsaved]. apply Forall_cons_iff in Hsaved as [Hsv16 _].
cbn [fst snd] in Hsv8, Hsv16.
assert (EA : 0 <= DEC_A_LLVMF + 0x690 < 2 ^ 64)
  by (clear; unfold DEC_A_LLVMF, decodeb_text, DecodeBList.AF_LLVMFuzzerTestOneInput; lia).
assert (Ho16 : d_sp1 cx - d_sp0 cx <= 0) by (clear - HN; lia).
assert (Hsp16 : spZ regs' mod 16 = 0).
{ rewrite Hsp. pose proof (Z.div_mod (d_sp1 cx) 32 ltac:(lia)) as D1.
  pose proof (Z.div_mod (d_sp1 cx) 16 ltac:(lia)) as D3.
  pose proof (Z.mod_pos_bound (d_sp1 cx) 16 ltac:(lia)) as D4.
  clear - HN D1 D3 D4. lia. }
assert (Hlive2 : blocks_bytes S' + DEC_CRT_LIVE <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ HP), !bsum_app,
    <- (blocks_bytes_bsum B (d_ly cx) (d_S cx)).
  cbn [bsum fold_right snd]. unfold DEC_LIVE_LIB in Hlive. unfold DEC_CRT_LIVE, LIVE_MAX in *.
  clear - Hlive HN. lia. }
assert (HBRAID : dec_crt_braid (aview decodesegsB0 (w_H W') mem') (res + 50) out nch ns)
  by (apply (c1b_braid_of_garr8 W' mem' (d_body cx) res out nch ns);
      [clear - HN; lia | clear - HN; lia | clear - HN; lia | exact Hgb | exact HBR]).
(* ---- the call of check_round_trip at +0x68c ---- *)
eapply SRr_bind.
{ eapply (@c1e_crt_call rc B MT RA_LLVMF ICRT fx' (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' W' mem' md' dec_ev_5cc regs' (s0Z (d_regs cx))
    (res + 50) out nch ns res (dec_b_len (d_n cx)) out (dec_b_olen nch ns) (dec_rest_5cc MT) HJ Hch).
  - rewrite Hsv8. f_equal. exact Hra.
  - rewrite Hsv16. reflexivity.
  - exact Hra4.
  - left. unfold raZ. rewrite R1. unfold w64. apply MState.unsigned_lit. clear - EA. lia.
  - rewrite R1. apply YK0s.ret_ok_even. clear. vm_compute. reflexivity.
  - exact Hgp'.
  - exact Htp'.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R13.
  - unfold s0Z. rewrite R8. unfold w64. apply MState.unsigned_lit. clear - HN. lia.
  - exact Hsp16.
  - rewrite Hsp. clear - HN. lia.
  - rewrite Hsp. clear - HN. lia.
  - exact Hfrm.
  - rewrite c1b_even_mod. apply Z.eqb_eq. clear - HN. lia.
  - clear - HN. lia.
  - clear - HN. lia.
  - clear - HN. lia.
  - exact Hinr.
  - clear - HN. lia.
  - clear - HN. lia.
  - exact Hino.
  - clear - HN. lia.
  - clear - HN. lia.
  - exact HBRAID.
  - exact (c1_rom_rd B cx DEC_LLVMF_STK [(DEC_FCLASS, d_fpos cx)] ly' S' W' mem' md' dec_ev_5cc
             HROS HRNE Hrom HJ).
  - unfold DEC_EV_LIB in Hnev. unfold dec_ev_5cc, DEC_CRT_EV. clear - Hnev. lia.
  - exact Hlive2.
  - exact Hmok.
  - exact (c1k_cost_rest MT nch ns MTL ltac:(clear - HN; lia) ltac:(clear - HN; lia) ltac:(clear - HN; lia)). }
cbv beta.
intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfrm2 & HJ2 & HPRES & Hfrs2 & HPERM2 & HKEPT & HMLE2).
(* ---- what the call leaves ---- *)
assert (HPERM3 : Permutation (ablocks B ly2 S2)
  (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_b_len (d_n cx))] ++ [(out, dec_b_olen nch ns)]))
  by (eapply Permutation_trans; [exact HPERM2 | exact HP]).
assert (Hfrs2' : frames S2 = [(DEC_FCLASS, d_fpos cx)]) by (rewrite Hfrs2; exact Hfrs).
assert (HJ2' : @ajournal rc dec_B_sink_head decodesegsB0 B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx)
                 (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly2 S2 W2 mem2 md2 dec_ev_6f0).
{ rewrite <- c1k_ev. exact HJ2. }
destruct (c1g_keep_acall B LAWS cx ly' S' W' regs' mem' md' dec_ev_5cc res out nch ns W2 mem2
            Hcore HP Hn2 Hpay ltac:(rewrite Hsp in HKEPT; exact HKEPT)) as (KS & KF & KH & KR & KP & KO).
destruct (c1_step B cx ly' S' W' regs' mem' md' dec_ev_5cc res out mode nch ns ly2 S2 W2 regs2 mem2 md2
            dec_ev_6f0 HCELLS HROS HRNE Hrom Hcore Hmem HJ2' Hfrs2'
            ltac:(intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPERM2 | exact Hb])
            (eq_trans (HPRES 8 ltac:(unfold acallee_saved; clear; lia)) eq_refl)
            (eq_trans (HPRES 9 ltac:(unfold acallee_saved; clear; lia)) eq_refl)
            (f_equal bv_unsigned (HPRES 2 ltac:(unfold acallee_saved; clear; lia)))
            (eq_trans (HPRES 3 ltac:(unfold acallee_saved; clear; lia)) eq_refl)
            (eq_trans (HPRES 4 ltac:(unfold acallee_saved; clear; lia)) eq_refl)
            ltac:(intros a Ha _; apply KS; exact Ha) KF KH KR KP) as (Hcore2 & Hmem2).
pose proof Hmem2 as (Hfrs2'' & Hmode2 & Hfsh2 & Hgb2 & S24' & S32' & S40' & S56' & S64' & S72' & S88' & S112').
assert (S80' : dec_b_slot cx (aview decodesegsB0 (w_H W2) mem2) 80 (res + 50)).
{ unfold dec_b_slot in *. rewrite <- Hs80. apply rdword_ext. intros j Hj. apply KS. clear - HN Hj. lia. }
assert (HGB2 : garr8 decodesegsB0 (mrestrict (w_H W2) mem2) out
  (map (fun b : byte => bv_unsigned b) (CDec.braid_out (d_body cx) nch ns))).
{ apply (c1_garr8_kept (w_H W') (w_H W2) mem' mem2 out); [|exact HBR].
  rewrite length_map.
  assert (Hbl' : length (CDec.braid_out (d_body cx) nch ns) = Z.to_nat (3 * nch * ns))
    by (unfold CDec.braid_out; rewrite !length_map, length_seq; reflexivity).
  rewrite Hbl'. intros i Hi. apply KO. clear - HN Hi. lia. }
assert (Hmle2 : mo_le MT (d_S cx) S2 (dec_spent_6f0 MT (d_n cx))).
{ apply (mo_le_mono MT MTL _ _ _ _ (mo_le_trans MT MTL _ _ _ _ _ Hmle HMLE2)).
  exact (c1k_spent MT (d_n cx) nch ns MTL ltac:(clear - HN; lia) ltac:(clear - HN; lia) ltac:(clear - HN; lia)). }
assert (Hmok2 : mo_ok MT S2 (dec_rest_6f0 MT)).
{ apply (mo_ok_step MT MTL S' S2 (dec_crt_cost MT nch ns) (dec_rest_6f0 MT)); [|exact HMLE2].
  apply (mo_ok_le MT MTL S' _ (dec_rest_5cc MT) Hmok).
  exact (c1k_rest MT nch ns MTL ltac:(clear - HN; lia) ltac:(clear - HN; lia) ltac:(clear - HN; lia)). }
assert (HST2 : @c1_st rc B MT cx res out mode nch ns dec_ev_6f0 (dec_spent_6f0 MT (d_n cx))
                 (dec_rest_6f0 MT) fx2 ly2 S2 W2 regs2 mem2 md2).
{ split; [exact Hfrm2|]. split; [exact Hcore2|]. split; [exact HPERM3|]. split; [exact Hres4|].
  split; [exact Hout4|]. split; [exact Hmle2|]. split; [exact Hmok2|]. split; [exact Hmem2 | exact S80']. }
assert (HREG2 : c1_regs cx res out mode nch ns regs2).
{ split; [exact (eq_trans (HPRES 19 ltac:(unfold acallee_saved; clear; lia)) R19)|].
  split; [exact (eq_trans (HPRES 20 ltac:(unfold acallee_saved; clear; lia)) R20)|].
  split; [exact (eq_trans (HPRES 21 ltac:(unfold acallee_saved; clear; lia)) R21)|].
  split; [exact (eq_trans (HPRES 23 ltac:(unfold acallee_saved; clear; lia)) R23)|].
  split; [exact (eq_trans (HPRES 24 ltac:(unfold acallee_saved; clear; lia)) R24)|].
  split; [exact (eq_trans (HPRES 26 ltac:(unfold acallee_saved; clear; lia)) R26)
         | exact (eq_trans (HPRES 27 ltac:(unfold acallee_saved; clear; lia)) R27)]. }
pose proof HREG2 as (R19' & R20' & R21' & R23' & R24' & R26' & R27').
assert (R9' : YK11.getr regs2 9 = w64 (d_sp1 cx))
  by exact (eq_trans (HPRES 9 ltac:(unfold acallee_saved; clear; lia)) R9).
assert (R22' : YK11.getr regs2 22 = w64 out)
  by exact (eq_trans (HPRES 22 ltac:(unfold acallee_saved; clear; lia)) R22).
assert (Hsp2 : spZ regs2 = d_sp1 cx)
  by (etransitivity; [exact (f_equal bv_unsigned (HPRES 2 ltac:(unfold acallee_saved; clear; lia))) | exact Hsp]).
(* ---- the run +0x690 .. +0x6bc ---- *)
set (wf := CInsp.inspect_wf (dec_b_len (d_n cx)) (d_body cx)).
set (fz := ((0 <? nch) && (0 <? ns))%bool).
set (ft := (dec_b_prod nch ns <? 481)).
assert (Ep : c1_pok wf fz ft = CPlain.plain_ok (dec_b_len (d_n cx)) (d_body cx) nch ns)
  by exact (c1g_pok (dec_b_len (d_n cx)) (d_body cx) nch ns Hnch Hns).
assert (Efz : dec_b_fits0 nch ns = (if fz then 1 else 0)) by reflexivity.
assert (G2r : YK11.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 (d_sp1 cx))
  by (apply bv_eq; rewrite (MState.unsigned_lit (d_sp1 cx)) by (clear - HN; lia); exact Hsp2).
assert (G9r : YK11.getr regs2 (Z_to_bv 5 9) = Z_to_bv 64 (d_sp1 cx)) by exact R9'.
assert (G19r : YK11.getr regs2 (Z_to_bv 5 19) = Z_to_bv 64 (if c1_pok wf fz ft then 1 else 0))
  by (rewrite Ep; exact R19').
assert (G20r : YK11.getr regs2 (Z_to_bv 5 20) = Z_to_bv 64 (dec_b_len (d_n cx))) by exact R20'.
assert (G21r : YK11.getr regs2 (Z_to_bv 5 21) = Z_to_bv 64 mode) by exact R21'.
assert (G22r : YK11.getr regs2 (Z_to_bv 5 22) = Z_to_bv 64 out) by exact R22'.
assert (G23r : YK11.getr regs2 (Z_to_bv 5 23) = Z_to_bv 64 nch) by exact R23'.
assert (G24r : YK11.getr regs2 (Z_to_bv 5 24) = Z_to_bv 64 (if fz then 1 else 0))
  by (rewrite <- Efz; exact R24').
assert (G26r : YK11.getr regs2 (Z_to_bv 5 26) = Z_to_bv 64 (dec_b_olen nch ns)) by exact R26'.
assert (RSTK : ExecF.rng (LeafCgKit.RNG_W (world decodesegsB0) (@w_H decodesegsB0) W2) (d_sp1 cx + 24) 72)
  by (apply (c1e_rng_stk B cx ly2 S2 W2 regs2 mem2 md2 dec_ev_6f0);
      [exact Hcore2 | unfold DEC_LLVMF_STK; clear - HN; lia | clear - HN; lia | clear; lia]).
assert (RD40 : ov_read_bytes Img0.rsegs mem2 (Z_to_bv 64 (d_sp1 cx + 40)) 8 =
               Some (Mem.le8 (Z_to_bv 64 res)))
  by (apply (c1e_slot_rd8 B cx ly2 S2 W2 regs2 mem2 md2 dec_ev_6f0);
      [exact Hcore2 | clear; lia | clear; lia | exact S40']).
assert (RD72 : ov_read_bytes Img0.rsegs mem2 (Z_to_bv 64 (d_sp1 cx + 72)) 8 =
               Some (Mem.le8 (Z_to_bv 64 ns))).
{ pose proof (c1e_slot_rd8 B cx ly2 S2 W2 regs2 mem2 md2 dec_ev_6f0 72 (ns mod 2 ^ 64)
    Hcore2 ltac:(clear; lia) ltac:(clear; lia) S72') as X.
  rewrite (Z.mod_small ns (2 ^ 64)) in X by (clear - HN; lia). exact X. }
assert (RD80 : ov_read_bytes Img0.rsegs mem2 (Z_to_bv 64 (d_sp1 cx + 80)) 8 =
               Some (Mem.le8 (Z_to_bv 64 (res + 50))))
  by (apply (c1e_slot_rd8 B cx ly2 S2 W2 regs2 mem2 md2 dec_ev_6f0);
      [exact Hcore2 | clear; lia | clear; lia | exact S80']).
assert (RD88 : ov_read_bytes Img0.rsegs mem2 (Z_to_bv 64 (d_sp1 cx + 88)) 8 =
               Some (Mem.le8 (Z_to_bv 64 out)))
  by (apply (c1e_slot_rd8 B cx ly2 S2 W2 regs2 mem2 md2 dec_ev_6f0);
      [exact Hcore2 | clear; lia | clear; lia | exact S88']).
pose proof (c1_run_acrt (LeafCgKit.RNG_W (world decodesegsB0) (@w_H decodesegsB0) W2)
  (YK11.getr regs2 (Z_to_bv 5 3)) (YK11.getr regs2 (Z_to_bv 5 4)) (YK11.getr regs2 (Z_to_bv 5 8))
  (YK11.getr regs2 (Z_to_bv 5 25)) (@fp_regs fx2) (@fp_csr fx2)
  (d_sp1 cx) res out mode (dec_b_len (d_n cx)) (dec_b_olen nch ns) nch ns wf fz ft
  ltac:(clear - HN; lia) ltac:(clear - HN; lia) ltac:(clear - HN; lia) RSTK mem2 RD40 RD72 RD80 RD88
  (YK11.getr regs2 (Z_to_bv 5 1)) (YK11.getr regs2 (Z_to_bv 5 5)) (YK11.getr regs2 (Z_to_bv 5 6))
  (YK11.getr regs2 (Z_to_bv 5 7)) (YK11.getr regs2 (Z_to_bv 5 28)) (YK11.getr regs2 (Z_to_bv 5 29))
  (YK11.getr regs2 (Z_to_bv 5 30)) (YK11.getr regs2 (Z_to_bv 5 31))
  (YK11.getr regs2 (Z_to_bv 5 10)) (YK11.getr regs2 (Z_to_bv 5 11)) (YK11.getr regs2 (Z_to_bv 5 12))
  (YK11.getr regs2 (Z_to_bv 5 13)) (YK11.getr regs2 (Z_to_bv 5 14)) (YK11.getr regs2 (Z_to_bv 5 15))
  (YK11.getr regs2 (Z_to_bv 5 16)) (YK11.getr regs2 (Z_to_bv 5 17))
  (YK11.getr regs2 (Z_to_bv 5 18)) (YK11.getr regs2 (Z_to_bv 5 27))) as HRUN.
lazymatch type of HRUN with ExecF.evtF _ _ ?P _ =>
  assert (HRUN2 : ExecF.evtF Img0.rsegs (LeafCgKit.RNG_W (world decodesegsB0) (@w_H decodesegsB0) W2) P
                    (@LeafCgKit.ms_of_regs fx2 (DEC_A_LLVMF + 0x690) regs2 mem2)) end.
{ unfold LeafCgKit.ms_of_regs.
  rewrite G2r, G9r, G19r, G20r, G21r, G22r, G23r, G24r, G26r.
  replace (LeafCgKit.w64 (DEC_A_LLVMF + 0x690)) with (Z_to_bv 64 (C1 0x690))
    by (unfold LeafCgKit.w64; f_equal; unfold C1, DEC_A_LLVMF, DecodeBList.AF_LLVMFuzzerTestOneInput; clear; lia).
  exact HRUN. }
clear HRUN.
rewrite R1.
apply (c1f_run W2 regs2 mem2 md2 (DEC_A_LLVMF + 0x690) _ _ HRUN2).
intros ms' md3 (ms0 & HQ & HEQ) HSBM.
destruct HQ as (s2v' & r1' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & a4' & a5' & a6' & a7' & Ems0 & Hr1').
subst ms0.
pose proof (@c1f_ms_shape fx2 _ _ _ ms' HEQ) as Ems'.
pose proof (fun r Hr => c1f_ms_reg _ _ _ _ _ _ _ ms' r HEQ Hr) as GEQ.
(* the journal across the run: it stores nothing *)
assert (HJ3 : @ajournal rc dec_B_sink_head decodesegsB0 B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx)
                (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly2 S2 W2 mem2 md3 dec_ev_6f0).
{ eapply (ajournal_exec decodesegsB0 B LAWS c1f_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem2 md3
    (fun _ => False));
    [exact (proj1 Hcore2) | intros x _; reflexivity | intros x Hx; exact Hx | intros x _; reflexivity
     | exact HSBM | intros a []]. }
assert (Q2 : YK11.getr (ms_regs ms') (Z_to_bv 5 2) = Z_to_bv 64 (d_sp1 cx))
  by exact (GEQ (Z_to_bv 5 2) eq_refl).
assert (Q9 : YK11.getr (ms_regs ms') (Z_to_bv 5 9) = YK11.getr regs2 (Z_to_bv 5 9))
  by (etransitivity; [exact (GEQ (Z_to_bv 5 9) eq_refl) | symmetry; exact G9r]).
assert (Qsp : spZ (ms_regs ms') = spZ regs2).
{ change (bv_unsigned (YK11.getr (ms_regs ms') (Z_to_bv 5 2)) = bv_unsigned (YK11.getr regs2 (Z_to_bv 5 2))).
  rewrite Q2, G2r. reflexivity. }
destruct (c1_step B cx ly2 S2 W2 regs2 mem2 md2 dec_ev_6f0 res out mode nch ns ly2 S2 W2 (ms_regs ms') mem2 md3
            dec_ev_6f0 HCELLS HROS HRNE Hrom Hcore2 Hmem2 HJ3 Hfrs2' (fun b Hb => Hb)
            (GEQ (Z_to_bv 5 8) eq_refl) Q9 Qsp
            (GEQ (Z_to_bv 5 3) eq_refl) (GEQ (Z_to_bv 5 4) eq_refl)
            ltac:(intros a _ _; reflexivity)
            ltac:(intros a Ha; split; [reflexivity | exact (proj2 (KF a Ha))])
            ltac:(intros a _; reflexivity) ltac:(intros i _; reflexivity)
            ltac:(intros i _; reflexivity)) as (Hcore3 & Hmem3).
rewrite Ems'.
(* ---- the call of check_braid at +0x6bc ---- *)
apply (KBRAID cx res out mode nch ns fx2 ly2 S2 W2 (ms_regs ms') mem2 md3 HPRE).
- split; [exact Hfrm2|]. split; [exact Hcore3|]. split; [exact HPERM3|]. split; [exact Hres4|].
  split; [exact Hout4|]. split; [exact Hmle2|]. split; [exact Hmok2|]. split; [exact Hmem3|].
  unfold dec_b_slot in *. rewrite <- S80'. apply rdword_ext. intros j Hj. reflexivity.
- split;
    [ transitivity (Z_to_bv 64 (if c1_pok wf fz ft then 1 else 0));
      [exact (GEQ (Z_to_bv 5 19) eq_refl) | rewrite Ep; reflexivity] |].
  split; [exact (GEQ (Z_to_bv 5 20) eq_refl)|]. split; [exact (GEQ (Z_to_bv 5 21) eq_refl)|].
  split; [exact (GEQ (Z_to_bv 5 23) eq_refl)|].
  split; [rewrite Efz; exact (GEQ (Z_to_bv 5 24) eq_refl)|].
  split; [exact (GEQ (Z_to_bv 5 26) eq_refl) | exact (GEQ (Z_to_bv 5 27) eq_refl)].
- exact Hdok.
- exact HGB2.
- exact (GEQ (Z_to_bv 5 22) eq_refl).
- transitivity r1'; [exact (GEQ (Z_to_bv 5 1) eq_refl)|].
  apply bv_eq. rewrite Hr1'. unfold w64.
  rewrite (MState.unsigned_lit (DEC_A_LLVMF + 0x6c0))
    by (clear; unfold DEC_A_LLVMF, decodeb_text, DecodeBList.AF_LLVMFuzzerTestOneInput; lia).
  unfold C1, DEC_A_LLVMF, decodeb_text, DecodeBList.AF_LLVMFuzzerTestOneInput. clear. lia.
- exact (GEQ (Z_to_bv 5 10) eq_refl).
- exact (GEQ (Z_to_bv 5 11) eq_refl).
- exact (GEQ (Z_to_bv 5 12) eq_refl).
- exact (GEQ (Z_to_bv 5 13) eq_refl).
Qed.
