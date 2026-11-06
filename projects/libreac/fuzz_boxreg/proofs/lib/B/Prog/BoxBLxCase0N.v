(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 962 of its 1056 lines of code are new or changed and 837 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase1Want.v, with its module paths and module names changed; 212 of its 272 lines of code are new or changed and 996 lines of the source are left out. *)
(* Case op & 3 = 0 of the B walk of fuzz_boxreg's LLVMFuzzerTestOneInput, piece N: from C0_N (0x80524, read_name
   returned the name) through the width checks of legal_width and the room check (0x8052c .. 0x80554) to the cut C0_W
   (0x80584, want = -1, when a check fails), to the call of range_free (prev, base, nch, fabric) at 0x80568 and its
   return C0_RF (0x8056c, base >= 0), or to the head of the inlined lowest_free loop C0_L 0 (0x80930, base < 0).
   The branches: 0x8052c blt fab, nch; 0x80538 bltu 38, nch - 2; 0x80540 bnez nch & 1; 0x8054c blt 4, n (each a
   failed width or room test, to 0x8057c), 0x80554 bltz (base << 56) (the slot 0x50). No instruction of the piece
   checks a shadow byte or traps. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit BoxBRangeFree.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxCase0Defs BoxBLxCase0Kit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd read_name_c range_free_c
  lowest_free_c reac_boxreg_declare_c LLVMFuzzerTestOneInput_case0 LLVMFuzzerTestOneInput_rn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition C0N_R20 : YP09.region := c0k_reg 0x20 0x28 0x20 0x28 [].
Definition C0N_R48 : YP09.region := c0k_reg 0x48 0x58 0 0 [(0x48, SOff 48 0); (0x50, SOff 49 0)].
Definition C0N_R60 : YP09.region := c0k_reg 0x60 0x68 0x60 0x68 [].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HY : lx_hyps B MT.
Let LAWS := lh_laws B MT HY.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNTO := paj_run_to B LAWS.

(* A width test failed: 0x8057c a0 = -1, 0x80580 the slot 0x20 = -1, the cut W with want = -1. *)
Ltac c0n_fail HNW HB HJ HFR HMO HF0 HREG HS SHOK KA GEO UB9 E10 ER tac :=
  lazymatch type of HF0 with c0_from _ _ ?i ?cx ?fp ?k ?acc ?ly3 ?S3 ?W3 ?ms3 ?pc0 ?pos ?r ?fab ?op ?nm ?bs =>
  lazymatch type of UB9 with bv_unsigned (ew ?E 9) = _ =>
  paj_run_to_tok RUNTO HS HJ SHOK C0K_BSPAN C0P_W; [c0k_awr cx UB9|];
  c0k_step cx fp W3 [0x20; 0x60] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] E GEO UB9 KA;
  pmkst HS;
  let Q2 := fresh "Q" in let Q3 := fresh "Q" in let Q4 := fresh "Q" in let Q8 := fresh "Q" in
  let Q9 := fresh "Q" in let Q18 := fresh "Q" in let Q19 := fresh "Q" in let Q20 := fresh "Q" in
  let Q21 := fresh "Q" in let Q22 := fresh "Q" in let Q23 := fresh "Q" in let Q25 := fresh "Q" in
  let Q26 := fresh "Q" in let Q27 := fresh "Q" in
  prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (8%bv : bv 5) Q8;
  prreg HS (9%bv : bv 5) Q9; prreg HS (18%bv : bv 5) Q18; prreg HS (19%bv : bv 5) Q19; prreg HS (20%bv : bv 5) Q20;
  prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22; prreg HS (23%bv : bv 5) Q23; prreg HS (25%bv : bv 5) Q25;
  prreg HS (26%bv : bv 5) Q26; prreg HS (27%bv : bv 5) Q27;
  apply (c0_to_w B MT _ i cx fp k acc ly3 S3 W3 ms3 _ _ _ pc0 pos r fab op nm bs (-1)
    [0x20; 0x60] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] HNW HB HJ HFR HMO HF0 HREG);
  [ repeat apply Forall_cons; try apply Forall_nil; lia
  | left; reflexivity
  | right; left; reflexivity
  | exact KA
  | apply (lx_word_of_ss W3 _ E _ 0%nat 9%nat (lsp1 cx) 32 40 32 40 _ 32 (SLit (2 ^ 64 - 1)) (2 ^ 64 - 1) HS eq_refl UB9
      ltac:(left; reflexivity)); [reflexivity | lia]
  | apply (lx_word_of_ss W3 _ E _ 2%nat 9%nat (lsp1 cx) 96 104 96 104 _ 96 (SOff 10 0) nm HS eq_refl UB9
      ltac:(left; reflexivity)); [apply c0k_atom0; [exact E10 | lia] | lia]
  | left; split; [|reflexivity]; tac
  | lia
  | repeat split; c0k_reg_close ER
  | c0k_reg_close ER ]
  end end.

Theorem c0_n : forall POST i, lx_from B MT POST (C0_W B MT i) -> lx_from B MT POST (C0_RF B MT i) ->
  lx_from B MT POST (C0_L B MT i 0) -> lx_from B MT POST (C0_N B MT i).
Proof.
intros POST i HNW HNRF HNL cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
destruct HGI as (pos & r & fab & op & nm & bs & HCOM & HNM & HREG & HARG & R10).
pose proof HCOM as (HBODY & Hi64 & HPREV & HINV & HFAB & Hpos & Hop & Hop3 & HSLL & S58 & S48 & R20 & R21 & R27).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSHD & HFLAG
  & HS10 & HS18 & HS80 & HINP).
pose proof HARG as (R23 & R25 & R26 & S50).
pose proof HREGS as (G2 & G8 & G9 & G3 & G4 & G18 & G22).
pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
pose proof HINV as ((HLEN & HB1 & HB2 & HB3 & _) & _).
set (nch := c0_nchv (lc_pl cx) pos) in *.
set (base := c0_basev (lc_pl cx) pos) in *.
set (ex := [w64 (Boxreg.bx_n bs); w64 ((base * 2 ^ 56) mod 2 ^ 64)]).
remember (lx_env cx fp (ms_regs ms3) ex) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply lx_env_img).
assert (ER : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr (ms_regs ms3) rr)
  by (intros nn rr Hnn; rewrite HE; apply lx_env_reg; exact Hnn).
assert (E9 : ew E 9 = w64 (lsp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); exact G9).
assert (E48 : ew E 48 = w64 (Boxreg.bx_n bs)) by (rewrite HE; exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia))).
assert (E49 : ew E 49 = w64 ((base * 2 ^ 56) mod 2 ^ 64)) by (rewrite HE; exact (lx_env_ex cx fp (ms_regs ms3) ex 1 ltac:(lia))).
assert (UB9 : bv_unsigned (ew E 9) = lsp1 cx) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
assert (Hn5 : 0 <= Boxreg.bx_n bs <= 5) by exact HB1.
assert (HR20 : YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) C0N_R20).
{ unfold YP09.region_ok, C0N_R20, c0k_reg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite UB9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). apply HJpres. unfold LX_STK. lia. }
assert (HR60 : YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) C0N_R60).
{ unfold YP09.region_ok, C0N_R60, c0k_reg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite UB9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). apply HJpres. unfold LX_STK. lia. }
assert (HR48 : YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) C0N_R48).
{ unfold YP09.region_ok, C0N_R48, c0k_reg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite UB9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply (lx_slot_chunks_ok cx W3 ms3 E). unfold lx_slots. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - apply (lx_slot_atom cx W3 ms3 E 0x48 48 (Boxreg.bx_n bs) 0); [rewrite Z.add_0_r; exact S48 | exact E48 | lia | lia].
  - pose proof (Z.mod_pos_bound (base * 2 ^ 56) (2 ^ 64) ltac:(lia)).
    apply (lx_slot_atom cx W3 ms3 E 0x50 49 ((base * 2 ^ 56) mod 2 ^ 64) 0); [rewrite Z.add_0_r; exact S50 | exact E49 | lia | lia]. }
assert (HS : st_ok_pi SEGS VAL E (c0k_ss C0P_N [C0N_R20; C0N_R48; C0N_R60] C0K_SPF) (restrict (w_H W3) ms3)).
{ rewrite HE. rewrite HE in HR20, HR48, HR60, UB9. apply c0k_seat; try assumption.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; assumption.
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint, C0N_R20, C0N_R48, C0N_R60, c0k_reg.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite UB9. lia.
  - apply (c0k_spf_ok _ (lsp1 cx) UB9); lia. }
assert (SHOK : sh_ok SEGS C0K_BX [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.

pose proof HNM as (Hk & Hacc & HBLK & Haf & Hnm4 & Hname & Hcur).
assert (GEO : c0_geo cx fp [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)]).
{ apply (c0_geo_of B MT cx fp W3 ms3 ly3 S3 md3 k _ HB LAWS HJ HFR).
  - intros pp nn Hin. rewrite HBLK. apply in_or_app. left. exact Hin.
  - pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range (c0_pl2 (lc_pl cx) pos)) as Hnk. unfold c0_nk.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    + exists LX_REG. split; [rewrite HBLK; apply in_or_app; right; left; reflexivity|].
      pose proof (req_size_pos LX_REG ltac:(unfold LX_REG; lia)) as [_ Hq]. unfold LX_REG in *. lia.
    + exists (read_name_c.rn_k (c0_pl2 (lc_pl cx) pos) + 1).
      split; [rewrite HBLK; apply in_or_app; right; right; left; reflexivity|].
      pose proof (req_size_pos (read_name_c.rn_k (c0_pl2 (lc_pl cx) pos) + 1) ltac:(lia)) as [_ Hq]. lia. }
assert (Hnmr : 4096 <= nm < 2 ^ 47).
{ pose proof GEO as (_ & _ & _ & _ & _ & _ & G6 & _). inversion G6 as [|? ? _ G6']. inversion G6' as [|? ? Hq _].
  cbn [fst snd] in Hq. pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range (c0_pl2 (lc_pl cx) pos)). unfold c0_nk in Hq. lia. }
assert (E10 : ew E 10 = w64 nm) by (rewrite (ER 10%nat 10%bv eq_refl); exact R10).
assert (HF0 : c0_from B MT i cx fp k acc ly3 S3 W3 ms3 C0P_N pos r fab op nm bs) by exact (conj HCOM (conj HNM HARG)).
assert (Hfab : 1 <= fab <= 40) by (rewrite <- HFAB; exact HB2).
assert (Hnch : 0 <= nch < 256) by (apply LLVMFuzzerTestOneInput_case0.c0_nch_range).
assert (Hbase : -128 <= base < 128) by (apply LLVMFuzzerTestOneInput_case0.c0_base_range).
assert (E25 : ew E 25 = w64 nch) by (rewrite (ER 25%nat 25%bv eq_refl); exact R25).
assert (E26 : ew E 26 = w64 base) by (rewrite (ER 26%nat 26%bv eq_refl); exact R26).
assert (E27 : ew E 27 = w64 fab) by (rewrite (ER 27%nat 27%bv eq_refl); exact R27).

paj_run_tok RUN HS HJ SHOK C0K_BSPAN; [c0k_awr cx UB9|].
c0k_kd cx fp W3 [0x20; 0x60] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] E GEO UB9 KA.
c0k_clean.
(* 0x8052c blt s11, s9: fab < nch *)
psrr_branch_tok RUN BR HS SHOK C0K_BSPAN.
all: rewrite (c0k_br_lt E (SOff 27 0) (SOff 25 0) fab nch) in Hc by (first [apply c0k_atom0; [assumption | lia] | lia]).
1: { c0n_fail HNW HB HJ HFR HMO HF0 HREG HS SHOK KA GEO UB9 E10 ER
       ltac:(intros (Hok & _); rewrite HFAB in Hok; destruct Hok as (_ & _ & Hle); apply Z.ltb_lt in Hc; unfold nch in Hc; lia). }

assert (Hfn : nch <= fab) by (apply Z.ltb_ge in Hc; lia). clear Hc.
(* 0x80538 bltu 38, nch - 2 *)
paj_run_tok RUN HS HJ SHOK C0K_BSPAN; [c0k_awr cx UB9|].
c0k_step cx fp W3 [0x20; 0x60] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] E GEO UB9 KA.
psrr_branch_tok RUN BR HS SHOK C0K_BSPAN.
all: rewrite branch_ltu_U, U_lit, (c0k_U_off E 25 nch (-2) E25), c0k_wtest in Hc by lia.

1: { c0n_fail HNW HB HJ HFR HMO HF0 HREG HS SHOK KA GEO UB9 E10 ER
       ltac:(intros (Hok & _); rewrite HFAB in Hok; destruct Hok as (_ & Hk40 & _);
             apply negb_true_iff, andb_false_iff in Hc; destruct Hc as [Hc | Hc]; apply Z.leb_gt in Hc; unfold nch in Hc; lia). }
assert (Hn40 : 2 <= nch <= 40) by (apply negb_false_iff, andb_true_iff in Hc; destruct Hc as [Hc1 Hc2]; apply Z.leb_le in Hc1, Hc2; lia). clear Hc.
(* 0x80540 bnez (s9 & 1) *)
paj_run_tok RUN HS HJ SHOK C0K_BSPAN; [c0k_awr cx UB9|].
c0k_step cx fp W3 [0x20; 0x60] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] E GEO UB9 KA.
psrr_branch_tok RUN BR HS SHOK C0K_BSPAN.

all: rewrite branch_ne_U, U_and_lit, (U_atom E 25 nch E25), U_lit, c0k_land1 in Hc by lia.
1: { c0n_fail HNW HB HJ HFR HMO HF0 HREG HS SHOK KA GEO UB9 E10 ER
       ltac:(intros (Hok & _); rewrite HFAB in Hok; destruct Hok as (Hev & _ & _);
             unfold nch in Hc; rewrite Hev in Hc; discriminate Hc). }
assert (Hev : Z.even nch = true) by (destruct (Z.even nch); [reflexivity | discriminate Hc]). clear Hc.
(* 0x8054c blt 4, n_before *)
paj_run_tok RUN HS HJ SHOK C0K_BSPAN; [c0k_awr cx UB9|].
c0k_step cx fp W3 [0x20; 0x60] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] E GEO UB9 KA.
psrr_branch_tok RUN BR HS SHOK C0K_BSPAN.

all: rewrite (c0k_br_lt E (SLit 4) (SOff 48 0) 4 (Boxreg.bx_n bs)) in Hc
  by (first [apply c0k_denot_lit | apply c0k_atom0; [assumption | lia] | lia]).
1: { c0n_fail HNW HB HJ HFR HMO HF0 HREG HS SHOK KA GEO UB9 E10 ER
       ltac:(intros (_ & Hn5'); apply Z.ltb_lt in Hc; lia). }
assert (Hn4 : Boxreg.bx_n bs < 5) by (apply Z.ltb_ge in Hc; lia). clear Hc.
assert (Hok : reac_boxreg_declare_c.box_width_ok nch fab) by (split; [exact Hev | lia]).
(* 0x80554 bltz (base << 56) *)
paj_run_tok RUN HS HJ SHOK C0K_BSPAN; [c0k_awr cx UB9|].
c0k_step cx fp W3 [0x20; 0x60] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] E GEO UB9 KA.
psrr_branch_tok RUN BR HS SHOK C0K_BSPAN.

all: rewrite lx_sv_SOff0, E49, c0k_w64_mod, c0k_denot_lit in Hc; cbn [branch_taken] in Hc;
  unfold w64 in Hc; rewrite (LLVMFuzzerTestOneInput_case0.c0_lts56 base Hbase) in Hc.

1: { apply Z.ltb_lt in Hc.
paj_run_to_tok RUNTO HS HJ SHOK C0K_BSPAN C0P_L; [c0k_awr cx UB9|].
c0k_step cx fp W3 [0x20; 0x60] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] E GEO UB9 KA.
pmkst HS.
c0k_rawreg HS (24%bv : bv 5) Q24.

change (SAluw ALU_ADD (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SAlu ALU_ADD (SMd M_MUL (SOff 25 0) (SLit (-1))) (SOff 27 0)))) (SAlu ALU_ADD (SMd M_MUL (SOff 25 0) (SLit (-1))) (SOff 27 0))) (SLit 1))
  with (c0k_s8 25 27) in Q24.
rewrite (c0k_denot_s8 E 25 27 nch fab E25 E27 Hn40 ltac:(lia)) in Q24.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
apply (c0_to_l B MT _ i 0 cx fp k acc ly3 S3 W3 ms3 _ _ _ C0P_N pos r fab op nm bs
  [0x20; 0x60] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] HNL HB HJ HFR HMO HF0 HREG);
[ repeat apply Forall_cons; try apply Forall_nil; lia
| left; reflexivity
| right; left; reflexivity
| exact KA
| apply (lx_word_of_ss W3 _ E _ 0%nat 9%nat (lsp1 cx) 32 40 32 40 _ 32 (SLit (2 ^ 64 - 1)) (2 ^ 64 - 1) HS eq_refl UB9
    ltac:(left; reflexivity)); [reflexivity | lia]
| apply (lx_word_of_ss W3 _ E _ 2%nat 9%nat (lsp1 cx) 96 104 96 104 _ 96 (SOff 10 0) nm HS eq_refl UB9
    ltac:(left; reflexivity)); [apply c0k_atom0; [exact E10 | lia] | lia]
| exact Hok | exact Hn4 | exact Hc | lia | intros b0 Hb0; lia
| repeat split; c0k_reg_close ER
| c0k_reg_close ER
| rewrite Q24; reflexivity ]. }

assert (Hb0 : 0 <= base) by (apply Z.ltb_ge in Hc; lia). clear Hc.
paj_run_tok RUN HS HJ SHOK C0K_BSPAN; [c0k_awr cx UB9|].
c0k_step cx fp W3 [0x20; 0x60] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] E GEO UB9 KA.
pmkst HS.

prreg HS (1%bv : bv 5) CR1. prreg HS (2%bv : bv 5) CR2. prreg HS (3%bv : bv 5) CR3. prreg HS (4%bv : bv 5) CR4.
prreg HS (8%bv : bv 5) CR8. prreg HS (10%bv : bv 5) CR10. prreg HS (11%bv : bv 5) CR11. prreg HS (12%bv : bv 5) CR12.
prreg HS (13%bv : bv 5) CR13.

prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
assert (HX : Forall (fun x => x = 0x20 \/ x = 0x60) [0x20; 0x60]) by (repeat apply Forall_cons; try apply Forall_nil; lia).
assert (Hsp : 0 <= lsp1 cx /\ lsp1 cx + 256 <= lsp0 cx <= 2 ^ 47) by lia.
assert (S60 : rdword (aview SEGS (w_H W3) (ms_mem ms1)) (lsp1 cx + 0x60) = Some nm).
{ apply (c0k_word_of_st W3 E _ ms1 2%nat 9%nat (lsp1 cx) 96 104 96 104 _ 96 (SOff 10 0) nm HS eq_refl UB9
    ltac:(left; reflexivity)); [apply c0k_atom0; [exact E10 | lia] | lia]. }
assert (HRS : Forall (fun q => exists n, In (fst q, n) (ablocks B ly3 S3) /\ 0 <= snd q <= req_size n)
          [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)]).
{ pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range (c0_pl2 (lc_pl cx) pos)) as Hnk. unfold c0_nk.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
  + exists LX_REG. split; [rewrite HBLK; apply in_or_app; right; left; reflexivity|].
    pose proof (req_size_pos LX_REG ltac:(unfold LX_REG; lia)) as [_ Hq]. unfold LX_REG in *. lia.
  + exists (read_name_c.rn_k (c0_pl2 (lc_pl cx) pos) + 1).
    split; [rewrite HBLK; apply in_or_app; right; right; left; reflexivity|].
    pose proof (req_size_pos (read_name_c.rn_k (c0_pl2 (lc_pl cx) pos) + 1) ltac:(lia)) as [_ Hq]. lia. }
eapply SRr_bind.
{ eapply (c0_rf_call B MT HY cx fp k ly3 S3 W3 ms1 _ [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] base nch fab bs HB HJ HFR).
  - intros pp nn Hin. rewrite HBLK. apply in_or_app. left. exact Hin.
  - exact HRS.
  - rewrite CR2, (ER 2%nat 2%bv eq_refl). exact G2.
  - rewrite CR8, (ER 8%nat 8%bv eq_refl). exact G8.
  - rewrite CR3, (ER 3%nat 3%bv eq_refl). exact G3.
  - rewrite CR4, (ER 4%nat 4%bv eq_refl). exact G4.
  - rewrite CR1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite CR1. pose proof pa_base_lo. pose proof (pa_B_ok (L := boxb_listing)) as (HB0 & HB1b & _).
    rewrite unsigned_lit_small by lia. lia.
  - rewrite CR10, (ER 21%nat 21%bv eq_refl). exact R21.
  - rewrite CR11, (ER 26%nat 26%bv eq_refl). exact R26.
  - rewrite CR12, (ER 25%nat 25%bv eq_refl). exact R25.
  - rewrite CR13, (ER 27%nat 27%bv eq_refl). exact R27.
  - lia.
  - lia.
  - lia.
  - exact (c0_saved_keep cx fp W3 _ _ ms3 ms1 KA HX Hsp HSAVED).
  - exact (c0_shadow_keep cx fp W3 _ _ ms3 ms1 KA HSHD).
  - exact (c0_prev_keep cx fp W3 _ _ ms3 ms1 KA bs HPREV).
  - exact HLEN.
  - exact HB1.
  - exact HB2.
  - exact HB3. }
cbv beta. intros W2 c2 _ (regs2 & mem2 & md2 & -> & -> & HJ2 & HP & HK & HRES).
rewrite CR1.

apply (c0_to_rf B MT _ i cx fp k acc ly3 S3 W3 ms3 mem2 md2 regs2 C0P_N pos r fab op nm bs
  [0x20; 0x60] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] HNRF HB HJ2 HFR HMO HF0 HREG);
[ exact HX
| left; reflexivity
| right; left; reflexivity
| exact (c0_kept_trans _ _ _ _ _ _ _ _ KA (c0_kept_lx _ _ _ _ _ _ _ HK))
| apply (lx_rdword_keep cx fp W3 _ (ms_mem ms1) mem2 (lsp1 cx + 0x60) nm HK); [intros i0 Hi0; left; lia | exact S60]
| exact Hok | exact Hn4 | exact Hb0 | exact HRES
| repeat split; c0k_pres HP; c0k_reg_close ER
| c0k_pres HP; rewrite Q19; exact E10 ].
Qed.

End a.
