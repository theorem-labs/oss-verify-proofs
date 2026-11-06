(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 909 of its 980 lines of code are new or changed and 860 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase0TN.v, with its module names changed; 100 of its 139 lines of code are new or changed and 941 lines of the source are left out. *)
(* Case op & 3 = 0 of the B walk of fuzz_boxreg's LLVMFuzzerTestOneInput, piece RF: from C0_RF (0x8056c, range_free
   returned a0 in {0, 1}, base >= 0) the mask trick 0x8056c snez / 0x80570 addiw -1 / 0x80574 or s10 sets the slot
   0x20 to base when a0 <> 0 and -1 when a0 = 0 (want), then j 8 to the cut C0_W (0x80584). No shadow check, no trap. *)
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

Definition C0RF_R20 : YP09.region := c0k_reg 0x20 0x28 0x20 0x28 [].

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


Theorem c0_rf : forall POST i, lx_from B MT POST (C0_W B MT i) -> lx_from B MT POST (C0_RF B MT i).
Proof.
intros POST i HNW cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
destruct HGI as (pos & r & fab & op & nm & bs & HCOM & HNM & HREG & HARG & R19 & S60 & Hok & Hn4 & Hb0 & HRES).
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
remember (lx_env cx fp (ms_regs ms3) []) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply lx_env_img).
assert (ER : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr (ms_regs ms3) rr)
  by (intros nn rr Hnn; rewrite HE; apply lx_env_reg; exact Hnn).
assert (E9 : ew E 9 = w64 (lsp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); exact G9).
assert (UB9 : bv_unsigned (ew E 9) = lsp1 cx) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
assert (HR20 : YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) C0RF_R20).
{ unfold YP09.region_ok, C0RF_R20, c0k_reg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite UB9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). apply HJpres. unfold LX_STK. lia. }
assert (HS : st_ok_pi SEGS VAL E (c0k_ss C0P_RF [C0RF_R20] C0K_SPF) (restrict (w_H W3) ms3)).
{ rewrite HE. rewrite HE in HR20, UB9. apply c0k_seat; try assumption.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; assumption.
  - cbn. tauto.
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
assert (HF0 : c0_from B MT i cx fp k acc ly3 S3 W3 ms3 C0P_RF pos r fab op nm bs) by exact (conj HCOM (conj HNM HARG)).
assert (Hbase : -128 <= base < 128) by (apply LLVMFuzzerTestOneInput_case0.c0_base_range).
assert (E26 : ew E 26 = w64 base) by (rewrite (ER 26%nat 26%bv eq_refl); exact R26).
assert (E10 : ew E 10 = getr (ms_regs ms3) 10) by exact (ER 10%nat 10%bv eq_refl).
paj_run_to_tok RUNTO HS HJ SHOK C0K_BSPAN C0P_W; [c0k_awr cx UB9|].
c0k_kd cx fp W3 [0x20] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] E GEO UB9 KA.
c0k_clean.

pmkst HS.
assert (Hsp : 0 <= lsp1 cx /\ lsp1 cx + 256 <= lsp0 cx <= 2 ^ 47) by lia.
assert (Hnf : nch <= fab) by (destruct Hok as (_ & _ & H); lia).
assert (Hfab : 1 <= fab <= 40) by (rewrite <- HFAB; exact HB2).
pose proof HRES as [(HRF & R10) | (HRF & R10)].
all: [> assert (E10v : ew E 10 = w64 1) by (rewrite E10; exact R10) ..
     | assert (E10v : ew E 10 = w64 0) by (rewrite E10; exact R10) ].
all: prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (8%bv : bv 5) Q8;
  prreg HS (9%bv : bv 5) Q9; prreg HS (18%bv : bv 5) Q18; prreg HS (19%bv : bv 5) Q19; prreg HS (20%bv : bv 5) Q20;
  prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22; prreg HS (23%bv : bv 5) Q23; prreg HS (25%bv : bv 5) Q25;
  prreg HS (26%bv : bv 5) Q26; prreg HS (27%bv : bv 5) Q27.

1: { apply (c0_to_w B MT _ i cx fp k acc ly3 S3 W3 ms3 _ _ _ C0P_RF pos r fab op nm bs base
       [0x20] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] HNW HB HJ HFR HMO HF0 HREG);
  [ repeat apply Forall_cons; try apply Forall_nil; lia
  | left; reflexivity
  | right; left; reflexivity
  | exact KA
  | replace (base mod 2 ^ 64) with base by (symmetry; apply Z.mod_small; destruct HRF as (Hbb & _); lia);
    apply (c0k_word_of_st W3 E _ ms 0%nat 9%nat (lsp1 cx) 32 40 32 40 _ 32 _ base HS eq_refl UB9 ltac:(left; reflexivity));
    [ rewrite (c0k_denot_rf E 10 26 1 base E10v E26 ltac:(lia) ltac:(lia)); reflexivity
    | destruct HRF as (Hbb & _); lia ]
  | exact (c0_slot_keep cx fp W3 [0x20] _ ms3 ms KA Hsp 0x60 nm ltac:(lia) ltac:(lia)
      ltac:(repeat apply Forall_cons; try apply Forall_nil; lia) S60)
  | right; left; rewrite HFAB; split; [exact Hok|]; split; [exact Hn4|]; split; [exact Hb0|];
    left; split; [exact HRF | reflexivity]
  | destruct HRF as (Hbb & _); destruct Hok as (_ & Hkk & _); lia
  | repeat split; c0k_reg_close ER
  | c0k_reg_close ER ]. }

apply (c0_to_w B MT _ i cx fp k acc ly3 S3 W3 ms3 _ _ _ C0P_RF pos r fab op nm bs (-1)
  [0x20] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] HNW HB HJ HFR HMO HF0 HREG);
[ repeat apply Forall_cons; try apply Forall_nil; lia
| left; reflexivity
| right; left; reflexivity
| exact KA
| replace (-1 mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity;
  apply (c0k_word_of_st W3 E _ ms 0%nat 9%nat (lsp1 cx) 32 40 32 40 _ 32 _ (2 ^ 64 - 1) HS eq_refl UB9 ltac:(left; reflexivity));
  [ rewrite (c0k_denot_rf E 10 26 0 base E10v E26 ltac:(lia) ltac:(lia)); reflexivity | lia ]
| exact (c0_slot_keep cx fp W3 [0x20] _ ms3 ms KA Hsp 0x60 nm ltac:(lia) ltac:(lia)
    ltac:(repeat apply Forall_cons; try apply Forall_nil; lia) S60)
| right; left; rewrite HFAB; split; [exact Hok|]; split; [exact Hn4|]; split; [exact Hb0|];
  right; split; [exact HRF | reflexivity]
| lia
| repeat split; c0k_reg_close ER
| c0k_reg_close ER ].
Qed.

End a.
