(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 962 of its 1056 lines of code are new or changed and 837 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase1Want.v, with its module paths and module names changed; 274 of its 348 lines of code are new or changed and 982 lines of the source are left out. *)
(* Case op & 3 = 0 of the B walk of fuzz_boxreg's LLVMFuzzerTestOneInput, the inlined lowest_free loop (base < 0):
   pieces L and LR and the loop induction. C0_L (0x80930, the loop head at the candidate j) sets the four arguments
   and calls range_free (prev, j, nch, fabric) at 0x80940, landing at C0_LR (0x80944). C0_LR decides on a0: nonzero
   (j is free) stores s3 = j into the slot 0x20 and goes to C0_W (want = j, 0x80954 .. 0x8095c); zero steps
   s3 = j + 1 and either loops back to C0_L (j + 1) (0x8094c bne s8, s3) or, at j = fabric - nch, goes to C0_W with
   want = -1 (0x80950). c0_loop closes the loop: from C0_W every C0_L j reaches the post, by induction on 39 - j
   (C0_L needs 0 <= j <= fabric - nch <= 38). No instruction of a piece checks a shadow byte or traps; the call keeps
   every byte the cuts speak about (c0_rf_call, lx_keep_call). *)
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

(* The seat of C0_L / C0_LR: the registers as atoms, no spill region (nothing read or written before the call). *)
Lemma c0l_seat : forall cx fp (W3 : world SEGS) (ms3 : machine_state) pc ex,
  ms_pc_val ms3 = w64 (BASE + pc) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  st_ok_pi SEGS VAL (lx_env cx fp (ms_regs ms3) ex) (c0k_ss pc [] (mkFacts [] [] [])) (restrict (w_H W3) ms3).
Proof.
  intros cx fp W3 ms3 pc ex Hpc Hresv Hpend Hrom Hfregs Hfcsr.
  apply c0k_seat; try assumption; [vm_compute; reflexivity | apply Forall_nil | cbn; tauto | split; [exact I | split; exact I]].
Qed.

Definition C0LR_R20 : YP09.region := c0k_reg 0x20 0x28 0x20 0x28 [(0x20, SLit (2 ^ 64 - 1))].
Definition C0LR_R60 : YP09.region := c0k_reg 0x60 0x68 0 0 [(0x60, SOff 48 0)].


Theorem c0_l : forall POST i j, lx_from B MT POST (C0_LR B MT i j) -> lx_from B MT POST (C0_L B MT i j).
Proof.
intros POST i j HNLR cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
destruct HGI as (pos & r & fab & op & nm & bs & HCOM & HNM & HREG & HARG & S60 & S20 & Hok & Hn4 & Hbneg & Hj & Hlf & R19 & R24).
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
assert (Hfab : 1 <= fab <= 40) by (rewrite <- HFAB; exact HB2).
assert (Hnch2 : 2 <= nch <= 40) by (destruct Hok as (_ & H & _); exact H).
assert (HS : st_ok_pi SEGS VAL E (c0k_ss C0P_L [] (mkFacts [] [] [])) (restrict (w_H W3) ms3))
  by (rewrite HE; apply c0l_seat; assumption).
assert (SHOK : sh_ok SEGS C0K_BX [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
paj_run_tok RUN HS HJ SHOK C0K_BSPAN; [apply awr_ok_nil|].
c0k_kd cx fp W3 (@nil Z) [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] E GEO UB9 KA.
c0k_clean.
pmkst HS.

prreg HS (1%bv : bv 5) CR1. prreg HS (2%bv : bv 5) CR2. prreg HS (3%bv : bv 5) CR3. prreg HS (4%bv : bv 5) CR4.
prreg HS (8%bv : bv 5) CR8. prreg HS (10%bv : bv 5) CR10. prreg HS (11%bv : bv 5) CR11. prreg HS (12%bv : bv 5) CR12.
prreg HS (13%bv : bv 5) CR13.

assert (HX : Forall (fun x => x = 0x20 \/ x = 0x60) (@nil Z)) by apply Forall_nil.
assert (Hsp : 0 <= lsp1 cx /\ lsp1 cx + 256 <= lsp0 cx <= 2 ^ 47) by lia.
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
{ eapply (c0_rf_call B MT HY cx fp k ly3 S3 W3 ms _ [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] j nch fab bs HB HJ HFR).
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
  - rewrite CR11, (ER 19%nat 19%bv eq_refl). exact R19.
  - rewrite CR12, (ER 25%nat 25%bv eq_refl). exact R25.
  - rewrite CR13, (ER 27%nat 27%bv eq_refl). exact R27.
  - lia.
  - lia.
  - lia.
  - exact (c0_saved_keep cx fp W3 _ _ ms3 ms KA HX Hsp HSAVED).
  - exact (c0_shadow_keep cx fp W3 _ _ ms3 ms KA HSHD).
  - exact (c0_prev_keep cx fp W3 _ _ ms3 ms KA bs HPREV).
  - exact HLEN.
  - exact HB1.
  - exact HB2.
  - exact HB3. }
cbv beta. intros W2 c2 _ (regs2 & mem2 & md2 & -> & -> & HJ2 & HP & HK & HRES).
rewrite CR1.

prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
prreg HS (27%bv : bv 5) Q27. prreg HS (19%bv : bv 5) Q19. prreg HS (24%bv : bv 5) Q24.
assert (KALL : c0_kept cx fp W3 [] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] (ms_mem ms3) mem2)
  by (exact (c0_kept_trans _ _ _ _ _ _ _ _ KA (c0_kept_lx _ _ _ _ _ _ _ HK))).
assert (S20' : rdword (aview SEGS (w_H W3) mem2) (lsp1 cx + 0x20) = Some (2 ^ 64 - 1)).
{ apply (c0k_rdword_keep (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) mem2) (lsp1 cx + 0x20) (2 ^ 64 - 1));
  [ intros i0 Hi0; apply KALL; left; split; [lia | apply Forall_nil] | exact S20 ]. }
assert (S60' : rdword (aview SEGS (w_H W3) mem2) (lsp1 cx + 0x60) = Some nm).
{ apply (c0k_rdword_keep (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) mem2) (lsp1 cx + 0x60) nm);
  [ intros i0 Hi0; apply KALL; left; split; [lia | apply Forall_nil] | exact S60 ]. }
assert (HF0 : c0_from B MT i cx fp k acc ly3 S3 W3 ms3 C0P_L pos r fab op nm bs) by exact (conj HCOM (conj HNM HARG)).
apply (c0_to_lr B MT _ i j cx fp k acc ly3 S3 W3 ms3 mem2 md2 regs2 C0P_L pos r fab op nm bs
  (@nil Z) [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] HNLR HB HJ2 HFR HMO HF0 HREG);
[ apply Forall_nil
| left; reflexivity
| right; left; reflexivity
| exact (c0_kept_trans _ _ _ _ _ _ _ _ KA (c0_kept_lx _ _ _ _ _ _ _ HK))
| exact S20' | exact S60' | exact Hok | exact Hn4 | exact Hbneg | exact Hj | exact Hlf | exact HRES
| repeat split; c0k_pres HP; c0k_reg_close ER
| c0k_pres HP; c0k_reg_close ER
| c0k_pres HP; c0k_reg_close ER ].
Qed.


Theorem c0_lr : forall POST i j, lx_from B MT POST (C0_W B MT i) -> lx_from B MT POST (C0_L B MT i (j + 1)) ->
  lx_from B MT POST (C0_LR B MT i j).
Proof.
intros POST i j HNW HNL cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
destruct HGI as (pos & r & fab & op & nm & bs & HCOM & HNM & HREG & HARG & S60 & S20 & Hok & Hn4 & Hbneg & Hj & Hlf & R19 & R24 & HRES).
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
set (ex := [w64 nm]).
remember (lx_env cx fp (ms_regs ms3) ex) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply lx_env_img).
assert (ER : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr (ms_regs ms3) rr)
  by (intros nn rr Hnn; rewrite HE; apply lx_env_reg; exact Hnn).
assert (E9 : ew E 9 = w64 (lsp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); exact G9).
assert (UB9 : bv_unsigned (ew E 9) = lsp1 cx) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
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
assert (Hfab : 1 <= fab <= 40) by (rewrite <- HFAB; exact HB2).
assert (Hnch2 : 2 <= nch <= 40) by (destruct Hok as (_ & H & _); exact H).
assert (E10 : ew E 10 = getr (ms_regs ms3) 10) by exact (ER 10%nat 10%bv eq_refl).
assert (E19 : ew E 19 = w64 j) by (rewrite (ER 19%nat 19%bv eq_refl); exact R19).
assert (E24 : ew E 24 = w64 (fab - nch + 1)) by (rewrite (ER 24%nat 24%bv eq_refl); exact R24).
assert (E48 : ew E 48 = w64 nm) by (rewrite HE; exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia))).
assert (HF0 : c0_from B MT i cx fp k acc ly3 S3 W3 ms3 C0P_LR pos r fab op nm bs) by exact (conj HCOM (conj HNM HARG)).
assert (Hsp : 0 <= lsp1 cx /\ lsp1 cx + 256 <= lsp0 cx <= 2 ^ 47) by lia.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
assert (HR20 : YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) C0LR_R20).
{ unfold YP09.region_ok, C0LR_R20, c0k_reg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite UB9. split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). apply HJpres. unfold LX_STK. lia.
  - apply (lx_slot_chunks_ok cx W3 ms3 E [(0x20, SLit (2 ^ 64 - 1))]).
    unfold lx_slots. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    apply (lx_slot_lit cx W3 ms3 E 0x20 (2 ^ 64 - 1) S20). lia. }
assert (Hnmr : 4096 <= nm < 2 ^ 47).
{ pose proof GEO as (_ & _ & _ & _ & _ & _ & G6 & _). inversion G6 as [|? ? _ G6']. inversion G6' as [|? ? Hq _].
  cbn [fst snd] in Hq. pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range (c0_pl2 (lc_pl cx) pos)). unfold c0_nk in Hq. lia. }
assert (HR60 : YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) C0LR_R60).
{ unfold YP09.region_ok, C0LR_R60, c0k_reg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite UB9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply (lx_slot_chunks_ok cx W3 ms3 E [(0x60, SOff 48 0)]).
  unfold lx_slots. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
  apply (lx_slot_atom cx W3 ms3 E 0x60 48 nm 0); [rewrite Z.add_0_r; exact S60 | exact E48 | lia | lia]. }
assert (HS : st_ok_pi SEGS VAL E (c0k_ss C0P_LR [C0LR_R20; C0LR_R60] C0K_SPF) (restrict (w_H W3) ms3)).
{ rewrite HE. rewrite HE in HR20, HR60, UB9. apply c0k_seat; try assumption.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; assumption.
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint, C0LR_R20, C0LR_R60, c0k_reg.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite UB9. lia.
  - apply (c0k_spf_ok _ (lsp1 cx) UB9); lia. }
assert (SHOK : sh_ok SEGS C0K_BX [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.

paj_run_tok RUN HS HJ SHOK C0K_BSPAN; [c0k_awr cx UB9|].
c0k_kd cx fp W3 [0x20] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] E GEO UB9 KA.
c0k_clean.
assert (Da0 : forall v, getr (ms_regs ms3) 10 = w64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff 10 0) = w64 v) by (intros v Hv Hvr; rewrite lx_sv_SOff0, E10; exact Hv).
destruct HRES as [(HRF & R10) | (HRF & R10)].

1: {
psrr_branch_tok RUN BR HS SHOK C0K_BSPAN.
all: rewrite (c0k_br_ne E (SOff 10 0) (SLit 0) 1 0) in Hc
  by (first [apply (Da0 1 R10); lia | apply c0k_denot_lit | lia]).
2: { cbn [Z.eqb negb] in Hc. discriminate Hc. }
clear Hc.

paj_run_to_tok RUNTO HS HJ SHOK C0K_BSPAN C0P_W; [c0k_awr cx UB9|].
c0k_step cx fp W3 [0x20] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] E GEO UB9 KA.
pmkst HS.

prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
assert (S20' : rdword (aview SEGS (w_H W3) (ms_mem ms0)) (lsp1 cx + 0x20) = Some j).
{ apply (c0k_word_of_st W3 E _ ms0 0%nat 9%nat (lsp1 cx) 32 40 32 40 _ 32 (SOff 19 0) j HS eq_refl UB9 ltac:(left; reflexivity));
  [ rewrite lx_sv_SOff0, E19; reflexivity | lia ]. }
assert (S60' : rdword (aview SEGS (w_H W3) (ms_mem ms0)) (lsp1 cx + 0x60) = Some nm).
{ apply (c0k_word_of_st W3 E _ ms0 1%nat 9%nat (lsp1 cx) 96 104 0 0 _ 96 (SOff 48 0) nm HS eq_refl UB9 ltac:(left; reflexivity));
  [ rewrite lx_sv_SOff0, E48; reflexivity | lia ]. }
apply (c0_to_w B MT _ i cx fp k acc ly3 S3 W3 ms3 _ _ _ C0P_LR pos r fab op nm bs j
  [0x20] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] HNW HB HJ HFR HMO HF0 HREG);
[ repeat apply Forall_cons; try apply Forall_nil; lia
| left; reflexivity
| right; left; reflexivity
| exact KA
| replace (j mod 2 ^ 64) with j by (symmetry; apply Z.mod_small; lia); exact S20'
| exact S60'
| right; right; rewrite HFAB; split; [exact Hok|]; split; [exact Hn4|]; split; [exact Hbneg|];
  right; split; [lia|]; split; [exact HRF | exact Hlf]
| lia
| repeat split; c0k_reg_close ER
| c0k_reg_close ER ].

}
psrr_branch_tok RUN BR HS SHOK C0K_BSPAN.
all: rewrite (c0k_br_ne E (SOff 10 0) (SLit 0) 0 0) in Hc
  by (first [apply (Da0 0 R10); lia | apply c0k_denot_lit | lia]).
1: { cbn [Z.eqb negb] in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS HJ SHOK C0K_BSPAN; [c0k_awr cx UB9|].
c0k_step cx fp W3 [0x20] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] E GEO UB9 KA.
psrr_branch_tok RUN BR HS SHOK C0K_BSPAN.
all: rewrite (c0k_br_ne E (SOff 24 0) (SAluw ALU_ADD (SOff 19 0) (SLit 1)) (fab - nch + 1) (j + 1)) in Hc;
  [ | apply c0k_atom0; [exact E24 | lia]
    | apply (c0k_addw E (SOff 19 0) (SLit 1) j 1); [apply c0k_atom0; [exact E19 | lia] | reflexivity | lia | lia | lia]
    | lia | lia ].

1: { apply negb_true_iff, Z.eqb_neq in Hc.
paj_run_to_tok RUNTO HS HJ SHOK C0K_BSPAN C0P_L; [c0k_awr cx UB9|].
c0k_step cx fp W3 [0x20] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] E GEO UB9 KA.
pmkst HS.

c0k_rawreg HS (19%bv : bv 5) Q19r.
rewrite (c0k_addw E (SOff 19 0) (SLit 1) j 1) in Q19r;
  [ | apply c0k_atom0; [exact E19 | lia] | reflexivity | lia | lia | lia ].
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27. prreg HS (24%bv : bv 5) Q24.
assert (S20' : rdword (aview SEGS (w_H W3) (ms_mem ms1)) (lsp1 cx + 0x20) = Some (2 ^ 64 - 1)).
{ apply (c0k_word_of_st W3 E _ ms1 0%nat 9%nat (lsp1 cx) 32 40 32 40 _ 32 (SLit (2 ^ 64 - 1)) (2 ^ 64 - 1) HS eq_refl UB9 ltac:(left; reflexivity));
  [ reflexivity | lia ]. }
assert (S60' : rdword (aview SEGS (w_H W3) (ms_mem ms1)) (lsp1 cx + 0x60) = Some nm).
{ apply (c0k_word_of_st W3 E _ ms1 1%nat 9%nat (lsp1 cx) 96 104 0 0 _ 96 (SOff 48 0) nm HS eq_refl UB9 ltac:(left; reflexivity));
  [ rewrite lx_sv_SOff0, E48; reflexivity | lia ]. }
apply (c0_to_l B MT _ i (j + 1) cx fp k acc ly3 S3 W3 ms3 _ _ _ C0P_LR pos r fab op nm bs
  [0x20] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] HNL HB HJ HFR HMO HF0 HREG);
[ repeat apply Forall_cons; try apply Forall_nil; lia
| left; reflexivity
| right; left; reflexivity
| exact KA
| exact S20' | exact S60' | exact Hok | exact Hn4 | exact Hbneg | lia
| intros b0 Hb0; destruct (Z.eq_dec b0 j) as [-> | Hne]; [exact HRF | apply Hlf; lia]
| repeat split; c0k_reg_close ER
| rewrite Q19r; reflexivity
| c0k_reg_close ER ]. }

apply negb_false_iff, Z.eqb_eq in Hc.
assert (Hjend : j = fab - nch) by lia.
paj_run_to_tok RUNTO HS HJ SHOK C0K_BSPAN C0P_W; [c0k_awr cx UB9|].
c0k_step cx fp W3 [0x20] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] E GEO UB9 KA.
pmkst HS.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
assert (S20' : rdword (aview SEGS (w_H W3) (ms_mem ms1)) (lsp1 cx + 0x20) = Some (2 ^ 64 - 1)).
{ apply (c0k_word_of_st W3 E _ ms1 0%nat 9%nat (lsp1 cx) 32 40 32 40 _ 32 (SLit (2 ^ 64 - 1)) (2 ^ 64 - 1) HS eq_refl UB9 ltac:(left; reflexivity));
  [ reflexivity | lia ]. }
assert (S60' : rdword (aview SEGS (w_H W3) (ms_mem ms1)) (lsp1 cx + 0x60) = Some nm).
{ apply (c0k_word_of_st W3 E _ ms1 1%nat 9%nat (lsp1 cx) 96 104 0 0 _ 96 (SOff 48 0) nm HS eq_refl UB9 ltac:(left; reflexivity));
  [ rewrite lx_sv_SOff0, E48; reflexivity | lia ]. }
apply (c0_to_w B MT _ i cx fp k acc ly3 S3 W3 ms3 _ _ _ C0P_LR pos r fab op nm bs (-1)
  [0x20] [(r, LX_REG); (nm, c0_nk (lc_pl cx) pos + 1)] HNW HB HJ HFR HMO HF0 HREG);
[ repeat apply Forall_cons; try apply Forall_nil; lia
| left; reflexivity
| right; left; reflexivity
| exact KA
| replace (-1 mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity; exact S20'
| exact S60'
| right; right; rewrite HFAB; split; [exact Hok|]; split; [exact Hn4|]; split; [exact Hbneg|];
  left; split; [reflexivity|]; intros b0 Hb0; destruct (Z.eq_dec b0 j) as [-> | Hne]; [exact HRF | apply Hlf; lia]
| lia
| repeat split; c0k_reg_close ER
| c0k_reg_close ER ].
Qed.


Lemma c0_L_past : forall POST i j, (39 <= j) -> lx_from B MT POST (C0_L B MT i j).
Proof.
  intros POST i j Hj cx fp k acc ly3 S3 W3 ms3 md3 _ _ _ _ HGI.
  destruct HGI as (pos & r & fab & op & nm & bs & HCOM & HNM & HREG & HARG & S60 & S20 & Hok & Hn4 & Hbneg & Hjr & _).
  exfalso. pose proof HCOM as (_ & _ & _ & HINV & HFAB & _). pose proof HINV as ((_ & _ & HB2 & _) & _).
  unfold Boxreg.boxreg_B2 in HB2. rewrite HFAB in HB2. destruct Hok as (_ & Hk2 & _). lia.
Qed.

Theorem c0_loop : forall POST i, lx_from B MT POST (C0_W B MT i) -> forall j, lx_from B MT POST (C0_L B MT i j).
Proof.
  intros POST i HNW.
  assert (H : forall (n : nat) (j : Z), (Z.to_nat (39 - j) <= n)%nat -> lx_from B MT POST (C0_L B MT i j)).
  { induction n as [|n IHn]; intros j Hj.
    - apply c0_L_past. assert (Z.to_nat (39 - j) = 0)%nat by lia. lia.
    - destruct (Z_lt_le_dec j 39) as [Hlt | Hge]; [|apply c0_L_past; lia].
      apply c0_l. apply c0_lr; [exact HNW|]. apply IHn. lia. }
  intros j. apply (H (Z.to_nat (39 - j)) j). lia.
Qed.

End a.
