(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YI08.v:162-174, 176-180;
   projects/cgif/cgif_file_fuzzer/proofs/lib/YN13.v:121-125; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC1n.v:201-203, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D1.v, with its module paths, module names and addresses changed; 317 of its 395 lines of code are new or changed and 5987 lines of the source are left out. *)
(* Phase 1 of segment D1 of LLVMFuzzerTestOneInput's ASan walk (0x80b20..0x80bc8 and the payload copy's malloc):
   the record header (fuzz_u16, fuzz_u8, fuzz_take: three checked input loads, the address bias of pick_addr, the
   length), then malloc(k). d1_ph1 takes inv_rec's state (D1ctx) to the running state D1S at 0x80bcc with P1.
   Every abort branch is decided by the plain model (lib/Prog/SlotModel.v); every __asan_report branch of the
   three loads is refuted by the input block's shadow (the token engine), so no path reaches a report call.
   LLVMFuzzerTestOneInput_D1cut.v holds the predicates; LLVMFuzzerTestOneInput_D1.v composes the phases. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YK1g YK0w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv reac_identity_ingest.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import LLVMFuzzerTestOneInput_D1cut.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec reac_identity_ingest_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; the shadow arithmetic here needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- Ph1's symbolic state at 0x80b20 ---------------------------------------------------------------------------- *)
(* Atoms: 32 the shadow base, 33 + j the input byte at the cursor + j (j < 3). The machine frame (base s1, atom 9)
   is read at mf+176 only; the input (base s10, atom 26) holds the h = min(left, 3) header bytes. With h < 3 the
   remaining length x18 is pinned to the literal h, so the engine decides 0x80b20 / 0x80b40 / 0x80bac. *)
Definition p1_mf : YP09.region := YP09.mkRegion (Some 9%nat) 176 184 176 176 [YP09.mkChunk 176 (CVal 8 (SOff 32 0))].
Definition p1_chunk (j : nat) : YP09.chunk := YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (33 + j) 0)).
Definition p1_in (h : nat) : YP09.region := YP09.mkRegion (Some 26%nat) 0 (Z.of_nat h) 0 0 (map p1_chunk (seq 0 h)).
Definition p1_left (h : nat) : afact := if (h <? 3)%nat then mkAF (Z.of_nat h) (Z.of_nat h) 0 else mkAF 3 (2 ^ 26 - 1) 0.
Definition p1_facts (h : nat) : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, p1_left h);
           (26%nat, mkAF 4096 (2 ^ 47 - 16) 0); (32%nat, mkAF d1_SB d1_SB 0);
           (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0)] [] [].
Definition p1_SH (h : nat) : list shent := if (h =? 0)%nat then [] else [mkSHE 26 0 (Z.of_nat h)].
Definition p1_regs (h : nat) : list sv := if (h <? 3)%nat then sr_set sr_atoms 18%bv (SLit (Z.of_nat h)) else sr_atoms.
Definition ss_p1 (h : nat) : sstate :=
  mkSS 0x414 (p1_regs h) (p1_mf :: (if (h =? 0)%nat then [] else [p1_in h])) None (p1_facts h).
Definition p1_extra (inp : list byte) (c : Z) : list word :=
  map (Z_to_bv 64) [d1_SB; SlotModel.inb inp c; SlotModel.inb inp (c + 1); SlotModel.inb inp (c + 2)].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
(* What this segment takes, each with the name and type the contract's Section gives it (LLVMFuzzerTestOneInput.v). *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis HLIVE : LIVE_LLVMF <= LIVE_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA IS___asan_memcpy).
(* The allocator call traces (LLVMFuzzerTestOneInput.v, the contract's text). *)
Hypothesis HUMM : forall c, In c (LLVMF_MALLOC_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_malloc_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
Hypothesis HUMF : forall c, In c (LLVMF_FREE_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_free_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
(* cgif ACfh.v:162-164 *)
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
(* the program callee (lib/A/Prog/reac_identity_ingest.v) *)
Hypothesis HING : treac_identity_ingest_spec B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
(* the cut file's predicates and facts, with this Section's parameters *)
#[local] Notation CTX := (D1ctx B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation RUNS := (D1S B MT LLVMF_STK).
#[local] Notation NUMS := (d1_nums B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS HSTK LAWS).
#[local] Notation MALLOC1 := (d1_malloc1 B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS HSTK HEV HLIVE LAWS MTL AMALLOC4 HUMM).

(* ---- Ph1's entry state ------------------------------------------------------------------------------------------ *)
Lemma d1_p1_entry : forall g pos mf i ly2 S2 W2 regs2 mem2 md2 (h : nat),
  CTX g pos mf i ly2 S2 W2 regs2 mem2 md2 -> Z.of_nat h = Z.min (e_n g - m_cur g i) 3 ->
  regions_wf (p1_mf :: (if (h =? 0)%nat then [] else [p1_in h])) = true ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs2 (p1_extra (e_pl g) (m_cur g i))))
    (mkSS 0x414 sr_atoms (p1_mf :: (if (h =? 0)%nat then [] else [p1_in h])) None (p1_facts h))
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x414)) mem2 (seg_rom SEGS))) /\
  sh_ok SEGS d1_Bx (p1_SH h) (Eimg (Ereg regs2 (p1_extra (e_pl g) (m_cur g i)))) (mrestrict (w_H W2) mem2).
Proof.
intros g pos mf i ly2 S2 W2 regs2 mem2 md2 h HC Hh Hwf.
pose proof (NUMS g pos mf i ly2 S2 W2 regs2 mem2 md2 HC) as (Hmf0 & Hmfb & Hmf32 & Hsp0al & H47 & HSTKm &
  (HSF0 & HSF1 & HSF64 & HSFapp & EFa) & (Hn & Hinp2 & Hine & Hp4096 & Hpce & Hpapp & Hnlen) & Hi64 & Hcur).
pose proof HC as (HJ & Hfrs & _ & _ & _ & HEC & _ & _ & _ & _ & HRL).
destruct HEC as (Rsp & Rs1 & Rs0 & _ & _ & _ & _ & _ & _ & _ & V176 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & Hinb).
destruct HRL as (_ & _ & (R26 & R18 & _) & _).
pose proof asan_consts as (C1 & _).
assert (Has : ASTACK = 16384) by reflexivity.
set (inp := e_pl g) in *. set (c := m_cur g i) in *. set (p := e_p g) in *. set (n := e_n g) in *.
assert (Hreq : n <= req_size n) by (apply req_size_pos; lia).
assert (Hlen : Z.of_nat (length inp) = n) by (rewrite <- Hnlen; reflexivity).
set (E := Eimg (Ereg regs2 (p1_extra inp c))).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs2 (p1_extra inp c)) k)
  by (intros k Hk; subst E; apply Eimg_low; exact Hk).
assert (E9 : ew E 9 = w64 mf) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact Rs1).
assert (E26 : ew E 26 = w64 (p + c)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 26 26%bv eq_refl); exact R26).
assert (E2 : ew E 2 = w64 mf) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); exact Rsp).
assert (E18 : ew E 18 = w64 (n - c)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl); exact R18).
assert (E32 : ew E 32 = Z_to_bv 64 d1_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (EB : forall j, (j < 3)%nat -> ew E (33 + j) = Z_to_bv 64 (SlotModel.inb inp (c + Z.of_nat j))).
{ intros j Hj. rewrite EL by (unfold A_TEXT; lia). replace (33 + j)%nat with (32 + S j)%nat by lia.
  rewrite ew_Ereg_extra. unfold p1_extra.
  destruct j as [|[|[|j]]]; [cbn [map nth]; rewrite Z.add_0_r; reflexivity | reflexivity | reflexivity | lia]. }
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
assert (Hmfr : 2 ^ 46 <= mf /\ mf + 320 <= 2 ^ 47) by (clear - Hmf0 Hmfb H47 C1 Has; lia).
assert (Hpcr : 4096 <= p + c /\ p + c + Z.of_nat h <= alloc_ceiling) by (clear - Hcur Hh Hp4096 Hpce Hreq; lia).
split.
- rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + exact Hwf.
  + apply Forall_cons.
    * unfold region_ok, p1_mf. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 9%nat mf E9) by (clear - Hmfr C1; lia).
      split; [clear - Hmfr; lia|]. split; [clear - Hmfr; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ mf 176 8 (SOff 32 0) d1_SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold d1_SB; cbn; lia | lia | exact V176].
    * destruct (Nat.eqb_spec h 0) as [H0 | H0]; [constructor|].
      constructor; [|constructor].
      unfold region_ok, p1_in. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 26%nat (p + c) E26) by (clear - Hpcr C1; lia).
      split; [clear - Hpcr; lia|]. split; [clear - Hpcr C1; lia|]. split; [intros o Ho; lia|].
      rewrite Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
      assert (Hj3 : (j < 3)%nat) by lia.
      pose proof (SlotModel.inb_range inp (c + Z.of_nat j)) as Hbr.
      apply (chunk_ok_val SEGS E _ (p + c) (Z.of_nat j) 1 (SOff (33 + j) 0) (SlotModel.inb inp (c + Z.of_nat j)));
        [cbn [sv_denot]; rewrite (EB j Hj3), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
      replace (p + c + Z.of_nat j) with (p + Z.of_nat (Z.to_nat (c + Z.of_nat j))) by (clear - Hcur; lia).
      replace (c + Z.of_nat j) with (Z.of_nat (Z.to_nat (c + Z.of_nat j))) at 2 by (clear - Hcur; lia).
      apply d1_byte_of; [exact Hinb | clear - Hcur Hh Hj Hlen H0; lia].
  + destruct (Nat.eqb_spec h 0) as [H0 | H0].
    * cbn [pairwise_disjoint all_disjoint]. split; exact I.
    * cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
      unfold extent_disjoint, p1_mf, p1_in. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 9%nat mf E9) by (clear - Hmfr C1; lia). rewrite (VB 26%nat (p + c) E26) by (clear - Hpcr C1; lia).
      right. clear - Hpcr Hmf0 Has. lia.
  + unfold facts_ok, p1_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I].
    assert (L : afact_ok E 18 (p1_left h)).
    { unfold afact_ok, p1_left. rewrite E18. unfold w64. rewrite unsigned_lit_small by (clear - Hcur Hn; lia).
      destruct (Nat.ltb_spec h 3); cbn [af_lo af_hi af_al2]; rewrite Z.pow_0_r, Z.mod_1_r; clear - Hh Hcur Hn H; lia. }
    assert (E33 : ew E 33 = Z_to_bv 64 (SlotModel.inb inp c))
      by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
    assert (E34 : ew E 34 = Z_to_bv 64 (SlotModel.inb inp (c + 1)))
      by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
    assert (E35 : ew E 35 = Z_to_bv 64 (SlotModel.inb inp (c + 2)))
      by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
    pose proof (SlotModel.inb_range inp c) as B0. pose proof (SlotModel.inb_range inp (c + 1)) as B1.
    pose proof (SlotModel.inb_range inp (c + 2)) as B2.
    assert (UB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E k) = v)
      by (intros k v Hk Hv; rewrite Hk; apply unsigned_lit_small; exact Hv).
    pose proof (UB 2%nat mf E2 ltac:(clear - Hmfr C1; lia)) as U2.
    pose proof (UB 9%nat mf E9 ltac:(clear - Hmfr C1; lia)) as U9.
    pose proof (UB 26%nat (p + c) E26 ltac:(clear - Hpcr C1; lia)) as U26.
    pose proof (UB 32%nat d1_SB E32 ltac:(unfold d1_SB; lia)) as U32.
    pose proof (UB 33%nat _ E33 ltac:(clear - B0; lia)) as U33.
    pose proof (UB 34%nat _ E34 ltac:(clear - B1; lia)) as U34.
    pose proof (UB 35%nat _ E35 ltac:(clear - B2; lia)) as U35.
    split; [|split; [|split; [exact L|]]]; unfold afact_ok; cbn [af_lo af_hi af_al2];
    rewrite ?U2, ?U9, ?U26, ?U32, ?U33, ?U34, ?U35;
    change (2 ^ 5) with 32; rewrite ?Z.pow_0_r, ?Z.mod_1_r;
    unfold d1_SB; clear - Hmfr Hmf32 Hpcr B0 B1 B2 C1;
    repeat match goal with |- _ /\ _ => split end; try lia; try exact I.
- unfold p1_SH. destruct (Nat.eqb_spec h 0) as [H0 | H0]; [constructor|].
  constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E d1_Bx 26 (p + c) (Z.of_nat h) (p + c) 0 (Z.of_nat h)).
  + apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 p n (p + c) (Z.of_nat h)).
    * pose proof HJ as (HAR2 & _). exact HAR2.
    * exact Hinp2.
    * clear - Hcur. lia.
    * clear - Hcur Hh Hreq. lia.
  + unfold d1_Bx. rewrite (U_atom E 32 d1_SB E32) by (unfold d1_SB; lia). reflexivity.
  + apply (U_atom E 26 (p + c) E26). clear - Hpcr C1. lia.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp. unfold SHADOW_OFF.
    clear - Hx Hpapp Hcur Hh Hreq. lia.
Qed.



(* ---- Ph1: the header and the payload copy's malloc ---------------------------------------------------------------- *)
Lemma p1_c_lt : forall E hi, ew E 34 = Z_to_bv 64 hi -> 0 <= hi < 256 ->
  branch_taken BC_LT (sv_denot E (SLit 1)) (sv_denot E (SAlu ALU_SRL (SOff 34 0) (SLit 6))) = (1 <? hi / 64).
Proof.
intros E hi H Hr. pose proof (d1_U_srl6 E 34 hi H Hr) as Hu. assert (hi / 64 < 4) by (apply Z.div_lt_upper_bound; lia).
assert (0 <= hi / 64) by (apply Z.div_pos; lia).
rewrite d1_branch_lt; rewrite ?U_lit, ?Hu by lia; [reflexivity | lia | lia].
Qed.
Lemma p1_c_ge : forall E hi, ew E 34 = Z_to_bv 64 hi -> 0 <= hi < 256 ->
  branch_taken BC_GE (sv_denot E (SLit 1)) (sv_denot E (SAlu ALU_SRL (SOff 34 0) (SLit 6))) = negb (1 <? hi / 64).
Proof.
intros E hi H Hr. pose proof (d1_U_srl6 E 34 hi H Hr) as Hu. assert (hi / 64 < 4) by (apply Z.div_lt_upper_bound; lia).
assert (0 <= hi / 64) by (apply Z.div_pos; lia).
rewrite d1_branch_ge; rewrite ?U_lit, ?Hu by lia; [reflexivity | lia | lia].
Qed.
Lemma p1_c_eq : forall E hi v, ew E 34 = Z_to_bv 64 hi -> 0 <= hi < 256 -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SAlu ALU_SRL (SOff 34 0) (SLit 6))) (sv_denot E (SLit v)) = (hi / 64 =? v).
Proof. intros E hi v H Hr Hv. rewrite branch_eq_U, (d1_U_srl6 E 34 hi H Hr), U_lit by exact Hv. reflexivity. Qed.
Lemma p1_c_ne : forall E hi v, ew E 34 = Z_to_bv 64 hi -> 0 <= hi < 256 -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_SRL (SOff 34 0) (SLit 6))) (sv_denot E (SLit v)) = negb (hi / 64 =? v).
Proof. intros E hi v H Hr Hv. rewrite branch_ne_U, (d1_U_srl6 E 34 hi H Hr), U_lit by exact Hv. reflexivity. Qed.
Lemma p1_c_geu : forall E w l, ew E 35 = Z_to_bv 64 w -> ew E 18 = Z_to_bv 64 l -> 0 <= w < 256 -> 3 <= l < 2 ^ 26 ->
  branch_taken BC_GEU (sv_denot E (SOff 35 0)) (sv_denot E (SOff 18 (-3))) = negb (w <? l - 3).
Proof.
intros E w l H35 H18 Hw Hl. rewrite branch_geu_U, (U_atom E 35 w H35) by lia.
rewrite (d1_U_off E 18 (-3) l H18) by lia. reflexivity.
Qed.
Lemma p1_c_ltu : forall E w l, ew E 35 = Z_to_bv 64 w -> ew E 18 = Z_to_bv 64 l -> 0 <= w < 256 -> 3 <= l < 2 ^ 26 ->
  branch_taken BC_LTU (sv_denot E (SOff 35 0)) (sv_denot E (SOff 18 (-3))) = (w <? l - 3).
Proof.
intros E w l H35 H18 Hw Hl. rewrite branch_ltu_U, (U_atom E 35 w H35) by lia.
rewrite (d1_U_off E 18 (-3) l H18) by lia. reflexivity.
Qed.
Ltac p1_hc :=
  repeat match goal with
  | Hc : branch_taken BC_LT (sv_denot ?Ex (SLit 1)) (sv_denot ?Ex (SAlu ALU_SRL (SOff 34 0) (SLit 6))) = _ |- _ =>
      rewrite (p1_c_lt Ex _ ltac:(d1_ew)) in Hc by lia; d1_hcZ Hc
  | Hc : branch_taken BC_GE (sv_denot ?Ex (SLit 1)) (sv_denot ?Ex (SAlu ALU_SRL (SOff 34 0) (SLit 6))) = _ |- _ =>
      rewrite (p1_c_ge Ex _ ltac:(d1_ew)) in Hc by lia; d1_hcZ Hc
  | Hc : branch_taken BC_EQ (sv_denot ?Ex (SAlu ALU_SRL (SOff 34 0) (SLit 6))) (sv_denot ?Ex (SLit ?v)) = _ |- _ =>
      rewrite (p1_c_eq Ex _ v ltac:(d1_ew)) in Hc by lia; d1_hcZ Hc
  | Hc : branch_taken BC_NE (sv_denot ?Ex (SAlu ALU_SRL (SOff 34 0) (SLit 6))) (sv_denot ?Ex (SLit ?v)) = _ |- _ =>
      rewrite (p1_c_ne Ex _ v ltac:(d1_ew)) in Hc by lia; d1_hcZ Hc
  | Hc : branch_taken BC_GEU (sv_denot ?Ex (SOff 35 0)) (sv_denot ?Ex (SOff 18 (-3))) = _ |- _ =>
      rewrite (p1_c_geu Ex _ _ ltac:(d1_ew) ltac:(d1_ew)) in Hc by lia; d1_hcZ Hc
  | Hc : branch_taken BC_LTU (sv_denot ?Ex (SOff 35 0)) (sv_denot ?Ex (SOff 18 (-3))) = _ |- _ =>
      rewrite (p1_c_ltu Ex _ _ ltac:(d1_ew) ltac:(d1_ew)) in Hc by lia; d1_hcZ Hc
  end.
(* The values of the header registers at the malloc call, as Z. *)
Ltac p1_U Ex :=
  repeat first
  [ rewrite U_lit by lia
  | rewrite (d1_U_raw Ex 33 34 _ _ ltac:(d1_ew) ltac:(d1_ew)) by lia
  | rewrite (d1_U_srl6 Ex 34 _ ltac:(d1_ew)) by lia
  | rewrite (U_atom Ex 35 _ ltac:(d1_ew)) by lia
  | rewrite (d1_U_off Ex 18 _ _ ltac:(d1_ew)) by lia
  | rewrite (d1_U_off Ex 26 _ _ ltac:(d1_ew)) by lia ].
(* The model values of the header, case by case: the min, the conditionals of fuzz_take and pick_addr. *)
Ltac p1_fin :=
  repeat match goal with
  | |- context [Z.min ?a ?b] => destruct (Z.min_spec a b) as [[? ->] | [? ->]]
  end;
  repeat match goal with
  | |- context [if (?x =? ?y) then _ else _] => destruct (Z.eqb_spec x y)
  | |- context [if (?x <? ?y) then _ else _] => destruct (Z.ltb_spec x y)
  end;
  try (rewrite D1Model.d1_pick by lia); try (rewrite D1Model.d1_pick_lo by lia);
  unfold RcIdentModel.ADDR_FIRMWARE, RcIdentModel.ADDR_REAC_VERSION, RcIdentModel.ADDR_MODEL_NAME;
  repeat match goal with
  | |- context [if (?x =? ?y) then _ else _] => destruct (Z.eqb_spec x y)
  end;
  lia.
Ltac p1_leaf :=
  lazymatch goal with
  | HS : st_ok _ ?Ex (setpc _ _) (restrict (w_H _) ?ms), HAE : env_agree 32 ?Er _,
    MK : D1k ?gg ?ii = _, MB : D1body ?gg ?ii = _, MA : D1addr ?gg ?ii = _ |- _ =>
    let Q1 := fresh "Q1" in let Q10 := fresh "Q10" in let Q22 := fresh "Q22" in let Q27 := fresh "Q27" in
    let Q26 := fresh "Q26" in let Q18 := fresh "Q18" in
    prreg HS (1%bv : bv 5) Q1;
    d1_prraw HS (10%bv : bv 5) Q10; d1_prraw HS (22%bv : bv 5) Q22; d1_prraw HS (27%bv : bv 5) Q27;
    d1_prraw HS (26%bv : bv 5) Q26; d1_prraw HS (18%bv : bv 5) Q18;
    let HAE' := fresh "HAE" in
    assert (HAE' : env_agree 32 Er Ex)
      by (split; [let nn := fresh "nn" in let Hnn := fresh "Hnn" in intros nn Hnn;
                  repeat first [rewrite ew_havoc_old by lia | rewrite ew_ewset_other by lia];
                  exact (proj1 HAE nn Hnn)
                 | cbn [ed ewset havoc]; exact (proj2 HAE)]);
    let HKR := fresh "HKR" in
    pose proof (regs_kept_of_st_ok SEGS Ex _ _ _ _ [2; 3; 4; 8; 9; 19; 20; 21; 24]%bv HS HAE'
      ltac:(vm_compute; reflexivity)) as HKR;
    cbn [ms_regs restrict] in HKR;
    pmkst HS; rewrite (pal_malloc B TL);
    eapply MALLOC1;
    [ eassumption | eassumption | eassumption
    | unfold RC; repeat split; (rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right]))); assumption
    | eapply d1_reg_val; [exact Q10 | rewrite MK; p1_U Ex; p1_fin | rewrite MK; p1_fin]
    | eapply d1_reg_val; [exact Q22 | rewrite MK; p1_U Ex; p1_fin | rewrite MK; p1_fin]
    | eapply d1_reg_val; [exact Q27 | rewrite MA; p1_U Ex; p1_fin
      | unfold D1addr; match goal with |- 0 <= SlotModel.rec_addr ?x ?j < _ =>
          pose proof (D1Model.d1_addr_range x j) end; lia]
    | eapply d1_reg_val; [exact Q26 | rewrite MB; p1_U Ex; p1_fin | rewrite MB; p1_fin]
    | eapply d1_reg_val; [exact Q18 | rewrite MB; p1_U Ex; p1_fin | rewrite MB; p1_fin]
    | exact Q1 ]
  end.
Ltac p1_go :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
                      SHOK : sh_ok _ _ _ _ _ |- _ =>
    paj_run_tok RUN HS HJ SHOK d1_Bspan; [awr_ok_tac |
    d1_keep_ro;
    lazymatch goal with
    | HS' : st_ok _ _ (setpc _ _) (restrict _ _) |- _ => p1_leaf
    | HS' : st_ok_pi _ _ _ _ _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
        psrr_branch_tok RUN BR HS' SHOK' d1_Bspan; p1_hc; p1_go
    end ]
  end.

Lemma d1_ph1 : forall g pos mf i ly2 S2 W2 regs2 mem2 md2,
  CTX g pos mf i ly2 S2 W2 regs2 mem2 md2 ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x414) regs2 mem2 md2)
    (fun W3 c3 => exists pl, RUNS g pos mf i ly2 S2 W2 mem2 1 (BASE + 0x4c0) (mo_malloc MT (D1k g i))
                   [(pl, D1k g i)] (WR0 g pos mf) (P1 B g pos mf i pl) W3 c3).
Proof.
intros g pos mf i ly2 S2 W2 regs2 mem2 md2 HC.
pose proof (NUMS g pos mf i ly2 S2 W2 regs2 mem2 md2 HC) as (Hmf0 & Hmfb & Hmf32 & Hsp0al & H47 & HSTKm &
  (HSF0 & HSF1 & HSF64 & HSFapp & EFa) & (Hn & Hinp2 & Hine & Hp4096 & Hpce & Hpapp & Hnlen) & Hi64 & Hcur).
pose proof HC as (HJ & Hfrs & _ & _ & _ & HEC & Hi & R20 & R21 & R24 & HRL).
destruct HEC as (Rsp & Rs1 & Rs0 & _ & _ & Rgp & Rtp & Rs3 & _).
destruct HRL as (_ & _ & (R26 & R18 & _) & _).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hreq : e_n g <= req_size (e_n g)) by (apply req_size_pos; lia).
pose proof (D1Model.d1_hdr (e_pl g) (m_cur g i) ltac:(rewrite Hnlen; lia)) as (Hhh & Hbody & Hkk & Hraw).
rewrite Hnlen in Hhh, Hbody, Hkk, Hraw.
pose proof (SlotModel.inb_range (e_pl g) (m_cur g i)) as Hlo.
pose proof (SlotModel.inb_range (e_pl g) (m_cur g i + 1)) as Hhi.
pose proof (SlotModel.inb_range (e_pl g) (m_cur g i + 2)) as Hw.
assert (MK : D1k g i = SlotModel.h_k (e_pl g) (m_cur g i)) by reflexivity.
assert (MB : D1body g i = SlotModel.h_body (e_pl g) (m_cur g i)) by reflexivity.
assert (MA : D1addr g i = SlotModel.pick (SlotModel.h_raw (e_pl g) (m_cur g i))) by reflexivity.
rewrite Hkk in MK. rewrite Hbody in MB. rewrite Hraw in MA. clear Hhh Hkk Hbody Hraw.
remember (Eimg (Ereg regs2 (p1_extra (e_pl g) (m_cur g i)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs2 (p1_extra (e_pl g) (m_cur g i))) k)
  by (intros k Hk; rewrite HE; apply Eimg_low; exact Hk).
assert (E18 : ew E 18 = Z_to_bv 64 (e_n g - m_cur g i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl); exact R18).
assert (E26 : ew E 26 = Z_to_bv 64 (e_p g + m_cur g i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 26 26%bv eq_refl); exact R26).
assert (E33 : ew E 33 = Z_to_bv 64 (SlotModel.inb (e_pl g) (m_cur g i)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (SlotModel.inb (e_pl g) (m_cur g i + 1)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (SlotModel.inb (e_pl g) (m_cur g i + 2)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (HAE : env_agree 32 (Ereg regs2 (p1_extra (e_pl g) (m_cur g i))) E)
  by (rewrite HE; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (KP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W2) mem2 a)
  by (intros; reflexivity).
unfold cfg_at. change (w64 (BASE + 0x414)) with (Z_to_bv 64 (BASE + 0x414)).
assert (Hcase : e_n g - m_cur g i = 0 \/ e_n g - m_cur g i = 1 \/ e_n g - m_cur g i = 2 \/
                3 <= e_n g - m_cur g i) by (clear - Hcur Hn; lia).
destruct Hcase as [L | [L | [L | L]]].
- destruct (d1_p1_entry g pos mf i ly2 S2 W2 regs2 mem2 md2 0 HC ltac:(clear - L; lia)
    ltac:(vm_compute; reflexivity)) as [HS0 SHOK].
  rewrite <- HE in HS0, SHOK.
  pose proof (st_ok_pi_pin_reg' E _ _ 18%bv 0 HS0
    ltac:(cbn [ms_regs restrict mkst]; rewrite R18; unfold w64; f_equal; clear - L; lia) eq_refl) as HS.
  clear HS0. assert (Hl : True) by exact I.
  p1_go.
- destruct (d1_p1_entry g pos mf i ly2 S2 W2 regs2 mem2 md2 1 HC ltac:(clear - L; lia)
    ltac:(vm_compute; reflexivity)) as [HS0 SHOK].
  rewrite <- HE in HS0, SHOK.
  pose proof (st_ok_pi_pin_reg' E _ _ 18%bv 1 HS0
    ltac:(cbn [ms_regs restrict mkst]; rewrite R18; unfold w64; f_equal; clear - L; lia) eq_refl) as HS.
  clear HS0. assert (Hl : True) by exact I.
  p1_go.
- destruct (d1_p1_entry g pos mf i ly2 S2 W2 regs2 mem2 md2 2 HC ltac:(clear - L; lia)
    ltac:(vm_compute; reflexivity)) as [HS0 SHOK].
  rewrite <- HE in HS0, SHOK.
  pose proof (st_ok_pi_pin_reg' E _ _ 18%bv 2 HS0
    ltac:(cbn [ms_regs restrict mkst]; rewrite R18; unfold w64; f_equal; clear - L; lia) eq_refl) as HS.
  clear HS0. assert (Hl : True) by exact I.
  p1_go.
- destruct (d1_p1_entry g pos mf i ly2 S2 W2 regs2 mem2 md2 3 HC ltac:(clear - L; lia)
    ltac:(vm_compute; reflexivity)) as [HS SHOK].
  rewrite <- HE in HS, SHOK.
  assert (Hl : 3 <= e_n g - m_cur g i < 2 ^ 26) by (clear - L Hn Hcur; lia).
  p1_go.
Qed.

End c.
End b.
End a.
