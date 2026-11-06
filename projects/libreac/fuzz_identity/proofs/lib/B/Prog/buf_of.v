(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-148
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:388-392 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFfi.v:262-264 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC4t.v:438 [Apache-2.0 OR MIT], for libreac/fuzz_identity's
   asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_identity_ingest.v, with its module paths and module names changed; 183 of its 226 lines of code are new or changed and 3022 lines of the source are left out. *)
(* buf_of (fuzz_identity.asan-ubsan 0x82800, 0x30 bytes, listing offset AF_buf_of = 0x208c): its ASan+UBSan-build
   contract tbuf_of_spec, in the afn_pre / apost_base form (CONVENTIONS.md section 3; cgif lib/A/ACb8.v pb_rawnewX,
   a call that allocates, with the meter premise mo_ok and the post mo_le): the call writes only its own stack
   window (ra at sp - 8) and, through the allocator, the new heap block.
   On the ASan build buf_of is inlined into LLVMFuzzerTestOneInput, so no A twin exists; the A draft of
   LLVMFuzzerTestOneInput calls malloc there through amalloc04_rule, and this contract hands the
   B caller the same facts amalloc04_rule hands the A caller (the result, the block list, the meter).
   C (fuzz_identity.c): static char *buf_of(size_t n) { char *p = malloc(n ? n : 1); if (!p) abort(); return p; }
   The released ubsan template is lib/U/Prog/buf_of_c.v (buf_of_contract, ubsan 0x140f0): a fresh block of
   Z.max c 1 bytes, its address non-null and 16-aligned, for 0 <= c <= 2 ^ 28 - 1. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun PaShadow PaJournal IdentBase YC81 YC4b.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import IdentBSyms IdentBList IdentBPa IdentBPaLib.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import YC1g YC1h YC85.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Definition A_buf_of : Z := BASE + AF_buf_of.
(* The return address of buf_of's malloc call (0x82810 jal, so 0x82814 = A_buf_of + 0x14). *)
Definition RA_buf_of_malloc : Z := A_buf_of + 0x14.
(* The stack the call needs, measured from the listing: the 16-byte frame (0x82800 addi sp,sp,-16; ra at sp+8)
   and below it the ASTACK window that amalloc04_rule asks of a malloc call (ASTACK - o <= STK at o = -16).
   The abort path (0x82824 __asan_handle_no_return, 0x82828 abort) is never reached. *)
Definition BUF_OF_STK : Z := 16 + ASTACK.
(* Allocator events of one call: the one malloc (amalloc04_rule's journal counts k + 1). *)
Definition EV_BUF_OF : Z := 1.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
(* The call contexts buf_of may be entered from: each is raZ :: spine ch at entry (CONVENTIONS section 3). buf_of
   pushes no frame record, so the trace its malloc sees is RA_buf_of_malloc :: spine ch (the walk's HUM). *)
Variable CTX : list (list Z).
(* The post: back at ra, the call's own journal (one event), callee-saved registers kept, and what amalloc04_rule
   gives the A caller at the inlined malloc: the result res >= 4096 in a0 (so abort is not reached), the frames
   unchanged, the block list grown by (res, Z.max n 1), and the meter used by one malloc of Z.max n 1 bytes. *)
Definition tbuf_of_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (n : Z) : world SEGS -> config -> Prop :=
  apost_base SEGS B BUF_OF_STK [] regs ly S W mem md EV_BUF_OF
    (fun ly' S' W' regs' mem' md' => exists res : Z,
       getr regs' 10 = w64 res /\ 4096 <= res /\ frames S' = frames S /\
       ablocks B ly' S' = ablocks B ly S ++ [(res, Z.max n 1)] /\
       mo_le MT S S' (mo_malloc MT (Z.max n 1))).
(* The pre-condition. a0 = n (size_t). The allocation succeeds by amalloc04_rule (the walk's Section hypothesis
   AMALLOC4) under these premises: n < MALLOC_MAX, the event budget st_nev S + EV_BUF_OF <= EV_MAX, the live-byte
   budget blocks_bytes S + Z.max n 1 <= LIVE_MAX, and the meter room mo_ok MT S (mo_malloc MT (Z.max n 1)); its
   post gives 4096 <= res, so the beqz at 0x82814 to the abort path is not taken. *)
Definition tbuf_of_spec : Prop :=
  forall ly S W (regs : bvmap 5 word) mem md ch (n : Z),
  afn_pre SEGS B BUF_OF_STK ly S W regs mem md ch ->
  In (raZ regs :: spine ch) CTX ->
  getr regs 10 = w64 n -> 0 <= n < MALLOC_MAX ->
  st_nev S + EV_BUF_OF <= EV_MAX -> blocks_bytes S + Z.max n 1 <= LIVE_MAX ->
  mo_ok MT S (mo_malloc MT (Z.max n 1)) ->
  SRr SEGS W (cfg_at SEGS A_buf_of regs mem md) (tbuf_of_post regs ly S W mem md n).
(* ---- The walk (CONVENTIONS.md section 5; cgif lib/A/ACb8.v pb_rawnewX for the malloc call) ---------------- *)
(* buf_of reads no shadow: the shadow base is never loaded, so the run has no shadow entries. *)
Definition Bx_BO : sv := SLit SB.
Definition Bspan_BO : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* The symbolic state at buf_of's first slot: its own 16-byte frame below sp, sp's range and alignment. *)
Definition ss_bo : sstate :=
  mkSS AF_buf_of sr_atoms [stack_region 16] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
(* a0 at the malloc call, as the walk computes it (0x82808 seqz a1,a0; 0x8280c add a0,a0,a1): n + (n == 0). *)
Definition BO_A0 : sv := SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLTU (SOff 10 0) (SLit 1)).
Lemma bo_a0 : forall E n, ew E 10 = Z_to_bv 64 n -> 0 <= n < MALLOC_MAX -> sv_denot E BO_A0 = w64 (Z.max n 1).
Proof.
intros E n H Hn. unfold MALLOC_MAX in Hn. rewrite denot_lit_U. unfold w64. f_equal. unfold BO_A0.
rewrite !U_SAlu, (U_atom E 10 n H) by lia. rewrite U_SLit. cbn [zalu_raw].
rewrite (zcanon_id 1) by (unfold M64; lia).
destruct (Z.ltb_spec n 1) as [Hl | Hl].
- rewrite (zcanon_id 1) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
- rewrite (zcanon_id 0) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* The taken side of 0x82814 beqz a0 (to the abort path) is impossible: a0 is malloc's result, at least 4096. *)
Lemma bo_beq_absurd : forall E a (w : word) res,
  w = sv_denot E a -> w = w64 res -> 4096 <= res < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E a) (sv_denot E (SLit 0)) = true -> False.
Proof.
intros E a w res H1 H2 Hr Hc. rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc. unfold U in Hc.
rewrite <- H1, H2 in Hc. cbn [sv_denot] in Hc. unfold w64 in Hc. rewrite !unsigned_lit_small in Hc by lia. lia.
Qed.
Section walk.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
(* The call traces of buf_of's malloc are in the allocator's universe (cgif ACb8.v:77 HUM): buf_of pushes no frame
   record, so the trace is pc_malloc_ra0 :: RA_buf_of_malloc :: spine ch, without buf_of's own return address. *)
Hypothesis HUM : forall ra c, In (ra :: c) CTX ->
  In (firstn kUnwindMax (pc_malloc_ra0 (as_code B)
        :: flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (RA_buf_of_malloc :: c)))
     (as_universe B).
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_identb) (PI := PI).
Lemma bo_entry : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch,
  afn_pre SEGS B BUF_OF_STK ly S W regs mem md ch ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_bo
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_buf_of)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (E2 : bv_unsigned (ew (Eimg (Ereg regs [])) 2) = spZ regs) by (rewrite (ew_Eimg_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
pose proof asan_consts as (C1 & _). unfold BUF_OF_STK, ASTACK in *.
rewrite restrict_mkst_fx. unfold ss_bo. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  unfold region_ok, stack_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem mkst].
  rewrite E2. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; exact I]. cbn [atoms_ok f_atoms]. split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2. change (2 ^ 4) with 16. lia.
Qed.
Theorem pb_buf_of : tbuf_of_spec.
Proof.
unfold tbuf_of_spec.
intros ly S W regs mem md ch n HPRE Hctx H10 Hn Hev Hlive MOK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
pose proof (bo_entry ly S W regs mem md ch HPRE) as HS.
pose proof (ajournal_init SEGS B BUF_OF_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r) by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (SHOK : sh_ok SEGS Bx_BO [] E (mrestrict (w_H W) mem)) by constructor.
unfold cfg_at, A_buf_of. change (w64 (BASE + AF_buf_of)) with (Z_to_bv 64 (BASE + AF_buf_of)).
paj_run_tok RUN HS HJ SHOK Bspan_BO; [awr_ok_tac; exact Usp |].
(* At the malloc call (slot 0x82810): the registers malloc receives. *)
assert (E10 : ew E 10 = Z_to_bv 64 n) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_restrict_reg SEGS (w_H W) E ssx msx (10%bv : bv 5) HS) as Ra0;
  replace (sr_get (ss_regs ssx) (10%bv : bv 5)) with BO_A0 in Ra0 by (vm_compute; reflexivity)
end.
cbn [ms_regs restrict] in Ra0. rewrite (bo_a0 E n E10 Hn) in Ra0.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp.
prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
pose proof asan_consts as (C1 & _).
assert (Qsp : alloc_ceiling + BUF_OF_STK <= spZ regs) by lia.
unfold BUF_OF_STK, ASTACK in Qsp.
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ eapply (aview_kept_frame E (ss_mem ss_bo) (w_H W) mem (ms_mem ms) (spZ regs) HFr); [lia|].
  intros a Ha (rg & Hin & Hrg). cbn [ss_mem ss_bo In] in Hin. destruct Hin as [<- | []].
  cbn [stack_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg. rewrite Usp in Hrg. lia. }
assert (Hch' : achain ly (aview SEGS (w_H W) (ms_mem ms)) (spZ regs) (s0Z regs) ch)
  by exact (achain_kept ly _ _ (spZ regs) (s0Z regs) ch (spZ regs) Hch (Z.le_refl _) ltac:(lia) HUP).
assert (Rsp' : spZ (ms_regs ms) = spZ regs + -16).
{ unfold spZ at 1. rewrite Rsp, Usp. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Rra' : raZ (ms_regs ms) = BASE + 8352).
{ unfold raZ. rewrite Rra. rewrite unsigned_lit_small by lia. reflexivity. }
pmkst HS. ppcs.
eapply SRr_bind.
{ eapply (amalloc04_sub SEGS B LAWS Hsegs MT AMALLOC4 W (ms_regs ms) (ms_mem ms) BUF_OF_STK (spZ regs) [] ly S W mem md []
    ly S _ 0 (Z.max n 1) (-16) (Z_to_bv 64 (BASE + 8352)) ch HJ).
  - exact Ra0.
  - unfold MALLOC_MAX in *. lia.
  - exact Hlive.
  - exact Rsp'.
  - reflexivity.
  - lia.
  - unfold BUF_OF_STK, ASTACK. lia.
  - rewrite Rgp, ?Z.add_0_r, ?Z_to_bv_bv_unsigned, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite Rtp, ?Z.add_0_r, ?Z_to_bv_bv_unsigned, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold EV_BUF_OF in Hev. lia.
  - apply (achain_chain_pre ly _ (spZ regs) (s0Z regs) ch _ Hch').
    + rewrite Rsp'. lia.
    + unfold s0Z. rewrite Rs0, ?Z.add_0_r, ?Z_to_bv_bv_unsigned, (EE 8%nat 8%bv eq_refl). reflexivity.
    + rewrite Rra'. lia.
  - rewrite call_trace_of_spine. rewrite Rra'.
    replace (BASE + 8352) with RA_buf_of_malloc by (unfold RA_buf_of_malloc, A_buf_of, AF_buf_of; lia).
    exact (HUM (raZ regs) (spine ch) Hctx).
  - exact MOK. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Ha02 & Hfrs2 & Hres4096 & Eab2 & HK2 & MLE2 & _).
(* Back at 0x82814 with malloc's result: re-seat the symbolic state on the kept frame. *)
assert (Hres_in : In (res, Z.max n 1) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res (Z.max n 1) (proj1 HJ2) Hres_in) as (_ & _ & Hrceil & _).
pose proof (req_size_pos0 (Z.max n 1) ltac:(lia)) as Hreq.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
let K := run_K_hi HS in jafter_call_keep_hi HS K regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
lazymatch type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
  - apply (mbyte_of_aview SEGS). apply (proj1 HK2); [lia | unfold ASTACK; lia].
  - intros _. apply (apresent_writable SEGS). apply HJpres2. unfold BUF_OF_STK, ASTACK. lia. }
specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (HEI2 : img_env VAL A_LIM Ev) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]);
  assert (HAE2 : env_agree 32 (Ereg regs []) Ev)
    by (destruct HAE as [HA HD]; split; [intros k Hk; rewrite ew_havoc_old by (cbv; lia); apply HA; exact Hk | exact HD]);
  assert (Usp2 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite ew_havoc_old by (cbv; lia); exact Usp);
  assert (SHOK2 : sh_ok SEGS Bx_BO [] Ev (mrestrict (w_H W2) mem2)) by constructor
end.
clear HEI HEI0 SHOK HAE Usp.
psrr_branch_tok RUN BR HS SHOK2 Bspan_BO.
- (* taken: the abort path; a0 = res >= 4096 refutes it *)
  exfalso.
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ev ?a) _ = true =>
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    pose proof (st_ok_pi_restrict_reg (w_H W2) Ev ssx msx (10%bv : bv 5) HS) as Ra2;
    change (sr_get (ss_regs ssx) (10%bv : bv 5)) with a in Ra2 end end.
  cbn [ms_regs restrict mkst] in Ra2.
  exact (bo_beq_absurd _ _ _ res Ra2 Ha02 ltac:(lia) Hc).
- (* not taken: restore ra and sp, return *)
  paj_run_tok RUN HS HJ2 SHOK2 Bspan_BO; [awr_ok_tac; exact Usp2 |].
  lazymatch type of HS with st_ok_pi _ _ ?Ef ?ssf (restrict _ ?msf) =>
    pose proof (st_ok_pi_restrict_reg (w_H W2) Ef ssf msf (1%bv : bv 5) HS) as R1;
    change (sr_get (ss_regs ssf) (1%bv : bv 5)) with (SOff 1 0) in R1;
    pose proof (st_ok_pi_restrict_reg (w_H W2) Ef ssf msf (10%bv : bv 5) HS) as R10;
    change (sr_get (ss_regs ssf) (10%bv : bv 5)) with (SOff 516 0) in R10;
    assert (Ef1 : ew Ef 1 = getr regs 1)
      by (destruct HAE2 as [HA _]; rewrite (HA 1%nat ltac:(lia)); apply ew_Ereg_nat; reflexivity);
    assert (Ef516 : ew Ef 516 = getr regs2 10%bv)
      by (exact (ew_havoc_new E 512 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0) ltac:(cbv; lia)));
    cbn [ms_regs restrict sv_denot] in R1, R10; rewrite Z.add_0_r, Z_to_bv_bv_unsigned in R1, R10;
    eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)); intros mat';
    unfold tbuf_of_post, apost_base;
    rewrite R1, Ef1, Hra;
    exists ly2, S2, (ms_regs msf), (ms_mem msf); eexists;
    split; [reflexivity|];
    split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ Ef _ _ regs [] HS); [exact HAE2 | vm_compute; reflexivity]|];
    exists res; split; [rewrite R10, Ef516; exact Ha02|];
    split; [exact Hres4096|]; split; [exact Hfrs2|]; split; [exact Eab2 | exact MLE2]
  end.
Qed.
End walk.
End h.
End f.
End d.
