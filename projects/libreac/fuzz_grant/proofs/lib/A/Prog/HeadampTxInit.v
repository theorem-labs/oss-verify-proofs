(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_init on fuzz_grant.asan, written for libreac/fuzz_grant: the entry seat and the return are adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v, the __asan_memset call from proofs/cgif/cgif_file_fuzzer/lib/A/AC8y.v, the reseat after it from proofs/cgif/cgif_file_fuzzer/lib/A/ACbl.v, and further proof steps from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v and proofs/cgif/cgif_file_fuzzer/lib/A/AE6j.v; the contract is new. *)
(* reac_headamp_tx_init (fuzz_grant.asan 0x84d1c, 8 instructions): the contract of the
   ASan build's code and its walk. The function takes a 16-byte frame on the machine
   stack, saves ra there, calls __asan_memset (t, 0, 460) and returns: the 460 bytes of
   the head-amp table at t, a heap block of the caller, read as 0 afterwards. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaRun PaShadow GrantSyms GrantList GrantPa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaJournal GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* sizeof (struct reac_headamp_tx), the length the function passes to memset. *)
Definition TX_SIZE : Z := 460.
Lemma req_tx : req_size TX_SIZE = TX_SIZE.
Proof. reflexivity. Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: its own 16-byte frame
   (addi sp,sp,-16) and ESTACK below it for the memset wrapper. *)
Definition A_reac_headamp_tx_initP : Z := BASE + AF_reac_headamp_tx_init.
Definition REAC_HEADAMP_TX_INIT_STK : Z := 16 + ESTACK.
Definition SB_TXI : Z := 0x7fff8000.
Definition Bx_TXI : sv := SLit SB_TXI.
Definition Bspan_TXI : Z * Z := (SB_TXI, SB_TXI + 2 ^ 44 - 1).
Definition ss_txi : sstate :=
mkSS AF_reac_headamp_tx_init sr_atoms [stack_region 16] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
Lemma aview_same_at : forall (H : word -> bool) (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a E. unfold aview, mbyte, mrestrict. cbv beta. rewrite E. reflexivity. Qed.
Section h.
Variable B : asyms.
Definition treac_headamp_tx_init_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (t : Z) : world SEGS -> config -> Prop :=
apost_base SEGS B REAC_HEADAMP_TX_INIT_STK [(t, t + TX_SIZE)] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall i, 0 <= i < TX_SIZE -> aview SEGS (w_H W') mem' (t + i) = Some 0)).
Definition treac_headamp_tx_init_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (t : Z),
afn_pre SEGS B REAC_HEADAMP_TX_INIT_STK ly S W regs mem md ch ->
getr regs 10 = w64 t -> In (t, TX_SIZE) (ablocks B ly S) ->
SRr SEGS W (cfg_at SEGS A_reac_headamp_tx_initP regs mem md) (treac_headamp_tx_init_post regs ly S W mem md t).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA GS___asan_memset).
Let RUN := paj_run B LAWS.
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).
Lemma txi_entry : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch,
afn_pre SEGS B REAC_HEADAMP_TX_INIT_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_txi
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_headamp_tx_init)) mem (seg_rom SEGS))) /\
sh_ok SEGS Bx_TXI [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch HPRE. split; [|constructor].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_HEADAMP_TX_INIT_STK = 4112) by reflexivity.
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs [])) 2) = spZ regs)
by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
rewrite restrict_mkst_fx. unfold ss_txi. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- split; exact I.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia].
Qed.
Theorem pb_reac_headamp_tx_init : treac_headamp_tx_init_spec.
Proof.
unfold treac_headamp_tx_init_spec.
intros ly S W regs mem md ch t HPRE H10 Hin.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (txi_entry ly S W regs mem md ch HPRE) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_HEADAMP_TX_INIT_STK [(t, t + TX_SIZE)] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_HEADAMP_TX_INIT_STK = 4112) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md t TX_SIZE HAR Hin) as (Ht16 & Ht4096 & Htceil & _).
rewrite req_tx in Htceil. assert (Htx : TX_SIZE = 460) by reflexivity.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE.
unfold cfg_at, A_reac_headamp_tx_initP.
change (w64 (BASE + AF_reac_headamp_tx_init)) with (Z_to_bv 64 (BASE + AF_reac_headamp_tx_init)).
(* The frame, the save of ra and the arguments, up to the call of __asan_memset. *)
paj_run_tok RUN HS HJ SHOK Bspan_TXI; [awr_ok_tac; exact Usp |].
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
assert (Qsp : spZ rg = spZ regs + -16) by (unfold spZ at 1; rewrite Rsp, Usp, unsigned_lit_small by lia; reflexivity)
end.
(* The memset wrapper: it writes 0 to [t, t + 460) and keeps every other byte above its own stack. *)
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply SRr_bind;
[ eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA GS___asan_memset) AMEMSET W rg mm
REAC_HEADAMP_TX_INIT_STK (spZ regs) [(t, t + TX_SIZE)] ly S W mem md [] ly S _ 0 t 0 TX_SIZE (-16) _ HJ);
[ rewrite Ra0, E10; reflexivity
| rewrite Ra1; reflexivity
| rewrite Ra2; reflexivity
| rewrite Htx; lia
| lia
| rewrite Htx; lia
| exact Qsp
| reflexivity
| lia
| rewrite WS, Hes; lia
| rewrite Rgp, E3; exact Hgp
| rewrite Rtp, E4; exact Htp
| exact Rra
| apply ret_ok_codeptr_v; [lia | reflexivity]
| intros a Ha; split;
[ right; left; split;
[ exists (t, t + TX_SIZE); split; [left; reflexivity | cbn [fst snd]; lia]
| exists t, TX_SIZE; split; [exact Hin | rewrite req_tx; lia] ]
| rewrite Hes; lia ]
| eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin); rewrite ?req_tx; lia
| eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin); rewrite ?req_tx; lia
| intros _; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin); rewrite ?req_tx; lia
| exact I ]
| ]
end.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Heff & Hfr & Hpres2).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
(* Back at the return slot: the stack region (the saved ra) is kept by the wrapper. *)
jafter_call_keep_pi HS 32%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hfr; [lia | lia | rewrite Hes; lia].
- intros _. apply (apresent_writable SEGS). apply HJpres. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 32 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall k, (k < 32)%nat -> ew E' k = ew E k) by (intros k Hk; rewrite HE'; apply YN3v.ew_havoc_old; exact Hk).
assert (HAE' : env_agree 32 (Ereg regs []) E') by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HE'.
assert (F1 : ew E' 1 = getr regs 1) by (rewrite OLD by lia; exact E1).
assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite OLD by lia; exact Usp).
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
assert (SHOK' : sh_ok SEGS Bx_TXI [] E' (mrestrict (w_H W) mem2)) by constructor.
clear SHOK.
(* The reload of ra, the release of the frame and the return. *)
paj_run_tok RUN HS HJ2 SHOK' Bspan_TXI; [awr_ok_tac; exact Usp' |].
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HF : frame_of _ ?rs mem2 (ms_mem ?msc) |- _ =>
prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
intros mat';
unfold treac_headamp_tx_init_post, apost_base;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1, F1, Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ E' _ _ regs [] HS); [exact HAE' | vm_compute; reflexivity]|];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [apply Permutation_refl|];
intros i Hi; rewrite (aview_same_at (w_H W) mem2 (ms_mem msc) (t + i)); [rewrite (Heff i Hi); reflexivity|];
apply HF; let rs' := eval vm_compute in rs in change rs with rs';
intros (r & [<- | []] & Hr);
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite Usp', unsigned_lit_small in Hr by lia; lia
end.
Qed.
End h.
End f.
End d.
