(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_init on fuzz_grant.asan, written for libreac/fuzz_grant: the entry seat and the return are adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v, the __asan_memset call from proofs/cgif/cgif_file_fuzzer/lib/A/AC8y.v, the reseat after it from proofs/cgif/cgif_file_fuzzer/lib/A/ACbl.v, and further proof steps from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v and proofs/cgif/cgif_file_fuzzer/lib/A/AE6j.v; the contract is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/HeadampTxInit.v, with its module paths and module names changed; 222 of its 296 lines of code are new or changed and 113 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YK06 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require CtrlParsed disco_classify_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset).
Definition REAC_DISCO_PEER_LOCK_INIT_STK : Z := 16 + ESTACK.
Definition treac_disco_peer_lock_init_kept (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (W2 : world SEGS) (mem2 : word -> option byte) (sp l : Z) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - REAC_DISCO_PEER_LOCK_INIT_STK <= a < sp) -> ~ (l <= a < l + 12) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ (l <= b + i < l + 12) ->
     aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ (l <= a < l + 12) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - REAC_DISCO_PEER_LOCK_INIT_STK <= a < sp) ->
     apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
  (forall a, sp - REAC_DISCO_PEER_LOCK_INIT_STK <= a < sp -> apresent (w_H W2) mem2 a).
Definition treac_disco_peer_lock_init_post (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (l : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst (fx := fq) regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\ getr regs2 1 = getr regs 1 /\
    getr regs2 10 = getr regs 10 /\
    frames S2 = frames Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    treac_disco_peer_lock_init_kept lyc Sc W memc W2 mem2 (spZ regs) l /\
    garr8 SEGS (mrestrict (w_H W2) mem2) l (map (fun b : byte => bv_unsigned b) (repeat (CtrlParsed.zb 0) 12)) /\
    disco_classify_c.lock_ok (repeat (CtrlParsed.zb 0) 12).
Definition treac_disco_peer_lock_init_spec : Prop :=
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
    (l : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 l ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_DISCO_PEER_LOCK_INIT_STK -> spZ regs <= sp0 ->
  l mod 4 = 0 ->
  0 <= l -> l + 12 <= 2 ^ 63 ->
  (spZ regs <= l \/ l + 12 <= spZ regs - REAC_DISCO_PEER_LOCK_INIT_STK) ->
  (forall a, l <= a < l + 12 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) ->
  amem_range l 12 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF l 12 -> shadow_hull_vis (aview SEGS (w_H W) memc) l 12 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_disco_peer_lock_init) regs memc mdc)
    (treac_disco_peer_lock_init_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs l).
Definition SB_PL : Z := 0x7fff8000.
Definition Bx_PL : YP0m.sv := YP0m.SLit SB_PL.
Definition Bspan_PL : Z * Z := (SB_PL, SB_PL + 2 ^ 44 - 1).
Definition ss_pl : YP0l.sstate :=
YP0l.mkSS AF_reac_disco_peer_lock_init sr_atoms [stack_region 16] None
(YP0m.mkFacts [(2%nat, YP0m.mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
Lemma pl_lock0 : disco_classify_c.lock_ok (repeat (CtrlParsed.zb 0) 12).
Proof. split; [reflexivity | left; vm_compute; reflexivity]. Qed.
Lemma pl_garr8 : forall (H : word -> bool) (m : word -> option byte) d n, 0 <= n ->
(forall i, 0 <= i < n -> aview SEGS H m (d + i) = Some 0) ->
garr8 SEGS (mrestrict H m) d (repeat 0 (Z.to_nat n)).
Proof.
intros H m d n Hn HZ. apply garr8_zeros. intros a Ha. rewrite Z2Nat.id in Ha by exact Hn.
pose proof (HZ (a - d) ltac:(lia)) as Hv. replace (d + (a - d)) with a in Hv by lia.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H m) a) as [b|]; cbn in Hv; [|discriminate].
injection Hv as Hv. f_equal. apply bv_eq. rewrite Hv. reflexivity.
Qed.
Lemma pl_view_frame : forall (H : word -> bool) (m m' : word -> option byte) E rs a,
frame_of E rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H m m' E rs a HF Ha Hn.
assert (Ex : m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) by (apply HF; rewrite YP03.unsigned_lit_small by exact Ha; exact Hn).
unfold aview, mbyte, mrestrict. cbv beta. rewrite Ex. reflexivity.
Qed.
Section w.
Context {fx : YK11.FPState}.
Let RUN := paj_run (PL := PL_disco) (PI := PI) B LAWS.
Let RET := paj_ret_at (PL := PL_disco) (PI := PI).
Lemma pl_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k (regs : bvmap 5 word),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_DISCO_PEER_LOCK_INIT_STK -> spZ regs <= sp0 ->
st_ok_pi SEGS (@pa_val _ disco_listing PI) (Eimg (Ereg regs [])) ss_pl
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_disco_peer_lock_init)) memc (seg_rom SEGS))) /\
YCbn.sh_ok SEGS Bx_PL [] (Eimg (Ereg regs [])) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hal16 Hslo Hshi. split; [|constructor].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hs16 & Hstk0 & Hceil & Hlo0 & Hhi0 & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_DISCO_PEER_LOCK_INIT_STK = 4112) by reflexivity.
assert (Usp : bv_unsigned (YP0m.ew (Eimg (Ereg regs [])) 2) = spZ regs)
by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
rewrite YA0o.restrict_mkst_fx. unfold ss_pl. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- split; exact I.
- split; [|split; exact I].
cbn [YP0m.f_atoms YP0m.atoms_ok]. split; [|exact I]. unfold YP0m.afact_ok. cbn [YP0m.af_lo YP0m.af_hi YP0m.af_al2]. rewrite Usp.
change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia].
Qed.
Lemma pl_walk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (g : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 g ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_DISCO_PEER_LOCK_INIT_STK -> spZ regs <= sp0 ->
g mod 4 = 0 ->
0 <= g -> g + 12 <= 2 ^ 63 ->
(spZ regs <= g \/ g + 12 <= spZ regs - REAC_DISCO_PEER_LOCK_INIT_STK) ->
(forall a, g <= a < g + 12 ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) ->
amem_range g 12 ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF g 12 -> shadow_hull_vis (aview SEGS (w_H W) memc) g 12 ->
SRr SEGS W (cfg_at SEGS (BASE + AF_reac_disco_peer_lock_init) regs memc mdc)
(treac_disco_peer_lock_init_post fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs g).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g HJ Hra Hra4 Hgp Htp H10 Hal16 Hslo Hshi Hg4 Hg0 Hg63 Hgsp Hwr Hamr Hrad Hhull.
pose proof (@pa_segs_low _ _ PI) as Hsegs.
destruct (pl_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hal16 Hslo Hshi) as [HS SHOK].
pose proof HJ as HJ0.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hs16 & Hstk0 & Hceil & Hlo0 & Hhi0 & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_DISCO_PEER_LOCK_INIT_STK = 4112) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hgb : g + 12 <= 2 ^ 47) by (unfold amem_range in Hamr; lia).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env (@pa_val _ disco_listing PI) A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : YP0m.ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : YP0m.ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : YP0m.ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : YP0m.ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : YP0m.ew E 10 = Z_to_bv 64 g) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (HAE : YP06.env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Usp : bv_unsigned (YP0m.ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE.
unfold cfg_at.
change (w64 (BASE + AF_reac_disco_peer_lock_init)) with (Z_to_bv 64 (BASE + AF_reac_disco_peer_lock_init)).
paj_run_tok RUN HS HJ SHOK Bspan_PL;
[ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
[ reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil ]
| ].
rename HF into HF1, HG into HG1.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
assert (Qsp : spZ rg = spZ regs + -16) by (unfold spZ at 1; rewrite Rsp, Usp, YP03.unsigned_lit_small by lia; reflexivity);
assert (V1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview SEGS (w_H W) mm a = aview SEGS (w_H W) memc a)
by (intros a Ha Hn; apply (pl_view_frame _ _ _ E _ a HF1 Ha);
change (YP0l.ss_mem ss_pl) with [stack_region 16]; intros (r & [<- | []] & Hr);
cbn [stack_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite Usp in Hr; lia)
end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply SRr_bind;
[ eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA DS___asan_memset) (AMEMSET fx) W rg mm
STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k g 0 12 (spZ regs - 16 - sp0) _ HJ);
[ rewrite Ra0, E10; reflexivity
| rewrite Ra1; reflexivity
| rewrite Ra2; reflexivity
| lia
| lia
| lia
| rewrite Qsp; lia
| lia
| lia
| rewrite Hes; lia
| rewrite Rgp, E3; exact Hgp
| rewrite Rtp, E4; exact Htp
| exact Rra
| apply ret_ok_codeptr_v; [lia | reflexivity]
| intros a Ha; split; [exact (proj1 (Hwr a Ha)) | rewrite Hes; lia]
| exact Hamr
| apply (range_addressable_agree (aview SEGS (w_H W) memc)); [|exact Hrad];
intros x Hx; apply V1; unfold shadow_of_addr, SHADOW_OFF; lia
| intros _ s Hs; rewrite V1; [exact (Hhull s Hs) | |]; unfold shadow_addr, SHADOW_OFF in Hs; lia
| exact I ]
| ]
end.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Heff & Hfr & Hpres2).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
jafter_call_keep_pi HS 32%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hfr; [lia | lia | rewrite Hes; lia].
- intros _. apply (apresent_writable SEGS). apply HJpres. lia. }
clear HS. rewrite <- YA0o.restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 32 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
assert (HEI' : img_env (@pa_val _ disco_listing PI) A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall n, (n < 32)%nat -> YP0m.ew E' n = YP0m.ew E n) by (intros n Hn; rewrite HE'; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE' : YP06.env_agree 32 (Ereg regs []) E') by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (A10 : YP0m.ew E' 36 = getr regs2 10) by (rewrite HE'; reflexivity).
clear HE'.
assert (F1 : YP0m.ew E' 1 = getr regs 1) by (rewrite OLD by lia; exact E1).
assert (Usp' : bv_unsigned (YP0m.ew E' 2) = spZ regs) by (rewrite OLD by lia; exact Usp).
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
assert (SHOK' : YCbn.sh_ok SEGS Bx_PL [] E' (mrestrict (w_H W) mem2)) by constructor.
clear SHOK.
paj_run_tok RUN HS HJ2 SHOK' Bspan_PL;
[ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
[ reflexivity | rewrite Usp'; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil ]
| ].
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HF : frame_of _ ?rs mem2 (ms_mem ?msc) |- _ =>
prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
assert (V3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview SEGS (w_H W) (ms_mem msc) a = aview SEGS (w_H W) mem2 a)
by (intros a Ha Hn; apply (pl_view_frame _ _ _ _ _ a HF Ha);
let rs' := eval vm_compute in rs in change rs with rs'; intros (r & [<- | []] & Hr);
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite Usp' in Hr; lia);
assert (VALL : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 4112 <= a < spZ regs) -> ~ (g <= a < g + 12) ->
aview SEGS (w_H W) (ms_mem msc) a = aview SEGS (w_H W) memc a)
by (intros a Ha Hs Hga; rewrite V3 by lia; rewrite Hfr by (rewrite ?Hes; lia); apply V1; lia);
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
intros mat';
unfold treac_disco_peer_lock_init_post;
exists lyc, Sc, (ms_regs msc), (ms_mem msc); eexists
end.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJp3 & _).
split; [cbn [ms_regs]; rewrite R1, F1, Hra; reflexivity|].
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ E' _ _ regs [] HS); [exact HAE' | vm_compute; reflexivity]|].
split; [rewrite R1, F1; reflexivity|].
split; [rewrite R10, A10, Ha0, H10; reflexivity|].
split; [reflexivity|]. split; [apply Permutation_refl|].
split.
{ unfold treac_disco_peer_lock_init_kept. rewrite WS.
split; [intros a Ha Hs Hga; apply VALL; lia|].
split.
{ intros b m i Hin Hi Hgi.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & Hb4096 & Hbceil & _).
apply VALL; lia. }
split.
{ intros a Himg Hns Hne. pose proof (Hsegs a Himg) as Hlow. apply VALL; [lia | lia |].
intros Hga. destruct (Hwr a Hga) as [Hw _].
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ0 Hw)
as (_ & [[Hc _] | [(_ & b & n & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl _] _]])]]).
- lia.
- exact (blk_img SEGS B LAWS _ _ _ _ _ _ _ _ HAR Hbin Hr Himg).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. exact (frm_img SEGS B LAWS _ _ _ _ _ _ _ _ HAR Hin' Hr Himg).
- lia. }
split.
{ intros cid pos a Hin Hr Hga.
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfs0.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs0) as Hse.
unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
apply VALL; [lia | lia | exact Hga]. }
split; [intros a _ _ Hp; eapply apresent_grows; [exact HG|]; apply Hpres2; eapply apresent_grows; [exact HG1|]; exact Hp|].
intros a Ha. apply HJp3. lia. }
split; [|exact pl_lock0].
change (map (fun b : byte => bv_unsigned b) (repeat (CtrlParsed.zb 0) 12)) with (repeat 0 (Z.to_nat 12)).
apply pl_garr8; [lia|]. intros i Hi. rewrite V3 by lia. rewrite (Heff i) by lia. reflexivity.
Qed.
End w.
Theorem pb_reac_disco_peer_lock_init : treac_disco_peer_lock_init_spec.
Proof. intros fq. exact (pl_walk (fx := fq)). Qed.
End h.
End f.
End d.
