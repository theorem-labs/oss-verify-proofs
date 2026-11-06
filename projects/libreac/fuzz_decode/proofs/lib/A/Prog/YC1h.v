(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC1h.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC1h.v, ea5560a967b, carries it): the listing's names are dsym; frm_off_imgP states fuzz_boxreg.asan's image range as Reusable/YImgTop.v's [IMG_LO, IMG_TOP) in place of cgif's off_img (as DecodePaLib's blk_off_imgP does); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC1h.v at a working branch a8925bf9f4d for libreac/fuzz_decode's program walk; module prefix, the listing's symbol type (bsym -> dsym) and the unit file names (BoxSyms / BoxPa / BoxPaLib / BoxList -> the Decode names) changed; in frm_off_imgP, pa_img_cover gets am_layout of AR's amem part, because decode's DecodePa.pa_img_cover takes layout_ok ly (as DecodePaLib's blk_off_imgP does), and the image bullet cites YImgTop's IMG_lt, because decode's IMG_LO and IMG_TOP are definitions, not numerals; nothing else. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI08 YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaRun PaShadow PaJournal DecodeSyms DecodeList DecodePa DecodePaLib YC4b YC1g.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {L : ptable dsym} {PL : PAListing L} {PI : PAImg L}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).
Lemma img_env_havoc_hi : forall E k ws, img_env VAL A_LIM E -> (A_LIM <= k)%nat -> img_env VAL A_LIM (havoc E k ws).
Proof. intros E k ws HE Hk a Ha. rewrite ew_havoc_old by lia. exact (HE a Ha). Qed.
Lemma img_env_ewset_hi : forall E n w, img_env VAL A_LIM E -> (A_LIM <= n)%nat -> img_env VAL A_LIM (ewset E n w).
Proof. intros E n w HE Hn a Ha. rewrite ew_ewset_other by lia. exact (HE a Ha). Qed.
Lemma aview_above_of_journal : forall B STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k ->
forall a, sp0 <= a < 2 ^ 64 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W0) mem a.
Proof.
intros B STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k HJ a Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & _) & _).
apply F1; lia.
Qed.
Lemma st_ok_pi_havoc_hi : forall k E ss ms ws,
st_ok_pi SEGS VAL E ss ms -> ss_atoms_p (pband k (k + length ws)) ss = true ->
st_ok_pi SEGS VAL (havoc E k ws) ss ms.
Proof.
intros k E ss ms ws HS Hat. unfold st_ok_pi in *.
eapply (st_ok_agree_p (pband k (k + length ws)) SEGS); [exact HS | | destruct ss; exact Hat].
apply env_agree_p_havoc. apply le_n.
Qed.
Theorem st_ok_pi_after_call_hi : forall k E ss ms regs' mem' rs retk,
img_env VAL A_LIM E -> 0 <= retk < 2 ^ 40 ->
st_ok SEGS E ss ms ->
ss_resv ss = None ->
ss_atoms_p (pband k (k + 16)) ss = true ->
regions_wf rs = true -> no_cdata rs = true -> mem_atoms_p (pband k (k + 16)) rs = true ->
submem rs (ss_mem ss) ->
sr_get (ss_regs ss) 1 = SOff A_TEXT retk ->
aregs_preserved (ms_regs ms) regs' ->
Forall (region_kept SEGS E (ms_mem ms) mem') rs ->
st_ok_pi SEGS VAL (havoc E k (map (getr regs') CLOB)) (ss_after_call ss rs k retk)
(mkst regs' (Z_to_bv 64 (BASE + retk)) mem' (seg_rom SEGS)).
Proof.
intros k E ss ms regs' mem' rs retk HE Hrk HS Hrv Hat Hwf Hnc Hmat Hsub Hra HP Hkept.
unfold st_ok_pi, abs_ss, ss_after_call, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
pose proof (st_ok_mkst SEGS E ss ms HS Hrv) as Hshape. rewrite Hshape in HS.
pose proof (st_ok_splice_havoc_p SEGS k (k + 16) E ss (ms_regs ms) regs' (Z_to_bv 64 (ss_pc ss)) (BASE + retk)
(ms_mem ms) mem' rs [] CLOB HS (le_n _) Hat) as H.
cbn [map app] in H. apply H.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- reflexivity.
- exact Hmat.
- apply regs_preserved_frame. exact HP.
- constructor.
- apply (mem_ok_kept SEGS E (ms_mem ms) mem' rs); [| exact Hnc | exact Hkept].
eapply mem_ok_sub; [exact Hsub | exact Hwf | exact (st_ok_mem_ok SEGS E ss _ HS)].
Qed.
Theorem st_ok_pi_after_stretch_hi : forall k E ss ms regs' mem' rs retk (clob : list (bv 5)),
st_ok SEGS E ss ms ->
ss_resv ss = None ->
ss_atoms_p (pband k (k + length clob)) ss = true ->
regions_wf rs = true -> no_cdata rs = true -> mem_atoms_p (pband k (k + length clob)) rs = true ->
submem rs (ss_mem ss) ->
reg_nodup clob = true -> forallb (fun r : bv 5 => negb (bv_eqb r 0)) clob = true ->
(forall r, reg_in r clob = false -> getr regs' r = getr (ms_regs ms) r) ->
Forall (region_kept SEGS E (ms_mem ms) mem') rs ->
st_ok_pi SEGS VAL (havoc E k (map (getr regs') clob)) (ss_after_stretch ss rs k clob retk)
(mkst regs' (Z_to_bv 64 (BASE + retk)) mem' (seg_rom SEGS)).
Proof.
intros k E ss ms regs' mem' rs retk clob HS Hrv Hat Hwf Hnc Hmat Hsub Hnd Hnz Hsame Hkept.
unfold st_ok_pi, abs_ss, ss_after_stretch, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
pose proof (st_ok_mkst SEGS E ss ms HS Hrv) as Hshape. rewrite Hshape in HS.
pose proof (st_ok_splice_havoc_p SEGS k (k + length clob) E ss (ms_regs ms) regs' (Z_to_bv 64 (ss_pc ss)) (BASE + retk)
(ms_mem ms) mem' rs [] clob HS (le_n _) Hat) as H.
cbn [map app] in H. apply H.
- exact Hnd.
- exact Hnz.
- reflexivity.
- exact Hmat.
- exact Hsame.
- constructor.
- apply (mem_ok_kept SEGS E (ms_mem ms) mem' rs); [| exact Hnc | exact Hkept].
eapply mem_ok_sub; [exact Hsub | exact Hwf | exact (st_ok_mem_ok SEGS E ss _ HS)].
Qed.
Lemma st_ok_pi_submem : forall E ss ms rs,
st_ok_pi SEGS VAL E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof. intros E ss ms rs HS Hs Hwf. destruct ss as [pc0 sr0 fr0 sm0 rv0 fs0]. exact (st_ok_submem SEGS E _ ms rs HS Hs Hwf). Qed.
Lemma img_env_atomP : forall E a, img_env VAL A_LIM E -> (A_TEXT <= a < A_LIM)%nat -> ew E a = Z_to_bv 64 (VAL a).
Proof. intros E a HE Ha. rewrite <- (HE a Ha). symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma fshadow_not_app : forall F k p n a, 4096 <= F -> F + 8 * k <= 2 ^ 47 -> in_app p n ->
2147450880 + F / 8 <= a < 2147450880 + F / 8 + k -> p <= a < p + n -> False.
Proof.
intros F k p n a HF Hk Hin Ha Hp. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hin.
pose proof (Z.div_mod F 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M. lia.
Qed.
Lemma amem_range_sub_app : forall p n lo k, in_app p n -> p + n <= alloc_ceiling -> p <= lo -> lo + k <= p + n -> 0 <= k -> amem_range lo k.
Proof.
intros p n lo k Hin Hce Hlo Hhi Hk. apply amem_range_high; [exact Hk | | lia].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hin. lia.
Qed.
Lemma frm_off_imgP : forall B ly S (W : world SEGS) mem md cid pos,
AR SEGS B ly S W mem md -> In (cid, pos) (frames S) ->
frame_addr ly cid pos + fs_frame_bytes cid <= IMG_LO \/ IMG_TOP <= frame_addr ly cid pos.
Proof.
intros B ly S W mem md cid pos (M & LG & _) Hin. pose proof (pa_img_cover ly S md (am_layout _ _ _ _ M) LG) as [C1 C2].
pose proof (frame_facts B ly S _ cid pos M Hin) as (Fc & Fp & _ & _ & _ & _ & _ & _ & F64 & _).
destruct (Z.le_gt_cases (frame_addr ly cid pos + fs_frame_bytes cid) IMG_LO) as [|H1]; [left; lia|].
destruct (Z.le_gt_cases IMG_TOP (frame_addr ly cid pos)) as [|H2]; [right; lia|]. exfalso.
apply (client_byte_not_img B ly S _ (Z.max (frame_addr ly cid pos) IMG_LO) M).
- right. exists (cid, pos). split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. lia.
- unfold in_zr. pose proof IMG_lt. lia.
Qed.
End c.
End b.
Ltac jafter_call_keep_hi HS k regs2 mem2 HP idxs HS2 :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss ?ms =>
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "jafter_call_keep_hi: no img_env hypothesis for" E end in
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
let retk := eval vm_compute in (match sr_get (ss_regs ss) 1 with SOff _ z => z | _ => 0 end) in
pose proof (st_ok_pi_after_call_hi k E (abs_ss val ss) ms regs2 mem2 rs retk HEI ltac:(lia) HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) HP) as HS2;
let ss2 := eval vm_compute in (ss_after_call ss rs k retk) in
change (ss_after_call (abs_ss val ss) rs k retk) with ss2 in HS2
| st_ok ?segs ?E ?ss ?ms =>
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "jafter_call_keep_hi: no img_env hypothesis for" E end in
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
let retk := eval vm_compute in (match sr_get (ss_regs ss) 1 with SOff _ z => z | _ => 0 end) in
pose proof (st_ok_pi_after_call_hi k E ss ms regs2 mem2 rs retk HEI ltac:(lia) HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) HP) as HS2;
let ss2 := eval vm_compute in (ss_after_call ss rs k retk) in
change (ss_after_call ss rs k retk) with ss2 in HS2
end.
Ltac jafter_stretch_hi HS k regs2 mem2 clob retk HS2 :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss ?ms =>
let rs := eval vm_compute in (ss_mem ss) in
pose proof (st_ok_pi_after_stretch_hi k E (abs_ss val ss) ms regs2 mem2 rs retk clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) (submem_refl rs) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs k clob retk) in
change (ss_after_stretch (abs_ss val ss) rs k clob retk) with ss2 in HS2
| st_ok ?segs ?E ?ss ?ms =>
let rs := eval vm_compute in (ss_mem ss) in
pose proof (st_ok_pi_after_stretch_hi k E ss ms regs2 mem2 rs retk clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) (submem_refl rs) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs k clob retk) in
change (ss_after_stretch ss rs k clob retk) with ss2 in HS2
end.
Ltac jafter_stretch_keep_hi HS k regs2 mem2 clob retk idxs HS2 :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss ?ms =>
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
pose proof (st_ok_pi_after_stretch_hi k E (abs_ss val ss) ms regs2 mem2 rs retk clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs k clob retk) in
change (ss_after_stretch (abs_ss val ss) rs k clob retk) with ss2 in HS2
| st_ok ?segs ?E ?ss ?ms =>
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
pose proof (st_ok_pi_after_stretch_hi k E ss ms regs2 mem2 rs retk clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs k clob retk) in
change (ss_after_stretch ss rs k clob retk) with ss2 in HS2
end.
Ltac run_K_hi HS :=
lazymatch type of HS with
| st_ok_pi _ _ _ ?ss _ => eval vm_compute in (run_K A_LIM (SOff 32 0) [] ss)
| st_ok _ _ ?ss _ => eval vm_compute in (run_K A_LIM (SOff 32 0) [] ss)
end.
