(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan fake-stack vocabulary of the cgif walks at fuzz_reply's symbol type wsym:
   proofs/cgif/cgif_file_fuzzer/lib/YC44.v (fake-frame and shadow regions, the plain pi runs over the journal and the
   flag store that ends a fake frame), lib/YC1h.v (atoms above A_LIM, after-call with high atoms), lib/YC45.v (the
   plain pi run that stops at a call) and the generic lemmas of lib/A/AC8j.v.  Only the symbol type, the module paths
   and PALibF's two stack_malloc fields (fuzz_reply calls classes 0 and 1) change. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_frame.v, with its module paths, module names and numbers changed; 352 of its 746 lines of code are new or changed and 786 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: generic helpers of the symbolic engine (st_ok_pi at link's listing) that every
   image-A walk of link's own functions uses and that link's tree did not have: the register / region / fact
   updates of a symbolic state, the after-call splice with fresh atoms above the listing's atoms, the side-stack
   frame regions and their kept clauses, the realigned stack pointer (`andi sp, sp, -0x20`) and the shadow cell of
   an atom. Adapted (link's listing `lsym`, LinkSyms / LinkList / LinkPa / LinkPaLib) from libreac/fuzz_pcap's
   released lib/A/Prog/YC1g.v, YC1h.v, PcapFrame.v (Sections q, w, z and the definitions before them; not the
   flag-store release, which is lib/A/Prog/LinkWalkSide.v's) and PcapSourceOpen.v (its arithmetic of the
   realigned stack pointer and of a shadow cell, and its region-trimming tactics), origin/ossv/recipes.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI08 YI00 YI09 YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaJournal LinkSyms LinkList LinkPa LinkPaLib YC4b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* a register atom's value as a symbolic value *)
Lemma sv_off0 : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v H. cbn [sv_denot]. rewrite H.
pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 v)). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* ---- frame and shadow arithmetic (PcapSourceOpen.v) ---- *)
Lemma div8_in : forall p x, p mod 8 = 0 -> p <= x < p + 8 -> x / 8 = p / 8.
Proof.
intros p x H Hx. pose proof (Z_div_mod_eq_full p 8) as E. rewrite H, Z.add_0_r in E.
symmetry. apply (Z.div_unique x 8 (p / 8) (x - p)); [left; lia | lia].
Qed.
Lemma div8_of_mul64 : forall a, a mod 64 = 0 -> a / 8 = 8 * (a / 64) /\ a = 64 * (a / 64).
Proof.
intros a H. pose proof (Z_div_mod_eq_full a 64) as E. rewrite H, Z.add_0_r in E. split; [|exact E].
symmetry. apply (Z.div_unique a 8 (8 * (a / 64)) 0); [left; lia | lia].
Qed.
Lemma ra_frame : forall (rd rd' : Z -> option Z) a n,
  range_addressable rd SHADOW_OFF a n ->
  (forall x, a <= x < a + n -> rd' (shadow_of_addr SHADOW_OFF x) = rd (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable rd' SHADOW_OFF a n.
Proof. intros rd rd' a n HR Hk x Hx. destruct (HR x Hx) as (s & Hs & Ho). exists s. rewrite Hk by exact Hx. split; [exact Hs | exact Ho]. Qed.
(* x / 8 for x in a frame [f, f + nb) with f and nb multiples of 64 lies in the frame's shadow [f / 8, f / 8 + nb / 8). *)
Lemma div8_frame : forall f nb x, f mod 64 = 0 -> nb mod 64 = 0 -> f <= x < f + nb ->
  f / 8 <= x / 8 < f / 8 + nb / 8.
Proof.
intros f nb x Hf Hn Hx. destruct (div8_of_mul64 f Hf) as [Ef8 Ef]. destruct (div8_of_mul64 nb Hn) as [En8 En].
rewrite Ef8, En8. split.
- apply Z.div_le_lower_bound; lia.
- apply Z.div_lt_upper_bound; lia.
Qed.
Lemma sp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.

Lemma land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.

(* cgif_file_fuzzer lib/A/ACer.v:156-164 (origin/ossv/recipes c8557374ad2e). *)
Lemma denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. rewrite M64_val.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma denot_and_m32_add0 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff n c) (SLit (-32))) (SLit 0)) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r.
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)) as Hle. pose proof (Z.div_pos (v + c) 32 ltac:(lia) ltac:(lia)) as Hp.
assert (HU : U E (SAlu ALU_AND (SOff n c) (SLit (-32))) = 32 * ((v + c) / 32)).
{ unfold U. rewrite (denot_and_m32 E n v c Hn H0 H1 Hv). apply unsigned_lit_small. lia. }
rewrite HU. apply zcanon_id. rewrite M64_val. lia.
Qed.
(* The shadow cell of an atom: (x >> 3) + B. *)
Lemma denot_shadow_cell : forall E n m v base,
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> ew E m = Z_to_bv 64 base -> 0 <= base -> base + v / 8 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (base + v / 8).
Proof.
intros E n m v base Hn Hv Hm Hb Hs. rewrite denot_lit_U. f_equal.
assert (Hd : 0 <= v / 8) by (apply Z.div_pos; lia).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
change (Z.land (zcanon 3) 63) with 3.
rewrite (U_atom_off E n v 0 Hn ltac:(lia) ltac:(lia)), (U_atom_off E m base 0 Hm ltac:(lia) ltac:(lia)).
rewrite !Z.add_0_r. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id (v / 8)) by (rewrite M64_val; lia). rewrite zcanon_id by (rewrite M64_val; lia). lia.
Qed.

(* ---- state updates (YC1g.v, YC1h.v) ---- *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {L : ptable lsym} {PL : PAListing L} {PI : PAImg L}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).
Lemma st_ok_pi_set_reg : forall E ss ms (r : bv 5) e,
st_ok_pi SEGS VAL E ss ms -> r <> 0%bv -> getr (ms_regs ms) r = sv_denot E e ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr He. unfold st_ok_pi, abs_ss, setpc in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
exact (st_ok_set_reg SEGS E (mkSST (BASE + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms r e HS Hr He).
Qed.
Lemma st_ok_pi_region_nth : forall E ss ms i r,
st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof. intros E ss ms i r HS Hi. exact (st_ok_region_nth E (abs_ss VAL ss) ms i r HS ltac:(destruct ss; exact Hi)). Qed.
Lemma ew_Eimg_Ereg_nat : forall (regs : bvmap 5 word) extra n (r : bv 5),
Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs extra)) n = getr regs r.
Proof.
intros regs extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
End f.
End d.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {L : ptable lsym} {PL : PAListing L} {PI : PAImg L}.
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
AR SEGS B ly S W mem md -> In (cid, pos) (frames S) -> off_img (frame_addr ly cid pos) (fs_frame_bytes cid).
Proof.
intros B ly S W mem md cid pos (M & LG & _) Hin. unfold off_img. pose proof (pa_img_cover ly S md LG) as [C1 C2].
pose proof (frame_facts B ly S _ cid pos M Hin) as (Fc & Fp & _ & _ & _ & _ & _ & _ & F64 & _).
destruct (Z.le_gt_cases (frame_addr ly cid pos + fs_frame_bytes cid) 0x10000) as [|H1]; [left; unfold YImgTop.IMG_LO in *; lia|].
destruct (Z.le_gt_cases pcap_img_end (frame_addr ly cid pos)) as [|H2]; [right; unfold pcap_img_end, YImgTop.IMG_TOP in *; lia|]. exfalso.
apply (client_byte_not_img B ly S _ (Z.max (frame_addr ly cid pos) 0x10000) M).
- right. exists (cid, pos). split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. lia.
- unfold in_zr. unfold pcap_img_end, YImgTop.IMG_TOP, YImgTop.IMG_LO in *. lia.
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

(* ---- side-stack frame regions and their kept clauses (PcapFrame.v) ---- *)
Definition set_window (r : YP09.region) (wlo whi : Z) : YP09.region :=
YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) wlo whi (YP09.r_chunks r).
Fixpoint list_upd {A} (l : list A) (i : nat) (x : A) : list A :=
match l, i with
| [], _ => []
| _ :: t, O => x :: t
| h :: t, S i' => h :: list_upd t i' x
end.
Lemma zall_disjoint_of_all : forall E r rs,
all_disjoint E r rs -> zall_disjoint (extent_of_region E r) (map (extent_of_region E) rs).
Proof.
intros E r rs. induction rs as [|r' rs IH]; cbn; intros H; [exact I|].
destruct H as [H1 H2]. split; [|exact (IH H2)]. unfold zdisj, extent_of_region, extent_disjoint in *. cbn [fst snd]. exact H1.
Qed.
Lemma zpairwise_of_pairwise : forall E rs,
pairwise_disjoint E rs -> zpairwise_disjoint (map (extent_of_region E) rs).
Proof.
intros E rs. induction rs as [|r rs IH]; cbn; intros H; [exact I|].
destruct H as [H1 H2]. split; [exact (zall_disjoint_of_all E r rs H1) | exact (IH H2)].
Qed.
Lemma map_extent_list_upd : forall E rs i r r',
nth_error rs i = Some r -> extent_of_region E r' = extent_of_region E r ->
map (extent_of_region E) (list_upd rs i r') = map (extent_of_region E) rs.
Proof.
intros E rs. induction rs as [|h t IH]; intros [|i] r r' Hn He; cbn in *; try discriminate.
- injection Hn as ->. rewrite He. reflexivity.
- rewrite (IH i r r' Hn He). reflexivity.
Qed.
Lemma Forall_list_upd : forall {A} (P : A -> Prop) (l : list A) i x,
Forall P l -> P x -> Forall P (list_upd l i x).
Proof.
intros A P l. induction l as [|h t IH]; intros [|i] x Hl Hx; cbn; [exact Hl | exact Hl | |]; inversion Hl; subst; constructor; auto.
Qed.
Definition uar_got_regionP (u : nat) : YP09.region :=
YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff u 0))].
Definition uar_cell_regionP (u : nat) : YP09.region :=
YP09.mkRegion (Some u) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))].
Definition obj8_region (i : nat) (v : sv) : YP09.region := YP09.mkRegion (Some (A_OBJ i)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 v)].
Definition const8_region (a v : Z) : YP09.region := YP09.mkRegion None a (a + 8) 0 0 [YP09.mkChunk a (CVal 8 (SLit v))].
Definition fframe_region (f fl : nat) (cid : Z) (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some f) 0 (fs_frame_bytes cid) 0 (fs_frame_bytes cid) (cs ++ [YP09.mkChunk (fs_frame_bytes cid - 8) (CVal 8 (SOff fl 0))]).
Definition fshadow_region (s : nat) (cid wlo whi : Z) (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some s) 0 (fs_frame_bytes cid / 8) wlo whi cs.
Definition HPTR (al : Z) : afact := mkAF 4096 140737479966720 al.
Lemma aregs_preserved_eqs : forall regs0 regs2 : bvmap 5 word,
getr regs2 2 = getr regs0 2 -> getr regs2 3 = getr regs0 3 -> getr regs2 4 = getr regs0 4 ->
getr regs2 8 = getr regs0 8 -> getr regs2 9 = getr regs0 9 ->
getr regs2 18 = getr regs0 18 -> getr regs2 19 = getr regs0 19 -> getr regs2 20 = getr regs0 20 ->
getr regs2 21 = getr regs0 21 -> getr regs2 22 = getr regs0 22 -> getr regs2 23 = getr regs0 23 ->
getr regs2 24 = getr regs0 24 -> getr regs2 25 = getr regs0 25 -> getr regs2 26 = getr regs0 26 ->
getr regs2 27 = getr regs0 27 -> aregs_preserved regs0 regs2.
Proof.
intros regs0 regs2 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 r Hr.
assert (Hr0 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
clear Hr. repeat (destruct Hr0 as [-> | Hr0]; [assumption|]). subst r. assumption.
Qed.
Lemma count_cid_le_length : forall cid l, count_cid cid l <= Z.of_nat (length l).
Proof. intros cid l. induction l as [|[c p] l IH]; cbn; [lia|]. destruct (c =? cid); lia. Qed.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Fixpoint zseps_from (b : Z * Z) (l : list (Z * Z)) : Prop :=
match l with [] => True | c :: r => (fst b + snd b <= fst c \/ fst c + snd c <= fst b) /\ zseps_from b r end.
Fixpoint zseps (l : list (Z * Z)) : Prop := match l with [] => True | b :: r => zseps_from b r /\ zseps r end.
Lemma val_mem_of_rd32 : forall segs H mem a v,
rd32 (aview segs H mem) a v -> val_mem segs (mrestrict H mem) a 4 v.
Proof.
intros segs H mem a v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
Lemma rdword_of_val_mem : forall segs H mem a v,
val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hr.
assert (B : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.
Lemma region_ok_rewindow : forall segs E m r wlo whi,
region_ok segs E m r ->
(forall o, wlo <= o < whi -> writable_at segs m (base_val E (YP09.r_base r) + o)) ->
region_ok segs E m (set_window r wlo whi).
Proof.
intros segs E m r wlo whi (H1 & H2 & H3 & H4) Hw. unfold region_ok, set_window.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [exact H1|]. split; [exact H2|]. split; [exact Hw | exact H4].
Qed.
Lemma ast_ok_set_region : forall segs E ss ms i r r',
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some r ->
extent_of_region E r' = extent_of_region E r ->
regions_wf (list_upd (ss_mem ss) i r') = true ->
region_ok segs E (ms_mem ms) r' ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) (list_upd (ss_mem ss) i r') (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros segs E ss ms i r r' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hn He Hwf' Hr'.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
split; [exact Hwf'|]. split; [exact (Forall_list_upd _ _ i r' Hok Hr')|].
apply pairwise_disjoint_of_extents. rewrite (map_extent_list_upd E _ i r r' Hn He). apply zpairwise_of_pairwise. exact Hpd.
Qed.
Lemma atoms_ok_pick : forall E l idx, atoms_ok E l -> atoms_ok E (pick l idx).
Proof.
intros E l idx H. induction idx as [|i idx IH]; cbn; [exact I|].
destruct (nth_error l i) as [[n f]|] eqn:Hn; [|exact IH].
cbn. split; [|exact IH].
apply nth_error_In in Hn. revert Hn. clear - H. induction l as [|[n' f'] l IHl]; cbn; intros Hin; [destruct Hin|].
destruct H as [H1 H2]. destruct Hin as [E1 | Hin]; [injection E1 as -> ->; exact H1 | exact (IHl H2 Hin)].
Qed.
Lemma st_ok_pick_facts : forall segs E ss ms ai ci li,
st_ok segs E ss ms ->
st_ok segs E (set_facts ss (mkFacts (pick (f_atoms (ss_facts ss)) ai) (pick (f_conds (ss_facts ss)) ci) (pick (f_alias (ss_facts ss)) li))) ms.
Proof.
intros segs E ss ms ai ci li HS. apply st_ok_set_facts; [exact HS|].
destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & (Ha & Hc & Hl)).
pose proof (facts_ok_prune E (ss_facts ss) ci li (conj Ha (conj Hc Hl))) as (_ & Hc' & Hl').
split; [apply atoms_ok_pick; exact Ha | split; [exact Hc' | exact Hl']].
Qed.
Lemma val_mem_moved : forall segs H H' (m m' : word -> option byte) a b n v,
(forall k, 0 <= k < Z.of_nat n -> aview segs H' m' (b + k) = aview segs H m (a + k)) ->
val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') b n v.
Proof.
intros segs H H' m m' a b n v Hk Hv k Hkn. specialize (Hk (Z.of_nat k) ltac:(lia)). unfold aview in Hk.
rewrite (Hv k Hkn) in Hk. destruct (mbyte segs (mrestrict H' m') (b + Z.of_nat k)) as [b'|]; cbn in Hk; [|discriminate].
injection Hk as Hk. f_equal. apply bv_eq. exact Hk.
Qed.
Lemma atoms_ok_incl : forall E l l', (forall x, In x l' -> In x l) -> atoms_ok E l -> atoms_ok E l'.
Proof.
intros E l l' Hi H. induction l' as [|[n f] l' IH]; cbn; [exact I|].
split; [|apply IH; intros x Hx; apply Hi; right; exact Hx].
assert (Hin : In (n, f) l) by (apply Hi; left; reflexivity). clear - H Hin.
induction l as [|[n' f'] l IHl]; cbn in *; [destruct Hin|].
destruct H as [H1 H2]. destruct Hin as [E1 | Hin]; [injection E1 as -> ->; exact H1 | exact (IHl H2 Hin)].
Qed.
Lemma alias_ok_incl : forall E l l', (forall x, In x l' -> In x l) -> alias_ok E l -> alias_ok E l'.
Proof.
intros E l l' Hi H. induction l' as [|[a b] l' IH]; cbn; [exact I|].
split; [|apply IH; intros x Hx; apply Hi; right; exact Hx].
assert (Hin : In (a, b) l) by (apply Hi; left; reflexivity). clear - H Hin.
induction l as [|[a' b'] l IHl]; cbn in *; [destruct Hin|].
destruct H as [H1 H2]. destruct Hin as [E1 | Hin]; [injection E1 as -> ->; exact H1 | exact (IHl H2 Hin)].
Qed.
Lemma st_ok_facts_incl : forall segs E ss ms fa al,
st_ok segs E ss ms ->
(forall x, In x fa -> In x (f_atoms (ss_facts ss))) -> (forall x, In x al -> In x (f_alias (ss_facts ss))) ->
st_ok segs E (set_facts ss (mkFacts fa [] al)) ms.
Proof.
intros segs E ss ms fa al HS Hfa Hal. apply st_ok_set_facts; [exact HS|].
destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & (Ha & Hc & Hl)).
split; [exact (atoms_ok_incl E _ _ Hfa Ha)|]. split; [exact I | exact (alias_ok_incl E _ _ Hal Hl)].
Qed.
Lemma st_ok_facts_incl3 : forall segs E ss ms fa cs al,
st_ok segs E ss ms ->
(forall x, In x fa -> In x (f_atoms (ss_facts ss))) -> (forall x, In x cs -> In x (f_conds (ss_facts ss))) ->
(forall x, In x al -> In x (f_alias (ss_facts ss))) ->
st_ok segs E (set_facts ss (mkFacts fa cs al)) ms.
Proof.
intros segs E ss ms fa cs al HS Hfa Hcs Hal. apply st_ok_set_facts; [exact HS|].
destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & (Ha & Hc & Hl)).
split; [exact (atoms_ok_incl E _ _ Hfa Ha)|]. split; [| exact (alias_ok_incl E _ _ Hal Hl)].
apply (proj2 (conds_ok_forall E cs)). intros c Hin. exact (proj1 (conds_ok_forall E _) Hc c (Hcs c Hin)).
Qed.
Lemma st_ok_cond_In : forall segs E ss ms c,
st_ok segs E ss ms -> In c (f_conds (ss_facts ss)) -> acond_ok E c.
Proof.
intros segs E ss ms c HS Hin. destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & Hc & _)).
exact (proj1 (conds_ok_forall E _) Hc c Hin).
Qed.
Lemma ast_ok_set_reg_fp : forall segs E ss ms (r : bv 5) e,
st_ok segs E ss ms -> bv_eqb r 0 = false -> sv_denot E e = getr (ms_regs ms) r ->
st_ok segs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros segs E ss ms r e HS Hr0 He. apply st_ok_regs; [exact HS|].
intros rr. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. rewrite He. apply (st_ok_reg segs E ss ms r HS).
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
Lemma st_ok_havoc : forall segs k E ss ms ws,
st_ok segs E ss ms -> ss_atoms_lt k ss = true -> st_ok segs (havoc E k ws) ss ms.
Proof.
intros segs k E ss ms ws HS Hk. eapply st_ok_agree; [exact HS | | exact Hk].
apply (env_agree_havoc_ge k k E E ws ltac:(lia) (env_agree_refl k E)).
Qed.
Lemma aview_of_val_mem1 : forall segs H mem a v,
val_mem segs (mrestrict H mem) a 1 v -> 0 <= v < 256 -> aview segs H mem a = Some v.
Proof.
intros segs H mem a v Hv Hr. unfold aview. specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv. rewrite Hv. cbn [option_map].
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YO0f.le_byte.
change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.shiftr_0_r. rewrite !Z.mod_mod by lia. apply Z.mod_small. exact Hr.
Qed.
Lemma range_addressable_partial : forall (rd : Z -> option Z) Bs p k,
rd (shadow_of_addr Bs p) = Some k -> p mod 8 = 0 -> 0 <= k < 8 -> range_addressable rd Bs p k.
Proof.
intros rd Bs p k Hk Hp Hr x Hx. exists k.
pose proof (Z.div_mod p 8 ltac:(lia)) as D. rewrite Hp, Z.add_0_r in D.
assert (Hq : x / 8 = p / 8) by (symmetry; apply (Z.div_unique x 8 (p / 8) (x - p)); lia).
assert (Hg : shadow_of_addr Bs x = shadow_of_addr Bs p) by (unfold shadow_of_addr; rewrite Hq; reflexivity).
rewrite Hg, Hk. split; [reflexivity|]. destruct (Z.eq_dec k 0) as [-> | Hnz]; [left; reflexivity | right].
assert (Hxm : x mod 8 = x - p) by (rewrite (Z.mod_eq x 8), Hq by lia; lia).
lia.
Qed.
Section q.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Lemma frame_al64 : forall ly S W mem md cid pos,
AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0 /\ 64 <= fs_frame_bytes cid.
Proof.
intros ly S W mem md cid pos [M _] Hin.
destruct (frame_facts B ly S _ cid pos M Hin) as (_ & _ & _ & _ & Hpg & _ & _ & Hoff & H64 & Hb & _).
unfold frame_addr, page_aligned in *. split; [|split; [exact Hb | exact H64]].
rewrite Z.add_mod, Hoff, Z.add_0_r, Z.mod_mod by lia.
replace (ly_F ly) with (64 * (ly_F ly / 4096 * 64)) by (pose proof (Z.div_mod (ly_F ly) 4096 ltac:(lia)); lia).
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma shadow_hull_vis_of_frame : forall ly S W mem md cid pos d n,
AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
frame_addr ly cid pos <= d -> d + n <= frame_addr ly cid pos + fs_frame_bytes cid -> 0 < n ->
shadow_hull_vis (aview segs (w_H W) mem) d n.
Proof.
intros ly S W mem md cid pos d n HAR Hin Hfd Hdn Hn s Hs.
destruct (frame_al64 ly S W mem md cid pos HAR Hin) as (Hal & Hbal & Hb64).
destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & _ & _ & Hsh).
set (f := frame_addr ly cid pos) in *. set (bs := fs_frame_bytes cid) in *.
pose proof (Z.div_mod f 64 ltac:(lia)) as Df. pose proof (Z.div_mod bs 64 ltac:(lia)) as Db.
assert (E8f : f / 8 = 8 * (f / 64)) by (rewrite Hal, Z.add_0_r in Df; rewrite Df at 1; replace (64 * (f / 64)) with (8 * (f / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (E8b : bs / 8 = 8 * (bs / 64)) by (rewrite Hbal, Z.add_0_r in Db; rewrite Db at 1; replace (64 * (bs / 64)) with (8 * (bs / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (Hsf : shadow_addr f = 8 * (268431360 + f / 64)) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (L1 : shadow_addr f <= shadow_addr d / 8 * 8).
{ pose proof (shadow_mono f d Hfd) as M1. rewrite Hsf. rewrite Hsf in M1.
assert (268431360 + f / 64 <= shadow_addr d / 8) by (apply Z.div_le_lower_bound; lia). lia. }
assert (L2 : shadow_addr (d + n - 1) / 8 * 8 + 8 <= shadow_addr f + bs / 8).
{ assert (M2 : shadow_addr (d + n - 1) < shadow_addr f + bs / 8).
{ unfold shadow_addr in *. assert ((d + n - 1) / 8 < f / 8 + bs / 8) by (apply Z.div_lt_upper_bound; lia). lia. }
rewrite Hsf, E8b in M2. rewrite Hsf, E8b.
assert (shadow_addr (d + n - 1) / 8 < 268431360 + f / 64 + bs / 64) by (apply Z.div_lt_upper_bound; lia). lia. }
specialize (Hsh (s - shadow_addr f) ltac:(lia)). replace (shadow_addr f + (s - shadow_addr f)) with s in Hsh by lia.
apply (aview_some_of_apresent segs). exact (proj1 Hsh).
Qed.
Lemma region_kept_block_ajw2 : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs b m ly2 S2 md2,
acall_kept segs B lyc Sc W memc W2 mem2 slo shi Er -> AR segs B ly2 S2 W2 mem2 md2 -> In (b, m) (ablocks B ly2 S2) ->
bv_unsigned (ew E n) = b -> In (b, m) (ablocks B lyc Sc) -> 0 <= lo -> hi <= req_size m -> lo <= wlo -> whi <= hi ->
(forall a, b + lo <= a < b + hi -> ~ Er a) ->
region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs b m ly2 S2 md2 (_ & K2 & _) HAR2 Hin2 Hn Hin Hlo Hhi Hwlo Hwhi HnE.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hin2) as (_ & _ & _ & _ & Hpres2 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia|].
replace (b + (a - b)) with a by lia. apply HnE. exact Ha.
- intros _. apply (apresent_writable segs). apply (proj1 (Hpres2 a ltac:(lia))).
Qed.
Lemma awr_new_block_any : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 res n blc i lyq ownq,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
AR segs B ly2 S2 W2 mem2 md2 -> ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] -> 0 <= n ->
In (res, n) blc -> 0 <= i < req_size n ->
awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (res + i).
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 res n blc i lyq ownq HJ HAR2 Ebl Hn Hin Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (res, n) (ablocks B ly S)) as [H0 | H0].
- destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (res, n) (ablocks B lyc Sc)) as [Hc | Hc].
+ exfalso. apply in_split in Hc as (l1 & l2 & E1).
pose proof (sep_blocks_pos segs B LAWS ly2 S2 W2 mem2 md2 (res, n) (res, n) l1 l2 [] HAR2) as Hd.
rewrite Ebl, E1, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
assert (0 < req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); cbn; lia). lia.
+ right. left. split; [exact (Hgone res n i H0 Hc Hi)|]. exists res, n. split; [exact Hin | lia].
- right. right. left. exists res, n. split; [exact Hin|]. split; [exact H0 | lia].
Qed.
End q.
Section w.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Lemma region_kept_frame_aj : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs b cid pos,
acall_kept segs B lyc Sc W memc W2 mem2 slo shi Er ->
bv_unsigned (ew E n) = b -> In (cid, pos) (frames Sc) ->
frame_addr lyc cid pos <= b + lo -> b + hi <= frame_addr lyc cid pos + fs_frame_bytes cid -> whi <= wlo ->
(forall a, b + lo <= a < b + hi -> ~ Er a) ->
region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs b cid pos (_ & _ & _ & K4 & _) Hn Hin Hlo Hhi Hro HnE.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha; [|lia].
apply (mbyte_of_aview segs). apply (K4 cid pos a Hin); [|apply HnE; exact Ha].
left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
Qed.
Lemma region_kept_ownframe_aj : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs b cid pos,
acall_kept segs B lyc Sc W memc W2 mem2 slo shi Er ->
bv_unsigned (ew E n) = b -> In (cid, pos) (frames Sc) ->
((frame_addr lyc cid pos <= b + lo /\ b + hi <= frame_addr lyc cid pos + fs_frame_bytes cid) \/
(shadow_addr (frame_addr lyc cid pos) <= b + lo /\ b + hi <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8)) ->
(forall a, b + lo <= a < b + hi -> ~ Er a) ->
(forall a, b + wlo <= a < b + whi -> apresent (w_H W2) mem2 a) ->
region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs b cid pos (_ & _ & _ & K4 & _) Hn Hin Hrng HnE Hpres.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply (K4 cid pos a Hin); [|apply HnE; exact Ha].
destruct Hrng as [[H1 H2] | [H1 H2]]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; lia.
- intros _. apply (apresent_writable segs). apply Hpres. exact Ha.
Qed.
End w.
Section z.
Context {L : ptable lsym} {PI : PAImg L}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
Lemma ast_ok_pi_set_region : forall E ss ms i r r',
st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r ->
extent_of_region E r' = extent_of_region E r ->
regions_wf (list_upd (ss_mem ss) i r') = true ->
region_ok SEGS E (ms_mem ms) r' ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) (list_upd (ss_mem ss) i r') (ss_resv ss) (ss_facts ss)) ms.
Proof. intros E ss ms i r r' HS Hn He Hw Hr. destruct ss as [p0 r0 f0 m0 v0 g0]. exact (ast_ok_set_region SEGS E _ ms i r r' HS Hn He Hw Hr). Qed.
Lemma st_ok_pi_pick_facts : forall E ss ms ai ci li,
st_ok_pi SEGS VAL E ss ms ->
st_ok_pi SEGS VAL E (set_facts ss (mkFacts (pick (f_atoms (ss_facts ss)) ai) (pick (f_conds (ss_facts ss)) ci) (pick (f_alias (ss_facts ss)) li))) ms.
Proof. intros E ss ms ai ci li HS. destruct ss as [p0 r0 f0 m0 v0 g0]. exact (st_ok_pick_facts SEGS E _ ms ai ci li HS). Qed.
Lemma st_ok_pi_facts_incl : forall E ss ms fa al,
st_ok_pi SEGS VAL E ss ms ->
(forall x, In x fa -> In x (f_atoms (ss_facts ss))) -> (forall x, In x al -> In x (f_alias (ss_facts ss))) ->
st_ok_pi SEGS VAL E (set_facts ss (mkFacts fa [] al)) ms.
Proof. intros E ss ms fa al HS H1 H2. destruct ss as [p0 r0 f0 m0 v0 g0]. exact (st_ok_facts_incl SEGS E _ ms fa al HS H1 H2). Qed.
Lemma st_ok_pi_facts_incl3 : forall E ss ms fa cs al,
st_ok_pi SEGS VAL E ss ms ->
(forall x, In x fa -> In x (f_atoms (ss_facts ss))) -> (forall x, In x cs -> In x (f_conds (ss_facts ss))) ->
(forall x, In x al -> In x (f_alias (ss_facts ss))) ->
st_ok_pi SEGS VAL E (set_facts ss (mkFacts fa cs al)) ms.
Proof. intros E ss ms fa cs al HS H1 H2 H3. destruct ss as [p0 r0 f0 m0 v0 g0]. exact (st_ok_facts_incl3 SEGS E _ ms fa cs al HS H1 H2 H3). Qed.
Lemma st_ok_pi_cond_In : forall E ss ms c,
st_ok_pi SEGS VAL E ss ms -> In c (f_conds (ss_facts ss)) -> acond_ok E c.
Proof. intros E ss ms c HS Hin. destruct ss as [p0 r0 f0 m0 v0 g0]. exact (st_ok_cond_In SEGS E _ ms c HS Hin). Qed.
Lemma ast_ok_pi_set_reg_fp : forall E ss ms (r : bv 5) e,
st_ok_pi SEGS VAL E ss ms -> bv_eqb r 0 = false -> sv_denot E e = getr (ms_regs ms) r ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof. intros E ss ms r e HS Hr He. destruct ss as [p0 r0 f0 m0 v0 g0]. exact (ast_ok_set_reg_fp SEGS E _ ms r e HS Hr He). Qed.
Lemma st_ok_pi_havoc : forall k E ss ms ws,
st_ok_pi SEGS VAL E ss ms -> ss_atoms_p (pband k A_TEXT) ss = true -> (k + length ws <= A_TEXT)%nat ->
st_ok_pi SEGS VAL (havoc E k ws) ss ms.
Proof.
intros k E ss ms ws HS Hat Hk. unfold st_ok_pi in *.
eapply (st_ok_agree_p (pband k A_TEXT) SEGS); [exact HS | | destruct ss; exact Hat].
split; [| reflexivity]. intros n Hn. unfold pband in Hn.
apply Bool.orb_true_iff in Hn. destruct Hn as [Hn|Hn];
[apply Nat.ltb_lt in Hn; apply ew_havoc_old; exact Hn | apply Nat.leb_le in Hn; apply ew_havoc_above; lia].
Qed.
Lemma st_ok_pi_add_alias : forall E ss ms e1 e2,
st_ok_pi SEGS VAL E ss ms -> sv_denot E e1 = sv_denot E e2 ->
st_ok_pi SEGS VAL E (set_facts ss (mkFacts (f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) ((e1, e2) :: f_alias (ss_facts ss)))) ms.
Proof. intros E ss ms e1 e2 HS He. destruct ss as [p0 r0 f0 m0 v0 g0]. exact (st_ok_add_alias SEGS E _ ms e1 e2 HS He). Qed.
End z.
End g.

(* ---- region trimming and the tactics of a walk (PcapSourceOpen.v) ---- *)
(* A register's symbolic value, not normalized (prreg normalizes it). *)
Ltac prreg_raw HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.

(* Region trimming (cgif_file_fuzzer lib/A/ACer.v:24-25, 86-91, 131-139). *)
Definition chunk_in (lo hi : Z) (c : YP09.chunk) : bool :=
  Z.leb lo (YP09.c_off c) && Z.leb (YP09.c_off c + YP09.c_len c) hi.
Definition trim_region (r : YP09.region) (lo hi : Z) : YP09.region :=
  YP09.mkRegion (YP09.r_base r) lo hi (Z.max (YP09.r_wlo r) lo) (Z.min (YP09.r_whi r) hi)
    (filter (chunk_in lo hi) (YP09.r_chunks r)).
Fixpoint trim_stack (rs : smem) (lo hi : Z) : smem :=
  match rs with
  | [] => []
  | r :: t => match YP09.r_base r with
              | Some 2%nat => trim_region r lo hi :: t
              | _ => r :: trim_stack t lo hi end end.
(* The first n regions made read-only (their chunks kept). *)
Fixpoint ro_upto (n : nat) (rs : smem) : smem :=
  match n, rs with
  | S n', r :: t => YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) 0 0 (YP09.r_chunks r) :: ro_upto n' t
  | _, _ => rs
  end.
Ltac subregion_tac :=
  unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
  split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|];
  let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc; cbn in Hc |- *;
  first [exact Hc | solve [destruct Hc] | tauto].
Ltac submem_to := repeat (first [apply submem_keep; [subregion_tac|] | apply submem_drop]); apply submem_nil.
Ltac norm_pi HS := lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let v := eval vm_compute in ss in change ss with v in HS end.
Ltac add_fact HS n f prf :=
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    let HS3 := fresh "HS3" in
    pose proof (st_ok_pi_add_fact Ev ssx msx n f HS ltac:(prf)) as HS3; clear HS; rename HS3 into HS; norm_pi HS end.
(* Disjointness of a new region from the state's regions, the atoms' values substituted. *)
(* A region of an st_ok_pi state, by index. *)
Ltac spregion HS i HR :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss ?ms =>
    let o := eval vm_compute in (nth_error (ss_mem ss) i) in
    lazymatch o with Some ?r =>
      pose proof (st_ok_pi_region_nth E ss ms i r HS ltac:(vm_compute; reflexivity)) as HR;
      cbn [ms_mem restrict mkst] in HR end end.
(* A chunk of a region, as val_mem. *)
Ltac fldv HR nn base off w e v :=
  lazymatch type of HR with region_ok _ ?Ex _ _ =>
    pose proof (field_of_region Ex _ nn base _ _ _ _ _ off w e v HR ltac:(eassumption)
      ltac:(cbn; repeat (first [left; reflexivity | right]))
      ltac:(apply sv_off0; eassumption) ltac:(cbn; lia) ltac:(cbn; lia)) end.
(* A register of an st_ok state, its symbolic value computed. *)
Ltac sreg HS r Hr :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr end.
(* A region of an st_ok state, by index. *)
Ltac sregion HS i HR :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let o := eval vm_compute in (nth_error (ss_mem ss) i) in
    lazymatch o with Some ?r =>
      pose proof (st_ok_region_nth (segs:=segs) E ss (restrict H ms) i r HS ltac:(vm_compute; reflexivity)) as HR;
      cbn [ms_mem restrict mkst] in HR end end.
Section vw. Context {fx : YK11.FPState}.
Variable SEGS : list Segment.
Lemma vm_frame : forall (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> mbyte SEGS m' x = mbyte SEGS m x) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v Hfr Hv k Hk. rewrite Hfr by lia. exact (Hv k Hk). Qed.
Lemma ms_shape_mkst : forall (msx : machine_state) r pcv m,
  msx = mkst r pcv m (seg_rom SEGS) ->
  ms_resv msx = None /\ ms_svc_pending msx = None /\ ms_rom msx = seg_rom SEGS /\
  ms_fregs msx = fp_regs /\ ms_fcsr msx = fp_csr /\ ms_pc_val msx = pcv.
Proof. intros msx r pcv m H. repeat split; rewrite H; reflexivity. Qed.
Lemma getr_rng : forall (rg : bvmap 5 word) (r : bv 5), 0 <= bv_unsigned (getr rg r) < 2 ^ 64.
Proof. intros rg r. exact (bv_unsigned_in_range _ (getr rg r)). Qed.
(* One byte of memory, from a one-byte val_mem. *)
Lemma aview_byte_of_val : forall (H : word -> bool) m a v,
  val_mem SEGS (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview SEGS H m a = Some v.
Proof.
intros H m a v Hv Hr. specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
rewrite (le_byte_small v 1%nat 0%nat ltac:(cbn; lia) ltac:(lia)) in Hv.
rewrite Z.mul_0_r, Z.shiftr_0_r in Hv. unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
Qed.
(* One byte of a zeroed chunk of a region (the name chunk_ok is shadowed here by the allocator's). *)
Lemma zero_byte_of_region : forall (Ex : env) (H : word -> bool) m (r : YP09.region) base off len j,
  region_ok SEGS Ex (mrestrict H m) r -> base_val Ex (YP09.r_base r) = base ->
  In (YP09.mkChunk off (CZero len)) (YP09.r_chunks r) -> 0 <= j < len ->
  aview SEGS H m (base + off + j) = Some 0.
Proof.
intros Ex H m r base off len j HR Hb Hin Hj.
destruct HR as (_ & _ & _ & HCh). rewrite Forall_forall in HCh.
pose proof (HCh _ Hin) as Hc. rewrite Hb in Hc.
destruct (Hc j ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val] in Hb1, Hb2. cbn in Hb1. injection Hb1 as <-.
unfold aview. rewrite Hb2. reflexivity.
Qed.
End vw.
Ltac vmf Hfr H := eapply vm_frame; [| exact H]; intros ?x ?Hx; apply Hfr.
