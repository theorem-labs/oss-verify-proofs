(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6bC9.v at f3898085bda (w6b_c9: the split
   head / call / tail and the assembly of e at J) for reac-pw/fuzz_headamp's image B: the statement is
   lib/AU/HPgW6bBase.v's hw6b_c9_stmt (the post HPgSteps.hdu_blk_postE with HPgCaseBJ.cj_wr and cj_J_R), the
   object is e62 at F+0x210 in the class-4 frame (4, pos), the copy's source facts come from HPgBase.hd_cstr, the
   call is lib/AU/HPgCaseB.v's cb_memcpy_at at 0x51d8c, the head and the tail are lib/AU/HPgW6bC9a.v's runs, and
   s7 = pp is set in the head and kept by the call. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the block lemma hw6b_c9
   of lib/AU/HPgW6bBase.v, ent_build's case 9 (the default arm of the `switch (kind % 10)`, pod.h:367-377) in
   LLVMFuzzerTestOneInput (0x80c40), from its entry 0x82004 to the join J 0x82618. Proves no function (kind:
   segment lemma).

   THE THREE PIECES.
     A  0x82004 .. the `jal` at 0x82054 (HPgW6bC9a.h9_A): through a0 := [R+0x130] = F + 0x210 (&e62) the head
        stores e62.type := 14, e62.body[0..4) := 14, e62.body[4..8) := 8; it loads s7 := [R+0x148] = pp, passes the
        two pointer-overflow tests on [R+0x118] = F + 0x218, and sets a0 := [R+0x40] = F + 0x220 (&e62.body[8]),
        a1 := 0x21160 (ent_build.s), a2 := 14, ra := 0x82058.
     B  __asan_memcpy(e62.body + 8, ent_build.s, 14) at 0x51d8c: the kernel's aintrin_realizes OCpy (the Section
        hypothesis MCPY) in its journal form HPgCaseB.cb_memcpy_at. Its premises: the 14 destination bytes lie in
        the frame for locals (4, pos) the harness holds (writable, in scope by hw6b_in's range_addressable and
        shadow hull over e62, application memory), and the source is the registered global ent_build.s with its
        13 bytes and the NUL (hw6b_s_ok = HPgBase.hd_cstr at 0x21160), in the image and so apart from the frame.
     C  0x82058 .. J 0x82618 (HPgW6bC9a.h9_C): e62.size := 24 through [R+0x130], t1 := s4 = |r|, s4 := &e62,
        a3 := s2 = c, s2 := [R+0x138] = pp + 0x4000.
   The registers the case leaves alone are callee-saved, so the call keeps them (h9_clob_cs); s2 and s4 carry c
   and |r| through the call the same way.

   WHY A's STORES DO NOT DISTURB THE COPY'S CHECKS. A writes only e62's first 16 bytes, which lie in the frame for
   locals, application memory (in_app): below kLowMemEnd or at or above kHighMemBeg (h9_F_band); the shadow bytes
   the copy's checks read, and their hull, lie in [kLowMemEnd, kHighMemBeg) (HPgMem.hm_shadow_band,
   HPgCaseBJ.cj_hull_band).

   AT J. e62 holds le32 14 ++ le32 24 ++ le32 14 ++ le32 8 ++ "reac.cfg.rate" ++ NUL ++ 74 zero bytes: the four
   words A and C store, the 14 bytes the copy brings from ent_build.s, and the tail of the 104 zero bytes
   hw6b_in gives. That list is Layout.ent_mem of Model.ent_build's default pod, Ent POD_STRUCT 24 (le32 14 ++
   le32 POD_STRING ++ S9 ++ [NUL] ++ zeros 2), and ent_build reads no byte after the kind byte, so a3 = c,
   t1 = |r|. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgSteps HPgCaseBJ.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgCaseB HPgW6bBase HPgW6bC9a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the bytes [a, a + n) of zeros n *)
Lemma h9_zeros : forall H mem a n,
  (forall i, 0 <= i < Z.of_nat n -> aview rsegs H mem (a + i) = Some 0) -> hm_bytes rsegs H mem a (zeros n).
Proof.
intros H mem a n Hz. apply (proj2 (hm_bytes_aview rsegs H mem a (zeros n))). intros i Hi.
unfold zeros in *. rewrite repeat_length in Hi. unfold NUL. rewrite nth_repeat.
rewrite (Hz (Z.of_nat i) ltac:(lia)). reflexivity.
Qed.
Lemma h9_app : forall H mem a l1 l2 n a2, Z.of_nat (length l1) = n -> a2 = a + n ->
  hm_bytes rsegs H mem a l1 -> hm_bytes rsegs H mem a2 l2 -> hm_bytes rsegs H mem a (l1 ++ l2).
Proof.
intros H mem a l1 l2 n a2 Hn -> B1 B2. apply hm_bytes_app. split; [exact B1|]. rewrite Hn. exact B2.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the frame for locals lies below the low shadow band or above the high one (in_app), below 2^47 *)
Lemma h9_F_band : forall F, in_app F 1024 -> F + 1024 <= alloc_ceiling ->
  (F + 1024 <= 0x7fff8000 \/ 0x10007fff8000 <= F) /\ F + 1024 <= 0x7fffff800000.
Proof.
intros F (_ & HA) Hc. pose proof (@asan_consts rc) as (Hc0 & _).
split; [|lia]. destruct HA as [Hl | (Hh & _)].
- left. unfold kLowShadowBeg in Hl. lia.
- right. unfold kHighMemBeg in Hh. lia.
Qed.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis MCPY : aintrin_realizes rsegs B OCpy HB_MEMCPY.

(* ===================== the case ===================== *)
Theorem hw6b_c9 : hw6b_c9_stmt B MT.
Proof.
unfold hw6b_c9_stmt, hw6b_case_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp b r
  (HJ & HR32 & HRsp & HRlo & Hown & HF & Hrom) Hcase Hin HSok.
cbv beta in Hcase.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof (@asan_consts rc) as (Hceil0 & _ & HhB & HhE & HlE).
assert (Has : T_SEG_STK = 16384) by reflexivity.
assert (HE : ESTACK = 4096) by reflexivity.
assert (HPP : Layout.PP_SIZE = 19744) by reflexivity.
(* ---- what the entry state gives ---- *)
destruct Hin as (G2 & G3 & G4 & G9 & G27 & G18 & G17 & G6 & G20 & G16 & _ & V40 & Ve8 & V118 & V130 & V138 & V148 &
  Hkd & Hpp1 & Hpp2 & HF1 & HF2 & HF32 & HRceil & HFp & Ez & Hra104 & Hhull104 & Hc1 & Hinp & _ & _).
pose proof Hinp as (_ & _ & Hcur0 & Hcurn & _ & _).
(* ---- the journal's static facts ---- *)
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hs16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (HR2 : R + 0x220 <= 2 ^ 47) by lia.
assert (HR16 : R mod 16 = 0).
{ apply (proj2 (Z.mod_divide _ 16 ltac:(lia))). apply (proj1 (Z.mod_divide R 32 ltac:(lia))) in HR32.
  destruct HR32 as [q Hq]. exists (2 * q). lia. }
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (_ & HFapp & _ & _).
rewrite <- HF in HFapp. change (fs_frame_bytes 4) with 1024 in HFapp.
destruct (h9_F_band F HFapp HF2) as (HFband & HFtop).
(* the frame is writable for the journal, and no byte of it is in the image *)
assert (HWF : forall a, F <= a < F + 1024 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a).
{ intros a Ha. right. right. right. exists 4, pos. split; [exact Hown|]. left.
  unfold in_zr. cbn [fst snd]. rewrite <- HF. change (fs_frame_bytes 4) with 1024. lia. }
assert (HFimg : forall a, F <= a < F + 1024 -> ~ in_img rsegs a).
{ intros a Ha. refine (proj2 (al_client_img _ _ LAWS lyc Sc W memc mdc a HAR _)).
  right. left. exists 4, pos. split; [exact Hin4|].
  rewrite <- HF. change (fs_frame_bytes 4) with 1024. lia. }
(* ---- ent_build.s, the source of the copy ---- *)
unfold hw6b_s_ok in HSok.
destruct HSok as (HSb & HSz & _ & HS0 & HS63 & HSimg & _ & HSra & HShull & _).
unfold hd_zbytes in HSb, HSz, HS63, HSimg, HSra, HShull. rewrite length_map in HSb, HSz, HS63, HSimg, HSra, HShull.
assert (LS9 : length S9 = 13%nat) by (vm_compute; reflexivity).
rewrite LS9 in HSb, HSz, HS63, HSimg, HSra, HShull.
change (Z.of_nat 13 + 1) with 14 in HSra, HShull. change (Z.of_nat 13) with 13 in HSb, HSz, HSimg.
assert (HSout : forall x, HB_S <= x < HB_S + 14 -> ~ (F <= x < F + 1024)).
{ intros x Hx Hf. apply (HFimg x Hf). replace x with (HB_S + (x - HB_S)) by lia. apply HSimg. lia. }
assert (HSFd : HB_S + 14 <= F + 0x220 \/ F + 0x220 + 14 <= HB_S).
{ pose proof (HSout HB_S ltac:(unfold HB_S; lia)) as A0.
  pose proof (HSout (HB_S + 13) ltac:(unfold HB_S; lia)) as A1. lia. }
assert (HSrc : hm_bytes rsegs (w_H W) memc HB_S (S9 ++ [NUL])).
{ apply (proj2 (hm_bytes_aview rsegs (w_H W) memc HB_S (S9 ++ [NUL]))). intros i Hi.
  rewrite length_app, LS9 in Hi. cbn [length] in Hi.
  destruct (Nat.lt_ge_cases i 13) as [H1|H1].
  - rewrite app_nth1 by lia. specialize (HSb (Z.of_nat i) ltac:(lia)).
    rewrite Nat2Z.id, hm_nth_map in HSb. exact HSb.
  - assert (Ei : i = 13%nat) by lia. subst i.
    rewrite app_nth2 by lia. rewrite LS9. cbn [Nat.sub nth].
    change (Z.of_nat 13) with 13. rewrite HSz. reflexivity. }
(* ---- block A ---- *)
eapply SRr_bind.
{ apply (h9_A B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pp HJ G9); try lia.
  - exact V40.
  - exact V118.
  - exact V130.
  - exact V148.
  - intros a Ha. replace a with (F + (a - F)) by lia. apply HFp. lia.
  - intros a Ha. apply HWF. lia. }
cbv beta. intros W1 c1 _ (-> & regsA & memA & mdA & -> & HJA & HioA & HrA & HKA & HprA &
  (A1 & A10 & A11 & A12 & A23 & VA0 & VA8 & VAc)).
(* the registers block A kept *)
assert (A2 : getr regsA 2 = w64 R)
  by (rewrite (HrA 2%bv ltac:(apply cb_nz; vm_compute; reflexivity)
        ltac:(apply cb_notin; vm_compute; reflexivity)); exact G2).
assert (A3 : getr regsA 3 = w64 (as_gp B))
  by (rewrite (HrA 3%bv ltac:(apply cb_nz; vm_compute; reflexivity)
        ltac:(apply cb_notin; vm_compute; reflexivity)); exact G3).
assert (A4 : getr regsA 4 = w64 (as_tp B))
  by (rewrite (HrA 4%bv ltac:(apply cb_nz; vm_compute; reflexivity)
        ltac:(apply cb_notin; vm_compute; reflexivity)); exact G4).
assert (A9 : getr regsA 9 = w64 R)
  by (rewrite (HrA 9%bv ltac:(apply cb_nz; vm_compute; reflexivity)
        ltac:(apply cb_notin; vm_compute; reflexivity)); exact G9).
assert (A18 : getr regsA 18 = w64 c)
  by (rewrite (HrA 18%bv ltac:(apply cb_nz; vm_compute; reflexivity)
        ltac:(apply cb_notin; vm_compute; reflexivity)); exact G18).
assert (A20 : getr regsA 20 = w64 (Z.of_nat (length r)))
  by (rewrite (HrA 20%bv ltac:(apply cb_nz; vm_compute; reflexivity)
        ltac:(apply cb_notin; vm_compute; reflexivity)); exact G20).
assert (Asp : spZ regsA = sp0 + (R - sp0))
  by (unfold spZ; rewrite A2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (KcA : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x210 <= a < F + 0x220) ->
  aview rsegs (w_H W) memA a = aview rsegs (w_H W) memc a) by exact HKA.
(* ---- the memcpy's premises at memA: A's stores lie below the shadow band ---- *)
assert (KSH : forall x, 0 <= x < kHighMemEnd ->
  aview rsegs (w_H W) memA (shadow_of_addr SHADOW_OFF x) = aview rsegs (w_H W) memc (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. pose proof (hm_shadow_band x Hx) as Hb. rewrite HlE, HhB in Hb. apply KcA; lia. }
assert (KHU : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 - 1 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 ->
  aview rsegs (w_H W) memc s <> None -> aview rsegs (w_H W) memA s <> None).
{ intros x n s H0 Hn Hxn Hs Hne. pose proof (cj_hull_band x n s H0 Hn Hxn Hs) as Hb.
  rewrite HlE, HhB in Hb. rewrite KcA by lia. exact Hne. }
assert (RAD : range_addressable (aview rsegs (w_H W) memA) SHADOW_OFF (F + 0x220) 14).
{ apply (hm_ra_kept rsegs (w_H W) memc (w_H W) memA).
  - apply (ra_sub _ _ (F + 0x210) 104); [exact Hra104 | lia | lia].
  - intros x Hx. apply KSH. rewrite HhE. lia. }
assert (RAS : range_addressable (aview rsegs (w_H W) memA) SHADOW_OFF HB_S 14).
{ apply (hm_ra_kept rsegs (w_H W) memc (w_H W) memA); [exact HSra|].
  intros x Hx. apply KSH. rewrite HhE. unfold HB_S in *. lia. }
assert (HUD : shadow_hull_vis (aview rsegs (w_H W) memA) (F + 0x220) 14).
{ apply (hm_hull_kept rsegs (w_H W) memc (w_H W) memA).
  - apply (hm_hull_sub _ (F + 0x210) 104); [exact Hhull104 | lia | lia | lia].
  - intros s Hs Hne. exact (KHU (F + 0x220) 14 s ltac:(lia) ltac:(lia) ltac:(lia) Hs Hne). }
assert (HUS : shadow_hull_vis (aview rsegs (w_H W) memA) HB_S 14).
{ apply (hm_hull_kept rsegs (w_H W) memc (w_H W) memA); [exact HShull|].
  intros s Hs Hne. exact (KHU HB_S 14 s ltac:(unfold HB_S; lia) ltac:(lia) ltac:(unfold HB_S; lia) Hs Hne). }
assert (HSrcA : hm_bytes rsegs (w_H W) memA HB_S (S9 ++ [NUL])).
{ apply (hm_bytes_kept rsegs (w_H W) memc); [exact HSrc|].
  intros x Hx. rewrite length_app, LS9 in Hx. cbn [length] in Hx.
  pose proof (HSout x ltac:(lia)) as Hx'. apply KcA; unfold HB_S in *; lia. }
assert (HSnn : forall x, HB_S <= x < HB_S + 14 -> aview rsegs (w_H W) memA x <> None).
{ intros x Hx. replace x with (HB_S + Z.of_nat (Z.to_nat (x - HB_S))) by lia.
  rewrite (proj1 (hm_bytes_aview rsegs (w_H W) memA HB_S (S9 ++ [NUL])) HSrcA (Z.to_nat (x - HB_S))
    ltac:(rewrite length_app, LS9; cbn [length]; lia)).
  discriminate. }
(* ---- block B: the call ---- *)
eapply SRr_bind.
{ apply (cb_memcpy_at B HB_MEMCPY MCPY W regsA memA STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdA k
    (F + 0x220) HB_S 14 (R - sp0) (w64 H9_RET) HJA A10 A11 A12).
  - lia.
  - lia.
  - lia.
  - exact Asp.
  - rewrite Zminus_mod, HR16, Hs16. reflexivity.
  - lia.
  - lia.
  - exact A3.
  - exact A4.
  - exact A1.
  - apply ret_ok_even; vm_compute; reflexivity.
  - intros a Ha. split; [apply HWF; lia|]. rewrite HE. lia.
  - unfold amem_range. rewrite HlE, HhB, HhE. destruct HFband as [Hl|Hh]; [left; lia | right; lia].
  - exact RAD.
  - intros _. exact HUD.
  - unfold HB_S. lia.
  - unfold HB_S. lia.
  - intros a Ha. split; [apply HSnn; lia|].
    rewrite Asp. replace (sp0 + (R - sp0)) with R by lia. rewrite HE. unfold HB_S in *. lia.
  - lia.
  - unfold amem_range. left. rewrite HlE. unfold HB_S. lia.
  - exact RAS.
  - intros _. exact HUS. }
cbv beta. intros W2 c2 _ (-> & regsB & memB & mdB & -> & HJB & HioB & HPB & B10 & HD & HKB & HprB).
(* the registers the call kept *)
assert (B9 : getr regsB 9 = w64 R)
  by (rewrite (cb_reg_eq regsA regsB 9%bv (HPB 9 ltac:(unfold acallee_saved; lia))); exact A9).
assert (B18 : getr regsB 18 = w64 c)
  by (rewrite (cb_reg_eq regsA regsB 18%bv (HPB 18 ltac:(unfold acallee_saved; lia))); exact A18).
assert (B20 : getr regsB 20 = w64 (Z.of_nat (length r)))
  by (rewrite (cb_reg_eq regsA regsB 20%bv (HPB 20 ltac:(unfold acallee_saved; lia))); exact A20).
assert (B23 : getr regsB 23 = w64 pp)
  by (rewrite (cb_reg_eq regsA regsB 23%bv (HPB 23 ltac:(unfold acallee_saved; lia))); exact A23).
assert (KAB : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x220 <= a < F + 0x22e) -> ~ (R - 4096 <= a < R) ->
  aview rsegs (w_H W) memB a = aview rsegs (w_H W) memA a).
{ intros a Ha H1 H2. apply HKB; [exact Ha | lia | rewrite HE; lia]. }
(* ---- block C ---- *)
eapply SRr_bind.
{ apply (h9_C B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memB mdB k regsB R F pp c (Z.of_nat (length r)) HJB B9);
    try lia.
  - exact B18.
  - exact B20.
  - apply (val_mem_kept rsegs (w_H W) (w_H W) memc memB (R + 0x130) 8 (F + 0x210)); [|exact V130].
    intros i Hi. rewrite KAB by lia. apply KcA; lia.
  - apply (val_mem_kept rsegs (w_H W) (w_H W) memc memB (R + 0x138) 8 (pp + 0x4000)); [|exact V138].
    intros i Hi. rewrite KAB by lia. apply KcA; lia.
  - intros a Ha. apply HprB. apply HprA. replace a with (F + (a - F)) by lia. apply HFp. lia.
  - intros a Ha. apply HWF. lia. }
cbv beta. intros W3 c3 _ (-> & regsC & memC & mdC & -> & HJC & HioC & HrC & HKC & HprC &
  (C6 & C13 & C18 & C20 & VC214)).
(* ---- the post at J ---- *)
apply SRr_ret. unfold hdu_blk_postE.
exists lyc, Sc, regsC, memC, mdC.
split; [reflexivity|].
split; [exact HJC|].
(* every register the three pieces keep *)
assert (Hkeep3 : forall rg : bv 5, bv_unsigned rg <> 0 -> acallee_saved (bv_unsigned rg) ->
  ~ In rg [1; 10; 11; 12; 23]%bv -> ~ In rg [6; 10; 11; 13; 18; 20]%bv -> getr regsC rg = getr regs rg).
{ intros rg Hr0 Hcs Hn1 Hn2.
  rewrite (HrC rg Hr0 Hn2), (cb_reg_eq regsA regsB rg (HPB (bv_unsigned rg) Hcs)).
  exact (HrA rg Hr0 Hn1). }
assert (Hsub1 : forall rg : bv 5, ~ In rg hw6b_clob -> ~ In rg [1; 10; 11; 12; 23]%bv).
{ intros rg Hn X. apply Hn. unfold hw6b_clob. cbv [In] in X |- *.
  repeat (destruct X as [X|X]; [rewrite <- X; repeat (first [left; reflexivity | right])|]). destruct X. }
assert (Hsub2 : forall rg : bv 5, ~ In rg hw6b_clob -> ~ In rg [6; 10; 11; 13; 18; 20]%bv).
{ intros rg Hn X. apply Hn. unfold hw6b_clob. cbv [In] in X |- *.
  repeat (destruct X as [X|X]; [rewrite <- X; repeat (first [left; reflexivity | right])|]). destruct X. }
split.
{ intros rg H1 H2. exact (Hkeep3 rg H1 (h9_clob_cs rg H1 H2) (Hsub1 rg H2) (Hsub2 rg H2)). }
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [eapply same_io_trans; [eapply same_io_trans; [exact HioA | exact HioB] | exact HioC]|].
split; [apply mo_le_refl; exact MTL|].
(* every byte outside cj_wr kept *)
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x210 <= a < F + 0x278) -> ~ (R - T_SEG_STK <= a < R) ->
  aview rsegs (w_H W) memC a = aview rsegs (w_H W) memc a).
{ intros a Ha H1 H2. rewrite Has in H2.
  rewrite (HKC a Ha ltac:(unfold h9_wrC; lia)). rewrite KAB by lia. apply KcA; lia. }
split.
{ intros a Ha Hnw. unfold cj_wr in Hnw.
  apply KALL; [exact Ha | intros X; apply Hnw; right; right; unfold HSU_E62; lia | intros X; apply Hnw; left; exact X]. }
(* ---- the state at J ---- *)
unfold cj_J_R. rewrite (h9_model b r Hcase). cbn [fst snd].
split; [rewrite C13; unfold w64; f_equal; lia|].
split; [exact C6|].
split; [rewrite C18; reflexivity|].
split; [rewrite C20; reflexivity|].
split.
{ rewrite (HrC 23%bv ltac:(apply cb_nz; vm_compute; reflexivity) ltac:(apply cb_notin; vm_compute; reflexivity)).
  exact B23. }
(* e62 holds Layout.ent_mem of the default pod *)
assert (EM : ent_mem (Ent POD_STRUCT 24 (le32 14 ++ le32 POD_STRING ++ S9 ++ [NUL] ++ zeros 2)) =
  Z_to_le_bytes 4 14 ++ Z_to_le_bytes 4 24 ++ Z_to_le_bytes 4 14 ++ Z_to_le_bytes 4 8 ++
  (S9 ++ [NUL]) ++ zeros 74) by (vm_compute; reflexivity).
apply (proj1 (hm_bytes_zbytes rsegs _ _ _ _)).
rewrite EM. unfold HSU_E62.
(* e62.type = POD_STRUCT *)
apply (h9_app _ _ _ _ _ 4 (F + 0x214)); [reflexivity | lia | | ].
{ apply hm_bytes_of_val.
  apply (val_mem_kept rsegs (w_H W) (w_H W) memA memC (F + 0x210) 4 14); [|exact VA0].
  intros i Hi. rewrite (HKC (F + 0x210 + i) ltac:(lia) ltac:(unfold h9_wrC; lia)). apply KAB; lia. }
(* e62.size = 24 *)
apply (h9_app _ _ _ _ _ 4 (F + 0x218)); [reflexivity | lia | | ].
{ apply hm_bytes_of_val. exact VC214. }
(* e62.body[0..4) = 14 *)
apply (h9_app _ _ _ _ _ 4 (F + 0x21c)); [reflexivity | lia | | ].
{ apply hm_bytes_of_val.
  apply (val_mem_kept rsegs (w_H W) (w_H W) memA memC (F + 0x218) 4 14); [|exact VA8].
  intros i Hi. rewrite (HKC (F + 0x218 + i) ltac:(lia) ltac:(unfold h9_wrC; lia)). apply KAB; lia. }
(* e62.body[4..8) = POD_STRING *)
apply (h9_app _ _ _ _ _ 4 (F + 0x220)); [reflexivity | lia | | ].
{ apply hm_bytes_of_val.
  apply (val_mem_kept rsegs (w_H W) (w_H W) memA memC (F + 0x21c) 4 8); [|exact VAc].
  intros i Hi. rewrite (HKC (F + 0x21c + i) ltac:(lia) ltac:(unfold h9_wrC; lia)). apply KAB; lia. }
(* e62.body[8..22) = the 14 bytes of ent_build.s *)
apply (h9_app _ _ _ _ _ 14 (F + 0x22e)); [rewrite length_app, LS9; reflexivity | lia | | ].
{ apply (hm_bytes_kept rsegs (w_H W) memB).
  - apply (hm_memcpy_bytes rsegs (w_H W) memA (w_H W) memB HB_S (F + 0x220) (S9 ++ [NUL])).
    + exact HSrcA.
    + intros i Hi. apply HD. rewrite length_app, LS9 in Hi. cbn [length] in Hi. lia.
  - intros x Hx. rewrite length_app, LS9 in Hx. cbn [length] in Hx.
    apply HKC; [lia | unfold h9_wrC; lia]. }
(* the tail of the 104 zero bytes *)
apply h9_zeros. intros i Hi. change (Z.of_nat 74) with 74 in Hi.
rewrite (HKC (F + 0x22e + i) ltac:(lia) ltac:(unfold h9_wrC; lia)), KAB by lia. rewrite KcA by lia.
unfold aview. replace (F + 0x22e + i) with (F + 0x210 + (30 + i)) by lia. rewrite (Ez (30 + i) ltac:(lia)).
reflexivity.
Qed.

End d.
End b.

Print Assumptions hw6b_c9.
