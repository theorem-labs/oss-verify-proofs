(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v, with its module paths changed; 248 of its 275 lines of code are new or changed and 263 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW3bPre.v at c7151e1be45; ported to reac-pw/fuzz_headamp image A: module paths, the rs_ / rm_ / rl_ prefixes renamed hs_ / hm_ / hd_, every pc moved to headamp's code, the real-frame cells moved by the slot map, the region widened to headamp's preheader window [R, R + 0x120), role's flags cell and cursor cells replaced by headamp's null-flag cell R+0x40, the block's cell R+0xf0 (a chunk over a5's atom: headamp reloads pp from it where role reads s11) and the length cell R+0x118 (the cursor stays in s11, its own atom), and role's s9 / R+0x28 frame copies replaced by headamp's s8 = cap and s10 = F; the run-keeps-bytes lemma is stated here (role took it from its RPgCfgChanges.v). *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the property loop's
   preheader of the build (M01) of LLVMFuzzerTestOneInput 0x80bc0, PH 0x81224 -> N 0x812f4 (nprops <> 0) / P
   0x82c68 (nprops = 0), pod.h:397-398. Proves no function (kind: segment lemma).

   THE CODE. 0x81224 .. 0x8124c spill a6 (the top word's offset 0), a5 (its address pp), s8 (the cap), s6 (F),
   &pp->n_ent (R+0xf0's pp + 0x4d14, from s4 = 0x5000) and its shadow index, and s10 (F) into R-relative cells;
   0x81250 loads nprops (R+0xb0) and `bnez` 0x81254 leaves to 0x8125c or, through `j` 0x81258, to P. 0x8125c ..
   0x812f0 set the loop's registers (seen = 0, i = 0, &t, &r, the `/ 10` multiplier, the shadow address of
   &pp->len) and the cells the property loop reloads (hs_Kc of HPgSeg.v).

   HOW. As HPgW3b.v: the symbolic state is rebuilt from PH's cut over the token engine (no instrumented check runs
   here, so no shadow entry is needed); the R-relative cells are one region with the write window [R, R + 0x120),
   inside the segment's journal's stack window, whose seven kept cells are chunks: the null flag, nprops, the
   shape and the bytes left over the extra atoms 32 .. 35, the shadow address of &pp->len over s5's and s7's atoms,
   pp over a5's atom and -0x3ffd as a literal. Every fact of the end cut is read from the final symbolic state: a
   register from its symbolic value, a cell from its chunk. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YI00 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgSeg HPgW3b.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* a run keeps every byte outside the zone its write windows lie in *)
Lemma w3b_kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m1 a = aview rsegs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* ===================================== PH -> N | P: the preheader =====================================
   0x81224 .. 0x812f0. The R-relative cells are one region with the preheader's write window [R, R + 0x120); the
   seven cells it keeps (the null flag, nprops, the shape, the shadow address of &pp->len, pp, -0x3ffd, the bytes
   left) are its chunks, the four input-dependent ones over the extra atoms 32 .. 35 and pp over a5's atom 15.
   a6 = 0 and s4 = 0x5000 are pinned. The engine stops at `bnez a0` 0x81254 (a0 = nprops); the taken arm runs to
   N, the other to P. *)
Definition w3b_regs_ph : list sv := sr_set (sr_set sr_atoms (Z_to_bv 5 16) (SLit 0)) (Z_to_bv 5 20) (SLit 0x5000).
Definition w3b_slot_ph : YP09.region :=
YP09.mkRegion (Some 9%nat) 0 0x120 0 0x120
[YP09.mkChunk 0x40 (CVal 8 (SOff 32 0)); YP09.mkChunk 0xb0 (CVal 8 (SOff 33 0)); YP09.mkChunk 0xb8 (CVal 8 (SOff 34 0));
 YP09.mkChunk 0xd0 (CVal 8 w3b_shx); YP09.mkChunk 0xf0 (CVal 8 (SOff 15 0)); YP09.mkChunk 0x108 (CVal 8 (SLit W3B_M3FFD));
 YP09.mkChunk 0x118 (CVal 8 (SOff 35 0))].
Definition w3b_atoms_ph : list (nat * afact) := [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 0)].
Definition w3b_ss_ph : sstate := mkSS W3B_PH w3b_regs_ph [w3b_slot_ph] None (mkFacts w3b_atoms_ph [] []).

(* the value of a symbolic expression of a final state, from the exact values of its atoms (U facts in context) *)
Ltac w3b_den :=
  unfold w3b_shx; rewrite denot_lit_U; apply Z_to_bv64_eq_mod;
  repeat match goal with H : U ?E ?x = _ |- context [U ?E ?x] => rewrite H end;
  rewrite ?U_SAlu, ?U_SOff, ?U_SLit; cbn [zalu_raw];
  repeat match goal with H : bv_unsigned (ew ?E ?n) = _ |- context [bv_unsigned (ew ?E ?n)] => rewrite H end;
  rewrite ?Z.add_0_r; unfold zcanon, M64; rewrite ?Zmod_mod;
  first [reflexivity | f_equal; lia | lia].
(* the machine state a final symbolic state describes *)
Ltac w3b_ms HS := lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => m end.
(* one (location, value) fact of a cut, read from the final symbolic state HS: a register from its symbolic value,
   a cell from the region's chunk at that offset *)
Ltac w3b_fact HS E :=
  let ms := w3b_ms HS in
  cbn [fst snd hd_at hd_xv];
  lazymatch goal with
  | |- getr _ ?r = _ =>
      rewrite (st_ok_restrict_reg rsegs _ E _ ms r HS);
      lazymatch goal with |- sv_denot _ (sr_get ?l ?r') = _ =>
        let x := eval vm_compute in (sr_get l r') in change (sr_get l r') with x end;
      unfold w64; w3b_den
  | |- val_mem _ _ (?R + ?o) 8 _ =>
      match goal with C : YP09.chunk_ok _ _ _ R (YP09.mkChunk o (CVal 8 ?ex)) |- _ =>
        apply (val_of_chunk_ok rsegs E _ R o 8 ex _ C);
        [ w3b_den
        | split; [apply Z.mod_pos_bound; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia]
        | cbn; lia ]
      end
  end.
Ltac w3b_split_chunks Cs :=
  repeat lazymatch type of Cs with _ /\ _ => let c := fresh "Cn" in destruct Cs as [c Cs] end.
Ltac w3b_kio := first [apply same_io_refl | eapply same_io_trans; [| apply HPgSteps.same_io_wvb]; w3b_kio].
(* the run's writes are the segment's stack window: the R-relative region on atom 9, R = sp0 + (R - sp0) *)
Ltac w3b_awr_slot U9 R sp :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp' ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp' fp b0 bc ly0 own0) end;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp));
    [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia | apply awr_ok_nil].
(* ... and those bytes are R-relative *)
Ltac w3b_kw U9 :=
  let a := fresh "a" in let rg := fresh "rg" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (rg & Hr & Hb);
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hr end;
  destruct Hr as [<-|[]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite U9 in Hb; lia.
(* fold a run's frame into the kept-bytes fact KE (every byte outside [R, R + 0x120) as at PH) *)
Ltac w3b_keep KE U9 R :=
  lazymatch goal with HFr : frame_of ?E0 ?rs (mrestrict _ _) (mrestrict _ _) |- _ =>
    let KW := fresh "KW" in let KE' := fresh "KE" in
    assert (KW : forall a, in_wrange E0 rs a -> R <= a < R + 0x120) by w3b_kw U9;
    pose proof (w3b_kept_run (fun a => R <= a < R + 0x120) _ _ _ _ _ _ KE HFr KW) as KE';
    clear KE KW HFr; rename KE' into KE end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the final region's chunks, one hypothesis each *)
Ltac w3b_chunks HS U9 :=
  let HOK := fresh "HOK" in let Cs := fresh "Cs" in
  pose proof (st_ok_mem_ok rsegs _ _ _ HS) as (_ & HOK & _); cbn [ss_mem] in HOK;
  pose proof (Forall_inv HOK) as (_ & _ & _ & Cs); cbn [YP09.r_base YP09.r_chunks base_val] in Cs;
  rewrite U9 in Cs; clear HOK; repeat rewrite Forall_cons_iff in Cs; w3b_split_chunks Cs.
(* hs_core at the end: the journal, s1 .. s3 as at the start (their own atoms), the frames, blocks, I/O and meter,
   and every byte outside the segment's write set as at the start (the run wrote only [R, R + 0x120), which is in
   hi_w1's real-frame range [R, R + 0x160)) *)
Ltac w3b_core HS E HAE regs2 W2 HJ H234 Hfr Hperm Hio Hmo Hkeep KE :=
  let ms := w3b_ms HS in
  unfold hs_core, hs_mid; split; [exact HJ|];
  split; [let rr := fresh "rr" in let Hrr := fresh "Hrr" in
          intros rr Hrr; rewrite <- (H234 rr Hrr); destruct Hrr as [->|[->| ->]];
          (eapply (w3b_reg_kept E _ ms regs2 _ (w_H W2)); [exact HS | exact HAE | vm_compute; reflexivity]) |];
  split; [exact Hfr|]; split; [exact Hperm|];
  split; [eapply same_io_trans; [exact Hio | w3b_kio] |];
  split; [exact Hmo|];
  let a := fresh "a" in let Ha := fresh "Ha" in let HnS := fresh "HnS" in let HnE := fresh "HnE" in
  let X := fresh "X" in
  intros a Ha HnS HnE; rewrite <- (Hkeep a Ha HnS HnE); apply KE; [exact Ha|];
  intros X; cbv beta in X; apply HnE; unfold hs_E1; left; unfold hd_inw; cbn [hi_w1 headamp_himg_A];
  apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; cbn [fst snd hd_xv]; lia.
(* the frame's shadow bytes: below the stack, so outside [R, R + 0x120) *)
Ltac w3b_fsh HS HFSH KE W2 mem2 :=
  let ms := w3b_ms HS in
  let i := fresh "i" in let Hi := fresh "Hi" in let X := fresh "X" in
  apply (hm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) _ hs_P0 HFSH);
  intros i Hi; change (length hs_P0) with 80%nat in Hi;
  apply KE; [unfold shadow_addr, SHADOW_OFF; lia | intros X; cbv beta in X; unfold shadow_addr, SHADOW_OFF in X; lia].
(* the block's bytes: below the stack too *)
Ltac w3b_pp HS HPP KE W2 mem2 Lpc :=
  let ms := w3b_ms HS in
  let y := fresh "y" in let Hy := fresh "Hy" in let X := fresh "X" in
  apply (hm_bytes_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) _ _ HPP);
  rewrite Lpc; change (Z.of_nat 19744) with 19744;
  intros y Hy; apply KE; [lia | intros X; cbv beta in X; lia].

(* the block's image has its full size at every shape *)
Lemma w3b_len_pc0 : forall sh, 0 <= sh < 8 -> length (pc_image (PbCut sh [] None)) = 19744%nat.
Proof.
intros sh Hsh. assert (H8 : sh = 0 \/ sh = 1 \/ sh = 2 \/ sh = 3 \/ sh = 4 \/ sh = 5 \/ sh = 6 \/ sh = 7) by lia.
destruct H8 as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

(* PH -> N | P *)
Lemma hs_piece_W3b_pre : hs_piece_W3b_pre_stmt rsegs B MT.
Proof.
intros cx POST rest HST HN HP ly2 S2 W2 regs2 mem2 md2 r sh np HC.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
destruct HST as (HPRE & _ & Hlen & _).
pose proof HPRE as (HJc & _ & _ & _ & _ & HSe & _ & HRsz & HRstk & Hown & HFe & _ & Hcap & Hnull & _ & _ & _ & _ & _
  & _ & _ & (_ & Hppc & Hfresh)).
cbn [hi_rsz hi_cid headamp_himg_A] in HRsz, Hown, HFe.
destruct HC as (HCORE & HAT & HFSH & HPP & HIN & HSUF & Esh & Enp & Er).
pose proof HCORE as (HJ & H234 & Hfr & Hperm & Hio & Hmo & Hkeep).
pose proof HJc as (HARc & _ & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (HT : T_SEG_STK = 16384) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hppc) as (_ & Hpp0 & Hppcl & Happ & _ & _).
change (req_size PP_SIZE) with 19744 in Hppcl, Happ.
assert (HFin : In (4, x_pos rsegs cx) (frames (x_Sc rsegs cx))) by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HARc HFin) as (HF0 & HFc & _).
rewrite <- HFe in HF0, HFc. change (fs_frame_bytes 4) with 1024 in HFc.
assert (Hnp : 0 <= np <= 3) by (assert (0 <= np < 4) by (rewrite Enp; unfold hs_np; apply Z.mod_pos_bound; lia); lia).
assert (Hsh8 : 0 <= sh < 8) by (rewrite Esh; unfold hs_sh; apply Z.mod_pos_bound; lia).
assert (HFd : 0 <= e_F (x_e rsegs cx) / 8 <= 17592184995840)
  by (split; [apply Z.div_pos; lia | apply (Z.div_le_mono _ 0x7fffff800000 8); lia]).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
pose proof (w3b_len_pc0 sh Hsh8) as Lpc.
(* the cursor is a pointer into the input: 0 < src <= cursor <= src + |rest| <= 2 ^ 63 *)
assert (Hcur : 0 <= hs_cur rsegs cx rest r < 2 ^ 64).
{ pose proof HIN as (Hleft & _ & _ & _ & _ & Hsrc0 & Hsrc1 & _).
  pose proof HSUF as (j & Hj & Hr).
  assert (Hrl : (length r <= length rest)%nat) by (rewrite Hr, length_skipn; lia).
  unfold hs_cur. lia. }
(* PH's facts *)
unfold hs_at_cx, hs_at, hs_L_PH, hs_cur2 in HAT. cbn [app] in HAT.
repeat rewrite Forall_cons_iff in HAT.
destruct HAT as (A15 & A16 & A20 & A8 & A9 & A19 & A23 & A21 & A22 & A26 & A24 & C40 & Cf0 & Cb0 & Cb8 & Cd0 & C108
  & A27 & C118 & _).
cbn [fst snd hd_at hd_xv] in A15, A16, A20, A8, A9, A19, A23, A21, A22, A26, A24, C40, Cf0, Cb0, Cb8, Cd0, C108, A27,
  C118.
remember (Ereg regs2 [Z_to_bv 64 (e_null (x_e rsegs cx)); Z_to_bv 64 np; Z_to_bv 64 sh;
  Z_to_bv 64 (Z.of_nat (length r))]) as E eqn:HE.
assert (HAE : forall n, (n < 32)%nat -> ew E n = ew (Ereg regs2 [Z_to_bv 64 (e_null (x_e rsegs cx)); Z_to_bv 64 np;
  Z_to_bv 64 sh; Z_to_bv 64 (Z.of_nat (length r))]) n) by (intros; subst E; reflexivity).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr)
  by (intros n rr Hn; subst E; exact (ew_Ereg_nat regs2 _ n rr Hn)).
assert (Ux : forall n v, (n < 32)%nat -> getr regs2 (Z_to_bv 5 (Z.of_nat n)) = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew E n) = v).
{ intros n v Hn Hg Hv. rewrite (EE n (Z_to_bv 5 (Z.of_nat n))), Hg by (rewrite Z_to_bv_unsigned; unfold bv_wrap;
    change (bv_modulus 5) with 32; rewrite Z.mod_small; lia). apply unsigned_lit_small. exact Hv. }
assert (U8 : bv_unsigned (ew E 8) = e_S (x_e rsegs cx)) by (apply (Ux 8%nat); [lia | exact A8 | lia]).
assert (U9 : bv_unsigned (ew E 9) = e_R (x_e rsegs cx)) by (apply (Ux 9%nat); [lia | exact A9 | lia]).
assert (U15 : bv_unsigned (ew E 15) = e_pp (x_e rsegs cx)) by (apply (Ux 15%nat); [lia | exact A15 | lia]).
assert (U16 : bv_unsigned (ew E 16) = 0) by (apply (Ux 16%nat); [lia | exact A16 | lia]).
assert (U19 : bv_unsigned (ew E 19) = shadow_addr (e_F (x_e rsegs cx)))
  by (apply (Ux 19%nat); [lia | exact A19 | unfold shadow_addr, SHADOW_OFF; lia]).
assert (U20 : bv_unsigned (ew E 20) = 0x5000) by (apply (Ux 20%nat); [lia | exact A20 | lia]).
assert (U21 : bv_unsigned (ew E 21) = e_pp (x_e rsegs cx) + 0x4000) by (apply (Ux 21%nat); [lia | exact A21 | lia]).
assert (U22 : bv_unsigned (ew E 22) = e_F (x_e rsegs cx)) by (apply (Ux 22%nat); [lia | exact A22 | lia]).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF) by (apply (Ux 23%nat); [lia | exact A23 | unfold SHADOW_OFF; lia]).
assert (U24 : bv_unsigned (ew E 24) = e_cap (x_e rsegs cx)) by (apply (Ux 24%nat); [lia | exact A24 | lia]).
assert (U26 : bv_unsigned (ew E 26) = e_F (x_e rsegs cx)) by (apply (Ux 26%nat); [lia | exact A26 | lia]).
assert (U27 : bv_unsigned (ew E 27) = hs_cur rsegs cx rest r) by (apply (Ux 27%nat); [lia | exact A27 | exact Hcur]).
assert (U32 : bv_unsigned (ew E 32) = e_null (x_e rsegs cx) mod 2 ^ 64)
  by (subst E; rewrite (ew_Ereg_extra regs2 _ 0); apply Z_to_bv_unsigned).
assert (U33 : bv_unsigned (ew E 33) = np mod 2 ^ 64) by (subst E; rewrite (ew_Ereg_extra regs2 _ 1); apply Z_to_bv_unsigned).
assert (U34 : bv_unsigned (ew E 34) = sh mod 2 ^ 64) by (subst E; rewrite (ew_Ereg_extra regs2 _ 2); apply Z_to_bv_unsigned).
assert (U35 : bv_unsigned (ew E 35) = Z.of_nat (length r) mod 2 ^ 64)
  by (subst E; rewrite (ew_Ereg_extra regs2 _ 3); apply Z_to_bv_unsigned).
assert (HUshx : U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 21 0) (SLit 3)) (SOff 23 0)) = shadow_addr (e_pp (x_e rsegs cx) + 0x4000)).
{ rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, U21, U23, !Z.add_0_r.
  change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  unfold shadow_addr, zcanon, M64, SHADOW_OFF.
  assert (0 <= (e_pp (x_e rsegs cx) + 0x4000) / 8 < 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (Z.mod_small (e_pp (x_e rsegs cx) + 0x4000)) by lia. rewrite (Z.mod_small 2147450880) by lia.
  rewrite (Z.mod_small ((e_pp (x_e rsegs cx) + 0x4000) / 8)) by lia. rewrite Z.mod_small by lia. lia. }
assert (HU68 : U E (SAlu ALU_SRL (SOff 15 19732) (SLit 3)) = Z.shiftr (e_pp (x_e rsegs cx) + 0x4d14) 3).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit, U15.
  change (Z.land (zcanon 3) 63) with 3. unfold zcanon, M64.
  rewrite (Z.mod_small (e_pp (x_e rsegs cx) + 19732)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  apply Z.mod_small. split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
(* the symbolic state at PH *)
assert (HS : st_ok rsegs E w3b_ss_ph (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 W3B_PH) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. rewrite HE. unfold w3b_ss_ph. apply (entry_st_ok_full rsegs).
  - unfold w3b_regs_ph. apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Ereg | reflexivity |] | reflexivity |].
    + rewrite A16. reflexivity.
    + rewrite A20. reflexivity.
  - vm_compute. reflexivity.
  - rewrite <- HE. constructor; [|constructor].
    unfold region_ok, w3b_slot_ph. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable rsegs); apply Hstkp; lia|].
    repeat apply Forall_cons; try apply Forall_nil;
    match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 ?ex)) =>
      lazymatch goal with C : val_mem _ _ (_ + o) 8 ?v |- _ =>
        apply (chunk_ok_val rsegs E _ _ o 8 ex v);
        [ w3b_den
        | split; [apply Z.mod_pos_bound; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia]
        | cbn; lia | exact C ] end end.
  - rewrite <- HE. apply pairwise_disjoint_of_extents. cbn. tauto.
  - rewrite <- HE. split; [|split; exact I]. cbn [f_atoms w3b_atoms_ph atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
assert (SHOK : sh_ok rsegs w3b_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) <= a < e_R (x_e rsegs cx) + 0x120) ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a) by (intros; reflexivity).
clear HE.
unfold cfg_at. change (w64 HS_PH) with (Z_to_bv 64 W3B_PH).
(* 0x81224 .. 0x81250: the spills of the top word's offset and address, the cap, F, &pp->n_ent; stop at `bnez a0` *)
aj_run_to_tok w3b_tbl_ok HS HJ SHOK w3b_Bspan W3B_N.
{ w3b_awr_slot U9 (e_R (x_e rsegs cx)) (x_sp0 rsegs cx). }
(* the run wrote only the R-relative window *)
w3b_keep KE U9 (e_R (x_e rsegs cx)).
(* 0x81254 bnez a0, a0 = nprops *)
srr_branch_tok w3b_tbl_ok HS SHOK w3b_Bspan.
- (* nprops <> 0: 0x8125c .. 0x812f0, the loop's registers and cells, to N *)
  rewrite branch_ne_U, U_SOff, U_SLit, U33, Z.add_0_r in Hc. unfold zcanon, M64 in Hc.
  rewrite Zmod_mod, (Z.mod_small np), Z.mod_0_l in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
  aj_run_to_tok w3b_tbl_ok HS HJ SHOK w3b_Bspan W3B_N.
  { w3b_awr_slot U9 (e_R (x_e rsegs cx)) (x_sp0 rsegs cx). }
  w3b_keep KE U9 (e_R (x_e rsegs cx)).
  w3b_chunks HS U9.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) =>
    rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ m HS eq_refl) at 1;
    apply (HN ly2 S2 W2 (ms_regs m) (ms_mem m) _ sh np [] r eq_refl) end.
  unfold hs_cut_N. split; [w3b_core HS E HAE regs2 W2 HJ H234 Hfr Hperm Hio Hmo Hkeep KE|].
  split.
  { unfold hs_at_cx, hs_at, hs_L_N, hs_Rc0, hs_Kc, hs_cur2. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; w3b_fact HS E. }
  split; [w3b_fsh HS HFSH KE W2 mem2|].
  split; [w3b_pp HS HPP KE W2 mem2 Lpc|].
  split; [exact HIN|]. split; [exact HSUF|].
  split; [split; [exact Hsh8|]; split; [constructor|]; split; [cbn; constructor | cbn; lia]|].
  split; [exact Esh|]. split; [exact Enp|]. split; [cbn; lia|]. split; [lia|].
  rewrite Er. reflexivity.
- (* nprops = 0: `j` 0x81258 to P *)
  rewrite branch_ne_U, U_SOff, U_SLit, U33, Z.add_0_r in Hc. unfold zcanon, M64 in Hc.
  rewrite Zmod_mod, (Z.mod_small np), Z.mod_0_l in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
  aj_run_to_tok w3b_tbl_ok HS HJ SHOK w3b_Bspan W3B_P.
  { w3b_awr_slot U9 (e_R (x_e rsegs cx)) (x_sp0 rsegs cx). }
  w3b_keep KE U9 (e_R (x_e rsegs cx)).
  w3b_chunks HS U9.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) =>
    rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ m HS eq_refl) at 1;
    apply (HP ly2 S2 W2 (ms_regs m) (ms_mem m) _ sh np [] r) end.
  unfold hs_cut_P, hs_Pbody. split; [split|].
  + w3b_core HS E HAE regs2 W2 HJ H234 Hfr Hperm Hio Hmo Hkeep KE.
  + split; [w3b_fsh HS HFSH KE W2 mem2|].
    split; [w3b_pp HS HPP KE W2 mem2 Lpc|].
    split; [exact HIN|]. split; [exact HSUF|].
    split; [split; [exact Hsh8|]; split; [constructor|]; split; [cbn; constructor | cbn; lia]|].
    split; [exact Hlen|]. split; [exact Esh|]. split; [exact Enp|]. split; [cbn; lia|].
    rewrite Er. reflexivity.
  + unfold hs_at_cx, hs_at, hs_L_P, hs_cur2. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; w3b_fact HS E.
Qed.
End d.
End b.

Print Assumptions hs_piece_W3b_pre.
