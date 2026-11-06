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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 589 of its 629 lines of code are new or changed and 250 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW3b.v at c7151e1be458, ported to
   reac-pw/fuzz_rate image A: module paths and prefixes (RPg* -> RtPg*, rm_ -> rtm_, rl_ -> rt_, e_ -> q_) changed;
   rate's pcs, its shadow base s2 (x18), &pp->len in s7 (x23) and the shadow address of &pp->len in s6 (x22, pinned
   to its expression, as the code loads the shadow byte of pp->len through s6 and not through a cell); the Object
   header reads the shape and -0x3ffd from R+0xd8 and R+0x130; the start fact list has rate's five conjuncts; the
   image facts come from lib/A/RtPgSteps.v; the frame's shadow has 56 bytes. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW3b.v; 261 of its 310 lines of code are new or changed and 580 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW3bPre.v at c7151e1be458, ported to
   reac-pw/fuzz_rate image A: module paths and prefixes (RPg* -> RtPg*, rm_ -> rtm_, rl_ -> rt_, e_ -> q_) changed;
   rate's preheader (its pcs, registers and R-relative cells; the cursor in s9 / t0 at PH and in R+0x100 / s8 at N;
   the nprops test before the constant cells are written); the cells are five regions whose write windows are the
   three real-frame ranges of the build's write set (RtPgImgA hi_w1), so a run's frame keeps every byte outside them;
   the start fact list has rate's five conjuncts; the image facts come from lib/A/RtPgSteps.v. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the property loop's
   preheader of the build (M01) of LLVMFuzzerTestOneInput 0x80714, PH 0x80d38 -> N 0x80e10 (nprops <> 0) / P
   0x826d0 (nprops = 0), pod.h:397-398. Proves no function (kind: segment lemma).

   THE CODE. 0x80d38 .. 0x80d60 spill a6 (the top word's offset 0) to R+0x28, a5 (its address pp) to R+0x30, s9
   (the cursor) to R+0x100, s8 (F) to R+0x18, &pp->n_ent (pp + 0x4d14, from s3 = 0x5000) to R+0xb8 and its shadow
   index to R+0xa8, s10 (F) to R+0x78 and s11 (pp) to R+0xc0; 0x80d64 loads nprops (R+0xd0) and `bnez` 0x80d68
   leaves to 0x80d70 or, through `j` 0x80d6c, to P (where the bytes left are still in t0). 0x80d70 .. 0x80e0c set the
   loop's registers (seen = 0, i = 0, &t, &r, s8 = the bytes left, s10 = -0x4001) and the cells the property loop
   reloads (RtPgSeg.rs_Kc).

   HOW. As RtPgW3b.v: the symbolic state is rebuilt from PH's cut over the token engine (no instrumented check runs
   here, so no shadow entry is needed). The R-relative cells are five regions on s1: [R+0x10, R+0x38),
   [R+0x60, R+0x120) and [R+0x128, R+0x140) are writable (the three real-frame ranges of the build's write set
   RtPgImgA.hi_w1, inside the segment's stack window), [R+0x38, R+0x60) and [R+0x120, R+0x128) are read only. The
   ten cells the preheader keeps (b3, the four other header values and buflen, fl, mask, nprops, the shape, -0x3ffd)
   are their chunks, the nine input-dependent ones over the extra atoms 32 .. 40. a6 = 0 and s3 = 0x5000 are pinned.
   The engine stops at `bnez a0` 0x80d68 (a0 = nprops); the taken arm runs to N, the other to P. Every fact of the end
   cut is read from the final symbolic state: a register from its symbolic value, a cell from its chunk. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YI00 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgMem RtPgSeg RtPgW3b.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgSteps.
From OSSVerify.reac_pw.fuzz_rate.images Require Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
(* image A's loaded segments *)
Local Notation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* the three real-frame ranges the preheader may write (RtPgImgA hi_w1's R-relative ranges) *)
Definition w3b_Z (R a : Z) : Prop :=
(R + 0x10 <= a < R + 0x38) \/ (R + 0x60 <= a < R + 0x120) \/ (R + 0x128 <= a < R + 0x140).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* ===================================== PH -> N | P: the preheader =====================================
   0x80d38 .. 0x80e0c. a6 = 0 and s3 = 0x5000 are pinned. *)
Definition w3b_regs_ph : list sv := sr_set (sr_set sr_atoms (Z_to_bv 5 16) (SLit 0)) (Z_to_bv 5 19) (SLit 0x5000).
Definition w3b_ph_rA : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x10 0x38 0x10 0x38 [YP09.mkChunk 0x20 (CVal 8 (SOff 32 0))].
Definition w3b_ph_rB : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x38 0x60 0 0
[YP09.mkChunk 0x38 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x40 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x48 (CVal 8 (SOff 35 0));
 YP09.mkChunk 0x50 (CVal 8 (SOff 36 0)); YP09.mkChunk 0x58 (CVal 8 (SOff 37 0))].
Definition w3b_ph_rC : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x60 0x120 0x60 0x120
[YP09.mkChunk 0xd0 (CVal 8 (SOff 39 0)); YP09.mkChunk 0xd8 (CVal 8 (SOff 40 0))].
Definition w3b_ph_rE : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x120 0x128 0 0 [YP09.mkChunk 0x120 (CVal 8 (SOff 38 0))].
Definition w3b_ph_rD : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x128 0x140 0x128 0x140 [YP09.mkChunk 0x130 (CVal 8 (SLit W3B_M3FFD))].
Definition w3b_atoms_ph : list (nat * afact) := [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 0)].
Definition w3b_ss_ph : sstate :=
mkSS W3B_PH w3b_regs_ph [w3b_ph_rA; w3b_ph_rB; w3b_ph_rC; w3b_ph_rE; w3b_ph_rD] None (mkFacts w3b_atoms_ph [] []).

(* the value of a symbolic expression of a final state, from the exact values of its atoms (U facts in context) *)
Ltac w3b_den :=
  rewrite denot_lit_U; apply Z_to_bv64_eq_mod;
  repeat match goal with H : U ?E ?x = _ |- context [U ?E ?x] => rewrite H end;
  rewrite ?U_SAlu, ?U_SOff, ?U_SLit; cbn [zalu_raw];
  repeat match goal with H : bv_unsigned (ew ?E ?n) = _ |- context [bv_unsigned (ew ?E ?n)] => rewrite H end;
  rewrite ?Z.add_0_r; unfold zcanon, M64; rewrite ?Zmod_mod;
  first [reflexivity | f_equal; lia | lia].
(* the machine state a final symbolic state describes *)
Ltac w3b_ms HS := lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => m end.
(* one (location, value) fact of a cut, read from the final symbolic state HS: a register from its symbolic value,
   a cell from the chunk at that offset of one of the regions *)
Ltac w3b_fact HS E :=
  let ms := w3b_ms HS in
  cbn [fst snd rt_at rt_xv];
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
Ltac w3b_kio := first [apply same_io_refl | eapply same_io_trans; [| apply RtPgSteps.same_io_wvb]; w3b_kio].
(* the run's writes are the segment's stack window: each writable region on atom 9, R = sp0 + (R - sp0); the
   read-only ones write nothing *)
Ltac w3b_awr_ph U9 R sp :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp' ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp' fp b0 bc ly0 own0) end;
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp));
        [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |] ].
(* ... and those bytes are in w3b_Z *)
Ltac w3b_kw U9 :=
  let a := fresh "a" in let rg := fresh "rg" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (rg & Hr & Hb); unfold w3b_Z;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hr end;
  repeat (destruct Hr as [<-|Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite U9 in Hb; lia |]);
  destruct Hr.
(* fold a run's frame into the kept-bytes fact KE (every byte outside w3b_Z R as at PH) *)
Ltac w3b_keep KE U9 R :=
  lazymatch goal with HFr : frame_of ?E0 ?rs (mrestrict _ _) (mrestrict _ _) |- _ =>
    let KW := fresh "KW" in let KE' := fresh "KE" in
    assert (KW : forall a, in_wrange E0 rs a -> w3b_Z R a) by w3b_kw U9;
    pose proof (w3b_kept_run (w3b_Z R) _ _ _ _ _ _ KE HFr KW) as KE';
    clear KE KW HFr; rename KE' into KE end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the final regions' chunks, one hypothesis each *)
Ltac w3b_chunks HS U9 :=
  let HOK := fresh "HOK" in
  pose proof (st_ok_mem_ok rsegs _ _ _ HS) as (_ & HOK & _); cbn [ss_mem] in HOK;
  repeat (lazymatch type of HOK with
    | Forall _ (_ :: _) =>
        let Cs := fresh "Cs" in
        pose proof (Forall_inv HOK) as (_ & _ & _ & Cs); apply Forall_inv_tail in HOK;
        cbn [YP09.r_base YP09.r_chunks base_val] in Cs; rewrite U9 in Cs;
        repeat rewrite Forall_cons_iff in Cs; w3b_split_chunks Cs
    end);
  clear HOK.
(* rs_core at the end: the journal, s1 .. s3 as at the start (their own atoms), the frames, blocks, I/O and meter,
   and every byte outside the segment's write set as at the start (the run wrote only w3b_Z R, which is three of
   hi_w1's real-frame ranges) *)
Ltac w3b_core HS E HAE regs2 W2 HJ H234 Hfr Hperm Hio Hmo Hkeep KE :=
  let ms := w3b_ms HS in
  unfold rs_core, rs_mid; split; [exact HJ|];
  split; [let rr := fresh "rr" in let Hrr := fresh "Hrr" in
          intros rr Hrr; rewrite <- (H234 rr Hrr); destruct Hrr as [->|[->| ->]];
          (eapply (w3b_reg_kept E _ ms regs2 _ (w_H W2)); [exact HS | exact HAE | vm_compute; reflexivity]) |];
  split; [exact Hfr|]; split; [exact Hperm|];
  split; [eapply same_io_trans; [exact Hio | w3b_kio] |];
  split; [exact Hmo|];
  let a := fresh "a" in let Ha := fresh "Ha" in let HnS := fresh "HnS" in let HnE := fresh "HnE" in
  let X := fresh "X" in
  intros a Ha HnS HnE; rewrite <- (Hkeep a Ha HnS HnE); apply KE; [exact Ha|];
  intros X; apply HnE; unfold rs_E1; left; unfold rt_inw; cbn [hi_w1 rate_himg_A];
  unfold w3b_Z in X; destruct X as [X|[X|X]];
  [ apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd
  | apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd
  | apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd ];
  cbn [fst snd rt_xv]; lia.
(* the frame's shadow bytes: below the stack, so outside w3b_Z R *)
Ltac w3b_fsh HS HFSH KE W2 mem2 :=
  let ms := w3b_ms HS in
  let i := fresh "i" in let Hi := fresh "Hi" in let X := fresh "X" in
  apply (rtm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) _ rs_P0 HFSH);
  intros i Hi; change (length rs_P0) with 56%nat in Hi;
  apply KE; [unfold shadow_addr, SHADOW_OFF; lia | intros X; unfold w3b_Z, shadow_addr, SHADOW_OFF in X; lia].
(* the block's bytes: below the stack too *)
Ltac w3b_pp HS HPP KE W2 mem2 Lpc :=
  let ms := w3b_ms HS in
  let y := fresh "y" in let Hy := fresh "Hy" in let X := fresh "X" in
  apply (rtm_bytes_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) _ _ HPP);
  rewrite Lpc; change (Z.of_nat 19744) with 19744;
  intros y Hy; apply KE; [lia | intros X; unfold w3b_Z in X; lia].

(* the block's image has its full size at every shape *)
Lemma w3b_len_pc0 : forall sh, 0 <= sh < 8 -> length (pc_image (PbCut sh [] None)) = 19744%nat.
Proof.
intros sh Hsh. assert (H8 : sh = 0 \/ sh = 1 \/ sh = 2 \/ sh = 3 \/ sh = 4 \/ sh = 5 \/ sh = 6 \/ sh = 7) by lia.
destruct H8 as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

(* PH -> N | P *)
Lemma rs_piece_W3b_pre : rs_piece_W3b_pre_stmt rsegs B MT.
Proof.
intros cx POST rest HST HN HP ly2 S2 W2 regs2 mem2 md2 r sh np HC.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof RtPgSteps.rts_wx as Hwx. pose proof RtPgSteps.rts_segs_low as Hsegs.
destruct HST as (HPRE & _ & _ & Hlen & _).
pose proof HPRE as (HJc & _ & _ & _ & _ & HSe & _ & HRsz & HRstk & Hown & HFe & _ & Hppc & _ & _ & _ & _ & _ & _ & _
  & Hfresh & _ & _).
cbn [hi_rsz hi_cid rate_himg_A] in HRsz, Hown, HFe.
destruct HC as (HCORE & HAT & HFSH & HPP & HIN & HSUF & Esh & Enp & Er).
pose proof HCORE as (HJ & H234 & Hfr & Hperm & Hio & Hmo & Hkeep).
pose proof HJc as (HARc & _ & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (HT : T_SEG_STK = 16384) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hppc) as (_ & Hpp0 & Hppcl & Happ & _ & _).
change (req_size PP_SIZE) with 19744 in Hppcl, Happ.
assert (HFin : In (3, x_pos rsegs cx) (frames (x_Sc rsegs cx))) by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HARc HFin) as (HF0 & HFc & _).
rewrite <- HFe in HF0, HFc. change (fs_frame_bytes 3) with 512 in HFc.
assert (Hnp : 0 <= np <= 3) by (assert (0 <= np < 4) by (rewrite Enp; unfold rs_np; apply Z.mod_pos_bound; lia); lia).
assert (Hsh8 : 0 <= sh < 8) by (rewrite Esh; unfold rs_sh; apply Z.mod_pos_bound; lia).
assert (HFd : 0 <= q_F (x_e rsegs cx) / 8 <= 17592184995840)
  by (split; [apply Z.div_pos; lia | apply (Z.div_le_mono _ 0x7fffff800000 8); lia]).
assert (HPd : 0 <= (q_pp (x_e rsegs cx) + 0x4000) / 8 <= 17592184995840)
  by (split; [apply Z.div_pos; lia | apply (Z.div_le_mono _ 0x7fffff800000 8); lia]).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
pose proof (w3b_len_pc0 sh Hsh8) as Lpc.
(* the cursor and the bytes left are in range *)
assert (Hcur : 0 <= rs_cur rsegs cx rest r < 2 ^ 64 /\ 0 <= Z.of_nat (length r) < 2 ^ 64).
{ pose proof HIN as (Hleft & _ & _ & _ & _ & Hsrc0 & Hsrc1 & _).
  pose proof HSUF as (j & Hj & Hrj). unfold rs_cur. rewrite Hrj, length_skipn. lia. }
(* PH's facts *)
unfold rs_at_cx, rs_at, rs_L_PH, rs_Hc, rs_cur2h in HAT. cbn [app] in HAT.
repeat rewrite Forall_cons_iff in HAT.
destruct HAT as (A15 & A16 & A19 & A8 & A9 & A20 & A18 & A23 & A24 & A26 & A27 & C58 & Cd0 & Cd8 & A22 & C130
  & C20 & C38 & C40 & C48 & C50 & C120 & A25 & A5 & _).
cbn [fst snd rt_at rt_xv] in A15, A16, A19, A8, A9, A20, A18, A23, A24, A26, A27, C58, Cd0, Cd8, A22, C130,
  C20, C38, C40, C48, C50, C120, A25, A5.
remember (Ereg regs2 [Z_to_bv 64 (q_b3 (x_e rsegs cx)); Z_to_bv 64 (Z.shiftl (q_b6 (x_e rsegs cx)) 8);
  Z_to_bv 64 (q_b5 (x_e rsegs cx)); Z_to_bv 64 (Z.shiftl (q_b4 (x_e rsegs cx)) 8); Z_to_bv 64 (q_buflen (x_e rsegs cx));
  Z_to_bv 64 (q_fl (x_e rsegs cx)); Z_to_bv 64 (q_mask (x_e rsegs cx)); Z_to_bv 64 np; Z_to_bv 64 sh]) as E eqn:HE.
assert (HAE : forall n, (n < 32)%nat -> ew E n = ew (Ereg regs2 [Z_to_bv 64 (q_b3 (x_e rsegs cx));
  Z_to_bv 64 (Z.shiftl (q_b6 (x_e rsegs cx)) 8); Z_to_bv 64 (q_b5 (x_e rsegs cx));
  Z_to_bv 64 (Z.shiftl (q_b4 (x_e rsegs cx)) 8); Z_to_bv 64 (q_buflen (x_e rsegs cx)); Z_to_bv 64 (q_fl (x_e rsegs cx));
  Z_to_bv 64 (q_mask (x_e rsegs cx)); Z_to_bv 64 np; Z_to_bv 64 sh]) n) by (intros; subst E; reflexivity).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr)
  by (intros n rr Hn; subst E; exact (ew_Ereg_nat regs2 _ n rr Hn)).
assert (Ux : forall n v, (n < 32)%nat -> getr regs2 (Z_to_bv 5 (Z.of_nat n)) = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew E n) = v).
{ intros n v Hn Hg Hv. rewrite (EE n (Z_to_bv 5 (Z.of_nat n))), Hg by (rewrite Z_to_bv_unsigned; unfold bv_wrap;
    change (bv_modulus 5) with 32; rewrite Z.mod_small; lia). apply unsigned_lit_small. exact Hv. }
assert (Uex : forall j v, nth j [Z_to_bv 64 (q_b3 (x_e rsegs cx)); Z_to_bv 64 (Z.shiftl (q_b6 (x_e rsegs cx)) 8);
  Z_to_bv 64 (q_b5 (x_e rsegs cx)); Z_to_bv 64 (Z.shiftl (q_b4 (x_e rsegs cx)) 8); Z_to_bv 64 (q_buflen (x_e rsegs cx));
  Z_to_bv 64 (q_fl (x_e rsegs cx)); Z_to_bv 64 (q_mask (x_e rsegs cx)); Z_to_bv 64 np; Z_to_bv 64 sh] (Z_to_bv 64 0)
  = Z_to_bv 64 v -> bv_unsigned (ew E (32 + j)%nat) = v mod 2 ^ 64).
{ intros j v Hj. subst E. rewrite (ew_Ereg_extra regs2 _ j), Hj. apply Z_to_bv_unsigned. }
assert (U5 : bv_unsigned (ew E 5) = Z.of_nat (length r)) by (apply (Ux 5%nat); [lia | exact A5 | lia]).
assert (U8 : bv_unsigned (ew E 8) = q_S (x_e rsegs cx)) by (apply (Ux 8%nat); [lia | exact A8 | lia]).
assert (U9 : bv_unsigned (ew E 9) = q_R (x_e rsegs cx)) by (apply (Ux 9%nat); [lia | exact A9 | lia]).
assert (U15 : bv_unsigned (ew E 15) = q_pp (x_e rsegs cx)) by (apply (Ux 15%nat); [lia | exact A15 | lia]).
assert (U16 : bv_unsigned (ew E 16) = 0) by (apply (Ux 16%nat); [lia | exact A16 | lia]).
assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF) by (apply (Ux 18%nat); [lia | exact A18 | unfold SHADOW_OFF; lia]).
assert (U19 : bv_unsigned (ew E 19) = 0x5000) by (apply (Ux 19%nat); [lia | exact A19 | lia]).
assert (U20 : bv_unsigned (ew E 20) = shadow_addr (q_F (x_e rsegs cx)))
  by (apply (Ux 20%nat); [lia | exact A20 | unfold shadow_addr, SHADOW_OFF; lia]).
assert (U22 : bv_unsigned (ew E 22) = shadow_addr (q_pp (x_e rsegs cx) + 0x4000))
  by (apply (Ux 22%nat); [lia | exact A22 | unfold shadow_addr, SHADOW_OFF; lia]).
assert (U23 : bv_unsigned (ew E 23) = q_pp (x_e rsegs cx) + 0x4000) by (apply (Ux 23%nat); [lia | exact A23 | lia]).
assert (U24 : bv_unsigned (ew E 24) = q_F (x_e rsegs cx)) by (apply (Ux 24%nat); [lia | exact A24 | lia]).
assert (U25 : bv_unsigned (ew E 25) = rs_cur rsegs cx rest r) by (apply (Ux 25%nat); [lia | exact A25 | lia]).
assert (U26 : bv_unsigned (ew E 26) = q_F (x_e rsegs cx)) by (apply (Ux 26%nat); [lia | exact A26 | lia]).
assert (U27 : bv_unsigned (ew E 27) = q_pp (x_e rsegs cx)) by (apply (Ux 27%nat); [lia | exact A27 | lia]).
assert (U32 : bv_unsigned (ew E 32) = q_b3 (x_e rsegs cx) mod 2 ^ 64) by exact (Uex 0%nat _ eq_refl).
assert (U33 : bv_unsigned (ew E 33) = Z.shiftl (q_b6 (x_e rsegs cx)) 8 mod 2 ^ 64) by exact (Uex 1%nat _ eq_refl).
assert (U34 : bv_unsigned (ew E 34) = q_b5 (x_e rsegs cx) mod 2 ^ 64) by exact (Uex 2%nat _ eq_refl).
assert (U35 : bv_unsigned (ew E 35) = Z.shiftl (q_b4 (x_e rsegs cx)) 8 mod 2 ^ 64) by exact (Uex 3%nat _ eq_refl).
assert (U36 : bv_unsigned (ew E 36) = q_buflen (x_e rsegs cx) mod 2 ^ 64) by exact (Uex 4%nat _ eq_refl).
assert (U37 : bv_unsigned (ew E 37) = q_fl (x_e rsegs cx) mod 2 ^ 64) by exact (Uex 5%nat _ eq_refl).
assert (U38 : bv_unsigned (ew E 38) = q_mask (x_e rsegs cx) mod 2 ^ 64) by exact (Uex 6%nat _ eq_refl).
assert (U39 : bv_unsigned (ew E 39) = np mod 2 ^ 64) by exact (Uex 7%nat _ eq_refl).
assert (U40 : bv_unsigned (ew E 40) = sh mod 2 ^ 64) by exact (Uex 8%nat _ eq_refl).
clear Uex.
assert (HU68 : U E (SAlu ALU_SRL (SOff 27 19732) (SLit 3)) = Z.shiftr (q_pp (x_e rsegs cx) + 0x4d14) 3).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit, U27.
  change (Z.land (zcanon 3) 63) with 3. unfold zcanon, M64.
  rewrite (Z.mod_small (q_pp (x_e rsegs cx) + 19732)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  apply Z.mod_small. split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
(* the symbolic state at PH *)
assert (HS : st_ok rsegs E w3b_ss_ph (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 W3B_PH) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. rewrite HE. unfold w3b_ss_ph. apply (entry_st_ok_full rsegs).
  - unfold w3b_regs_ph. apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Ereg | reflexivity |] | reflexivity |].
    + rewrite A16. reflexivity.
    + rewrite A19. reflexivity.
  - vm_compute. reflexivity.
  - rewrite <- HE. unfold w3b_ph_rA, w3b_ph_rB, w3b_ph_rC, w3b_ph_rE, w3b_ph_rD.
    repeat apply Forall_cons; try apply Forall_nil;
    (unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
     rewrite U9; split; [lia|]; split; [lia|];
     split; [intros o Ho; first [lia | apply (apresent_writable rsegs); apply Hstkp; lia]|];
     repeat apply Forall_cons; try apply Forall_nil;
     match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 ?ex)) =>
       lazymatch goal with C : val_mem _ _ (_ + o) 8 ?v |- _ =>
         apply (chunk_ok_val rsegs E _ _ o 8 ex v);
         [ w3b_den
         | split; [apply Z.mod_pos_bound; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia]
         | cbn; lia | exact C ] end end).
  - rewrite <- HE. apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val w3b_ph_rA w3b_ph_rB w3b_ph_rC w3b_ph_rE w3b_ph_rD]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - rewrite <- HE. split; [|split; exact I]. cbn [f_atoms w3b_atoms_ph atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
assert (SHOK : sh_ok rsegs w3b_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ w3b_Z (q_R (x_e rsegs cx)) a ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a) by (intros; reflexivity).
clear HE.
unfold cfg_at. change (w64 RS_PH) with (Z_to_bv 64 W3B_PH).
(* 0x80d38 .. 0x80d64: the spills of the top word's offset and address, the cursor, F, &pp->n_ent and its shadow
   index, F again and pp; stop at `bnez a0` *)
aj_run_to_tok w3b_tbl_ok HS HJ SHOK w3b_Bspan W3B_N.
{ w3b_awr_ph U9 (q_R (x_e rsegs cx)) (x_sp0 rsegs cx). }
(* the run wrote only the three windows *)
w3b_keep KE U9 (q_R (x_e rsegs cx)).
(* 0x80d68 bnez a0, a0 = nprops *)
srr_branch_tok w3b_tbl_ok HS SHOK w3b_Bspan.
- (* nprops <> 0: 0x80d70 .. 0x80e0c, the loop's registers and cells, to N *)
  rewrite branch_ne_U, U_SOff, U_SLit, U39, Z.add_0_r in Hc. unfold zcanon, M64 in Hc.
  rewrite Zmod_mod, (Z.mod_small np), Z.mod_0_l in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
  aj_run_to_tok w3b_tbl_ok HS HJ SHOK w3b_Bspan W3B_N.
  { w3b_awr_ph U9 (q_R (x_e rsegs cx)) (x_sp0 rsegs cx). }
  w3b_keep KE U9 (q_R (x_e rsegs cx)).
  w3b_chunks HS U9.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) =>
    rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ m HS eq_refl) at 1;
    apply (HN ly2 S2 W2 (ms_regs m) (ms_mem m) _ sh np [] r eq_refl) end.
  unfold rs_cut_N. split; [w3b_core HS E HAE regs2 W2 HJ H234 Hfr Hperm Hio Hmo Hkeep KE|].
  split.
  { unfold rs_at_cx, rs_at, rs_L_N, rs_Rc, rs_Rc0, rs_Kc, rs_Hc, rs_cur2. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; w3b_fact HS E. }
  split; [w3b_fsh HS HFSH KE W2 mem2|].
  split; [w3b_pp HS HPP KE W2 mem2 Lpc|].
  split; [exact HIN|]. split; [exact HSUF|].
  split; [split; [exact Hsh8|]; split; [constructor|]; split; [cbn; constructor | cbn; lia]|].
  split; [exact Esh|]. split; [exact Enp|]. split; [cbn; lia|]. split; [lia|].
  rewrite Er. reflexivity.
- (* nprops = 0: `j` 0x80d6c to P *)
  rewrite branch_ne_U, U_SOff, U_SLit, U39, Z.add_0_r in Hc. unfold zcanon, M64 in Hc.
  rewrite Zmod_mod, (Z.mod_small np), Z.mod_0_l in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
  aj_run_to_tok w3b_tbl_ok HS HJ SHOK w3b_Bspan W3B_P.
  { w3b_awr_ph U9 (q_R (x_e rsegs cx)) (x_sp0 rsegs cx). }
  w3b_keep KE U9 (q_R (x_e rsegs cx)).
  w3b_chunks HS U9.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) =>
    rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ m HS eq_refl) at 1;
    apply (HP ly2 S2 W2 (ms_regs m) (ms_mem m) _ sh np [] r) end.
  unfold rs_cut_P, rs_Pbody. split; [split|].
  + w3b_core HS E HAE regs2 W2 HJ H234 Hfr Hperm Hio Hmo Hkeep KE.
  + split; [w3b_fsh HS HFSH KE W2 mem2|].
    split; [w3b_pp HS HPP KE W2 mem2 Lpc|].
    split; [exact HIN|]. split; [exact HSUF|].
    split; [split; [exact Hsh8|]; split; [constructor|]; split; [cbn; constructor | cbn; lia]|].
    split; [exact Hlen|]. split; [exact Esh|]. split; [exact Enp|]. split; [cbn; lia|].
    rewrite Er. reflexivity.
  + unfold rs_at_cx, rs_at, rs_L_P, rs_Hc. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; w3b_fact HS E.
Qed.
End d.
End b.

Print Assumptions rs_piece_W3b_pre.
