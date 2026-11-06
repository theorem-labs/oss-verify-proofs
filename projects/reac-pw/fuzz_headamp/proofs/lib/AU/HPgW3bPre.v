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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgW3bPre.v, with its module paths, module names and addresses changed; 187 of its 314 lines of code are new or changed and 148 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW3bPre.v at c7151e1be45 (role image A's
   preheader piece) for reac-pw/fuzz_headamp's image B: B's own code walked again (the cells the preheader spills
   and the ones the loops reload, measured on image B), the statement lib/AU/HPgSeg.v's; its walk tactics (den,
   fact, keep, core, fsh, pp) taken with rs_ / rm_ renamed to hsu_ / hm_. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the property loop's
   preheader of the build (M01) of LLVMFuzzerTestOneInput 0x80c40, PH 0x8137c -> N 0x81494 (nprops <> 0) / P
   0x82bec (nprops = 0), pod.h:397-398, the piece statement lib/AU/HPgSeg.v hsu_piece_W3b_pre_stmt at image B's
   record headamp_himg_B and builder pcs headamp_bld_B. Proves no function (kind: segment lemma).

   THE CODE (0x8137c .. 0x81490, 70 words). 0x8137c .. 0x813b0 spill a7 (the top word's offset 0), a6 (its
   address pp), s8 (the cap) and s7 (F) to R+0x28, R+0x30, R+0x20 and R+0x18, &pp->n_ent (pp + 0x4d14, from s5 =
   0x5000) and its shadow index to R+0x120 and R+0xe0, s9 = pp to R+0x148 and &pp->is_props (pp + 0x4008, from
   a1 = 0x4000) to R+0x8; 0x813ac loads nprops (R+0x100) and `bnez` 0x813b4 goes to 0x813bc or, through `j`
   0x813b8, to P. 0x813bc .. 0x81490 set the loop's registers (t4 = pp, seen s4 = 0, the index t0 = 0, &t in s9,
   &r in s6, the `/ 10` multiplier in s8, s7 = -8, s10 = 1) and the cells the property loop reloads (HPgSeg's
   hsu_Kc: the three pod_ent objects' addresses e F+0xf0, e42 F+0x180, e62 F+0x210 and the complements the
   pointer-overflow tests compare against). No instrumented check and no UBSan trap branch runs here.

   REGISTERS AND R-CELLS this file reads (the role port renames these): s1 = R (x9), s5 = 0x5000 (x21), s7 = F
   (x23), s8 = cap (x24), s9 = pp (x25), a1 = 0x4000 (x11), a6 = pp (x16), a7 = 0 (x17); R+0x48 = F, R+0x100 =
   nprops, R+0x138 = pp + 0x4000; it writes x5, x6, x7, x10 .. x17, x20, x22 .. x26, x29 and the R-relative cells
   R+0x8 .. R+0x150.

   HOW. As RPgW3bPre.v: the symbolic state is rebuilt from PH's cut over the token engine (no instrumented check
   runs here, so no shadow entry is needed); the R-relative cells are one region of base s1 with the write window
   [R+0x8, R+0x150), the segment's stack window, whose eight cells the end cut reads again are chunks (1 - null,
   ~pp, the shape flag and nprops over the extra atoms 32 .. 35). Every fact of the end cut is read from the final
   symbolic state: a register kept as its own atom from PH's fact, any other register from its symbolic value, a
   cell from its chunk. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSteps HPgSeg HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ===================================== the engine's context ===================================== *)
Definition HWP_PH : Z := 0x8137c.
Definition HWP_N : Z := 0x81494.
Definition HWP_P : Z := 0x82bec.
(* the 70 instruction words 0x8137c .. 0x81490 *)
Definition hwp_tbl : ctable := build_table rsegs HWP_PH 70 TEmpty.
Lemma hwp_tbl_ok : table_ok rsegs hwp_tbl.
Proof. apply build_table_ok0. unfold HWP_PH. lia. Qed.
Definition hwp_Bx : sv := SOff 27 0.
Definition hwp_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the shadow address of &pp->len as the code keeps it in R+0x150 *)
Definition hwp_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 0x4000) (SLit 3)) (SOff 27 0).
Definition HWP_M3FFD : Z := 0xffffffffffffc003.  (* -0x3ffd mod 2^64 *)
(* a1 = 0x4000, s5 = 0x5000 and a7 = 0 pinned to their literals *)
Definition hwp_regs : list sv :=
sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 11) (SLit 0x4000)) (Z_to_bv 5 21) (SLit 0x5000)) (Z_to_bv 5 17) (SLit 0).
(* the R-relative cells: the write window [R+0x8, R+0x150), the cells the end cut reads again as chunks *)
Definition hwp_slot : YP09.region :=
YP09.mkRegion (Some 9%nat) 0 0x158 0x8 0x150
[YP09.mkChunk 0x38 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x48 (CVal 8 (SOff 23 0));
 YP09.mkChunk 0xf0 (CVal 8 (SOff 33 0)); YP09.mkChunk 0xf8 (CVal 8 (SOff 34 0));
 YP09.mkChunk 0x100 (CVal 8 (SOff 35 0)); YP09.mkChunk 0x108 (CVal 8 (SLit HWP_M3FFD));
 YP09.mkChunk 0x138 (CVal 8 (SOff 25 0x4000)); YP09.mkChunk 0x150 (CVal 8 hwp_shx)].
Definition hwp_atoms : list (nat * afact) := [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 0)].
Definition hwp_ss : sstate := mkSS HWP_PH hwp_regs [hwp_slot] None (mkFacts hwp_atoms [] []).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* a register the final symbolic state still holds as its own atom keeps its value *)
Lemma hwp_reg_kept : forall E ss ms regs0 extra (H : word -> bool) (r : bv 5),
st_ok rsegs E ss (restrict H ms) -> (forall n, (n < 32)%nat -> ew E n = ew (Ereg regs0 extra) n) ->
sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms regs0 extra H r HS HA Hq.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
pose proof (u5_range r) as Hr. rewrite HA by lia. apply ew_Ereg_reg.
Qed.

End b.

(* two values equal mod 2^64 *)
Lemma hwp_mod_eq : forall a b k, a = b + k * 2 ^ 64 -> a mod 2 ^ 64 = b mod 2 ^ 64.
Proof. intros a b k ->. apply Z.mod_add. lia. Qed.
(* the value of a symbolic expression of a final state, from the exact values of its atoms (U facts in context) *)
Ltac hwp_den :=
  try unfold hwp_shx;
  rewrite denot_lit_U; apply Z_to_bv64_eq_mod;
  repeat match goal with H : U ?E ?x = _ |- context [U ?E ?x] => rewrite H end;
  rewrite ?U_SAlu, ?U_SOff, ?U_SLit; cbn [zalu_raw];
  repeat match goal with H : bv_unsigned (ew ?E ?n) = _ |- context [bv_unsigned (ew ?E ?n)] => rewrite H end;
  cbv [HSU_T HSU_CH HSU_R4 HSU_E HSU_E42 HSU_E62 HSU_MULT10 Layout.OFF_LEN Layout.OFF_IS_PROPS
       Layout.OFF_HAS_PARAMS Layout.OFF_PARAMS_STRUCT Layout.OFF_ENT Layout.OFF_N_ENT];
  rewrite ?Z.add_0_r; unfold zcanon, M64; rewrite ?Zmod_mod;
  first [reflexivity | f_equal; lia | lia | apply (hwp_mod_eq _ _ 1); lia | apply (hwp_mod_eq _ _ (-1)); lia].
(* the machine state a final symbolic state describes *)
Ltac hwp_ms HS := lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => m end.
Ltac hwp_split Cs :=
  repeat lazymatch type of Cs with _ /\ _ => let c := fresh "Cn" in destruct Cs as [c Cs] end.
(* the run's writes are the segment's stack window: the R-relative region on atom 9 *)
Ltac hwp_awr_slot U9 R sp :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp' ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp' fp b0 bc ly0 own0) end;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp));
    [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia | apply awr_ok_nil].
(* ... and those bytes are R-relative *)
Ltac hwp_kw U9 :=
  let a := fresh "a" in let rg := fresh "rg" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (rg & Hr & Hb);
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hr end;
  destruct Hr as [<-|[]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite U9 in Hb; lia.
(* fold a run's frame into the kept-bytes fact KE (every byte outside [R, R + 0x158) as at PH) *)
Ltac hwp_keep KE U9 R :=
  lazymatch goal with HFr : frame_of ?E0 ?rs (mrestrict _ _) (mrestrict _ _) |- _ =>
    let KW := fresh "KW" in let KE' := fresh "KE" in
    assert (KW : forall a, in_wrange E0 rs a -> R <= a < R + 0x158) by hwp_kw U9;
    pose proof (cb_kept_run (fun a => R <= a < R + 0x158) _ _ _ _ _ _ KE HFr KW) as KE';
    clear KE KW HFr; rename KE' into KE end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the final region's chunks, one hypothesis each *)
Ltac hwp_chunks HS U9 :=
  let HOK := fresh "HOK" in let Cs := fresh "Cs" in
  pose proof (st_ok_mem_ok rsegs _ _ _ HS) as (_ & HOK & _); cbn [ss_mem] in HOK;
  pose proof (Forall_inv HOK) as (_ & _ & _ & Cs); cbn [YP09.r_base YP09.r_chunks base_val] in Cs;
  rewrite U9 in Cs; clear HOK; repeat rewrite Forall_cons_iff in Cs; hwp_split Cs.
(* one (location, value) fact of an end cut, read from the final symbolic state HS: a register still its own atom
   from PH's fact, any other register from its symbolic value, a cell from the region's chunk at that offset *)
Ltac hwp_fact HS E HAE regs2 W2 :=
  let ms := hwp_ms HS in
  cbn [fst snd];
  lazymatch goal with
  | |- hd_at _ _ _ _ _ (LReg ?r) ?v =>
      first
      [ match goal with A : hd_at _ _ _ regs2 _ (LReg r) v |- _ =>
          cbn [hd_at];
          rewrite (hwp_reg_kept E _ ms regs2 _ (w_H W2) (Z_to_bv 5 r) HS HAE) by (vm_compute; reflexivity);
          exact A end
      | cbn [hd_at]; rewrite (st_ok_restrict_reg rsegs _ E _ ms (Z_to_bv 5 r) HS);
        lazymatch goal with |- sv_denot _ (sr_get ?l ?r') = _ =>
          let x := eval vm_compute in (sr_get l r') in change (sr_get l r') with x end;
        unfold w64; hwp_den ]
  | |- hd_at _ _ _ _ _ (LCell XR ?o) ?v =>
      cbn [hd_at hd_xv];
      match goal with C : YP09.chunk_ok _ _ _ _ (YP09.mkChunk o (CVal 8 ?ex)) |- _ =>
        apply (val_of_chunk_ok rsegs E _ _ o 8 ex _ C);
        [ hwp_den
        | split; [apply Z.mod_pos_bound; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia]
        | cbn; lia ]
      end
  end.
(* hsu_core at an end cut: the journal, s1 .. s3 as at the start (their own atoms), the frames, blocks, I/O and
   meter, and every byte outside the segment's write set as at the start (the run wrote only [R, R + 0x158), which
   is in hi_w1's real-frame range [R, R + 0x198)) *)
Ltac hwp_core HS E HAE regs2 W2 HJ H234 Hfr Hperm Hio Hmo Hkeep KE :=
  let ms := hwp_ms HS in
  unfold hsu_core, hsu_mid; split; [exact HJ|];
  split; [let rr := fresh "rr" in let Hrr := fresh "Hrr" in
          intros rr Hrr; rewrite <- (H234 rr Hrr); destruct Hrr as [->|[->| ->]];
          (eapply (hwp_reg_kept E _ ms regs2 _ (w_H W2)); [exact HS | exact HAE | vm_compute; reflexivity]) |];
  split; [exact Hfr|]; split; [exact Hperm|];
  split; [eapply same_io_trans; [exact Hio | cb_kio] |];
  split; [exact Hmo|];
  let a := fresh "a" in let Ha := fresh "Ha" in let HnS := fresh "HnS" in let HnE := fresh "HnE" in
  let X := fresh "X" in
  intros a Ha HnS HnE; rewrite <- (Hkeep a Ha HnS HnE); apply KE; [exact Ha|];
  intros X; cbv beta in X; apply HnE; unfold hsu_E1; left; unfold hd_inw; cbn [hi_w1 headamp_himg_B];
  apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; cbn [fst snd hd_xv]; lia.
(* the frame's shadow bytes: below the stack, so outside [R, R + 0x158) *)
Ltac hwp_fsh HS HFSH KE W2 mem2 :=
  let ms := hwp_ms HS in
  let i := fresh "i" in let Hi := fresh "Hi" in let X := fresh "X" in
  apply (hm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) _ _ HFSH);
  intros i Hi; unfold hsu_P0 in Hi; cbn [hi_shA headamp_himg_B] in Hi;
  change (length headamp_B_shA) with 116%nat in Hi;
  apply KE; [unfold shadow_addr, SHADOW_OFF; lia | intros X; cbv beta in X; unfold shadow_addr, SHADOW_OFF in X; lia].
(* the block's bytes: below the stack too *)
Ltac hwp_pp HS HPP KE W2 mem2 Lpc :=
  let ms := hwp_ms HS in
  let y := fresh "y" in let Hy := fresh "Hy" in let X := fresh "X" in
  apply (hm_bytes_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) _ _ HPP);
  rewrite Lpc; change (Z.of_nat 19744) with 19744;
  intros y Hy; apply KE; [lia | intros X; cbv beta in X; lia].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* the block's image has its full size at every shape *)
Lemma hwp_len_pc0 : forall sh, 0 <= sh < 8 -> length (pc_image (PbCut sh [] None)) = 19744%nat.
Proof.
intros sh Hsh. assert (H8 : sh = 0 \/ sh = 1 \/ sh = 2 \/ sh = 3 \/ sh = 4 \/ sh = 5 \/ sh = 6 \/ sh = 7) by lia.
destruct H8 as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

(* PH -> N | P at image B's record and builder pcs *)
Lemma hsu_piece_W3b_pre_B : hsu_piece_W3b_pre_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof.
intros cx POST rest HST HN HP ly2 S2 W2 regs2 mem2 md2 r sh np HC.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
destruct HST as (HPRE & _ & Hlen & _).
pose proof HPRE as (HJc & _ & _ & _ & _ & HSe & _ & HRsz & HRstk & Hown & HFe & _ & Hcap & Hnull & _ & _ & _ & _ & _ & _
  & _ & _ & Hppc & Hfresh).
cbn [hi_rsz hi_cid headamp_himg_B] in HRsz, Hown, HFe.
destruct HC as (HCORE & HAT & HFSH & HPP & HIN & HSUF & Esh & Enp & Er).
pose proof HCORE as (HJ & H234 & Hfr & Hperm & Hio & Hmo & Hkeep).
pose proof HJc as (HARc & _ & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (HT : T_SEG_STK = 16384) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hppc) as (_ & Hpp0 & Hppcl & Happ & _ & _).
change (req_size PP_SIZE) with 19744 in Hppcl, Happ.
assert (HFin : In (4, x_pos rsegs cx) (frames (x_Sc rsegs cx)))
  by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HARc HFin) as (HF0 & HFc & _).
rewrite <- HFe in HF0, HFc. change (fs_frame_bytes 4) with 1024 in HFc.
assert (Hnp : 0 <= np <= 3) by (assert (0 <= np < 4) by (rewrite Enp; unfold hsu_np; apply Z.mod_pos_bound; lia); lia).
assert (Hsh8 : 0 <= sh < 8) by (rewrite Esh; unfold hsu_sh; apply Z.mod_pos_bound; lia).
assert (HFd : 0 <= e_F (x_e rsegs cx) / 8 <= 17592184995840)
  by (split; [apply Z.div_pos; lia | apply (Z.div_le_mono _ 0x7fffff800000 8); lia]).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
pose proof (hwp_len_pc0 sh Hsh8) as Lpc.
(* PH's facts *)
unfold hsu_at_cx, hsu_at, hsu_L_PH in HAT. cbv zeta in HAT.
repeat rewrite Forall_cons_iff in HAT.
destruct HAT as (A11 & A16 & A17 & A8 & A9 & A19 & A27 & A21 & A23 & A24 & A25 & C38 & C48 & Cf0 & Cf8 & C100 & C108
  & C138 & C150 & A18 & A28 & _).
cbn [fst snd] in A11, A16, A17, A8, A9, A19, A27, A21, A23, A24, A25, C38, C48, Cf0, Cf8, C100, C108, C138, C150, A18,
  A28.
pose proof A9 as R9. pose proof A11 as R11. pose proof A16 as R16. pose proof A17 as R17. pose proof A21 as R21.
pose proof A23 as R23. pose proof A24 as R24. pose proof A25 as R25. pose proof A27 as R27.
pose proof C38 as V38. pose proof C48 as V48. pose proof Cf0 as Vf0. pose proof Cf8 as Vf8. pose proof C100 as V100.
pose proof C108 as V108. pose proof C138 as V138. pose proof C150 as V150.
cbn [hd_at hd_xv] in R9, R11, R16, R17, R21, R23, R24, R25, R27, V38, V48, Vf0, Vf8, V100, V108, V138, V150.
unfold Layout.OFF_LEN, Layout.POD_BUF_MAX in *.
remember (Ereg regs2 [Z_to_bv 64 (1 - e_null (x_e rsegs cx)); Z_to_bv 64 (- e_pp (x_e rsegs cx) - 1);
  Z_to_bv 64 (if sh =? 7 then 1 else 0); Z_to_bv 64 np]) as E eqn:HE.
assert (HAE : forall n, (n < 32)%nat -> ew E n = ew (Ereg regs2 [Z_to_bv 64 (1 - e_null (x_e rsegs cx));
  Z_to_bv 64 (- e_pp (x_e rsegs cx) - 1); Z_to_bv 64 (if sh =? 7 then 1 else 0); Z_to_bv 64 np]) n)
  by (intros; subst E; reflexivity).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr)
  by (intros n rr Hn; subst E; exact (ew_Ereg_nat regs2 _ n rr Hn)).
assert (Ux : forall n v, (n < 32)%nat -> getr regs2 (Z_to_bv 5 (Z.of_nat n)) = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew E n) = v).
{ intros n v Hn Hg Hv. rewrite (EE n (Z_to_bv 5 (Z.of_nat n))), Hg by (rewrite Z_to_bv_unsigned; unfold bv_wrap;
    change (bv_modulus 5) with 32; rewrite Z.mod_small; lia). apply unsigned_lit_small. exact Hv. }
assert (U9 : bv_unsigned (ew E 9) = e_R (x_e rsegs cx)) by (apply (Ux 9%nat); [lia | exact R9 | lia]).
assert (U16 : bv_unsigned (ew E 16) = e_pp (x_e rsegs cx)) by (apply (Ux 16%nat); [lia | exact R16 | lia]).
assert (U23 : bv_unsigned (ew E 23) = e_F (x_e rsegs cx)) by (apply (Ux 23%nat); [lia | exact R23 | lia]).
assert (U24 : bv_unsigned (ew E 24) = e_cap (x_e rsegs cx)) by (apply (Ux 24%nat); [lia | exact R24 | lia]).
assert (U25 : bv_unsigned (ew E 25) = e_pp (x_e rsegs cx)) by (apply (Ux 25%nat); [lia | exact R25 | lia]).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF) by (apply (Ux 27%nat); [lia | exact R27 | unfold SHADOW_OFF; lia]).
assert (U32 : bv_unsigned (ew E 32) = (1 - e_null (x_e rsegs cx)) mod 2 ^ 64)
  by (subst E; rewrite (ew_Ereg_extra regs2 _ 0); apply Z_to_bv_unsigned).
assert (U33 : bv_unsigned (ew E 33) = (- e_pp (x_e rsegs cx) - 1) mod 2 ^ 64)
  by (subst E; rewrite (ew_Ereg_extra regs2 _ 1); apply Z_to_bv_unsigned).
assert (U34 : bv_unsigned (ew E 34) = (if sh =? 7 then 1 else 0) mod 2 ^ 64)
  by (subst E; rewrite (ew_Ereg_extra regs2 _ 2); apply Z_to_bv_unsigned).
assert (U35 : bv_unsigned (ew E 35) = np mod 2 ^ 64)
  by (subst E; rewrite (ew_Ereg_extra regs2 _ 3); apply Z_to_bv_unsigned).
assert (HUshx : U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 0x4000) (SLit 3)) (SOff 27 0))
  = shadow_addr (e_pp (x_e rsegs cx) + 0x4000)).
{ rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, U25, U27, !Z.add_0_r.
  change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  unfold shadow_addr, zcanon, M64, SHADOW_OFF.
  assert (0 <= (e_pp (x_e rsegs cx) + 0x4000) / 8 < 2 ^ 61)
    by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (Z.mod_small (e_pp (x_e rsegs cx) + 0x4000)) by lia. rewrite (Z.mod_small 2147450880) by lia.
  rewrite (Z.mod_small ((e_pp (x_e rsegs cx) + 0x4000) / 8)) by lia. rewrite Z.mod_small by lia. lia. }
(* the values the preheader forms: the three complements (`not`), the shadow index of &pp->n_ent *)
assert (E23 : ew E 23 = Z_to_bv 64 (e_F (x_e rsegs cx))) by (rewrite <- U23; symmetry; apply Z_to_bv_bv_unsigned).
assert (E25 : ew E 25 = Z_to_bv 64 (e_pp (x_e rsegs cx))) by (rewrite <- U25; symmetry; apply Z_to_bv_bv_unsigned).
assert (HUc0 : U E (SAlu ALU_XOR (SOff 23 160) (SLit (-1))) = 2 ^ 64 - 1 - (e_F (x_e rsegs cx) + 160))
  by (apply U_not_off; [exact E23 | lia | lia]).
assert (HUe8 : U E (SAlu ALU_XOR (SOff 23 536) (SLit (-1))) = 2 ^ 64 - 1 - (e_F (x_e rsegs cx) + 536))
  by (apply U_not_off; [exact E23 | lia | lia]).
assert (HUd8 : U E (SAlu ALU_XOR (SOff 25 16404) (SLit (-1))) = 2 ^ 64 - 1 - (e_pp (x_e rsegs cx) + 16404))
  by (apply U_not_off; [exact E25 | lia | lia]).
assert (HUe0 : U E (SAlu ALU_SRL (SOff 25 19732) (SLit 3)) = Z.shiftr (e_pp (x_e rsegs cx) + 19732) 3).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit, U25.
  change (Z.land (zcanon 3) 63) with 3. unfold zcanon, M64.
  rewrite (Z.mod_small (e_pp (x_e rsegs cx) + 19732)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  apply Z.mod_small. split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
(* the symbolic state at PH *)
assert (HS : st_ok rsegs E hwp_ss (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 HWP_PH) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. rewrite HE. unfold hwp_ss. apply (entry_st_ok_full rsegs).
  - unfold hwp_regs.
    apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Ereg | reflexivity |] | reflexivity |]
      | reflexivity |].
    + rewrite R11. reflexivity.
    + rewrite R21. reflexivity.
    + rewrite R17. reflexivity.
  - vm_compute. reflexivity.
  - rewrite <- HE. constructor; [|constructor].
    unfold region_ok, hwp_slot. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable rsegs); apply Hstkp; lia|].
    repeat apply Forall_cons; try apply Forall_nil;
    match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 ?ex)) =>
      lazymatch goal with C : val_mem _ _ (_ + o) 8 ?v |- _ =>
        apply (chunk_ok_val rsegs E _ _ o 8 ex v);
        [ hwp_den
        | split; [apply Z.mod_pos_bound; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia]
        | cbn; lia | exact C ] end end.
  - rewrite <- HE. apply pairwise_disjoint_of_extents. cbn. tauto.
  - rewrite <- HE. split; [|split; exact I]. cbn [f_atoms hwp_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
assert (SHOK : sh_ok rsegs hwp_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) <= a < e_R (x_e rsegs cx) + 0x158) ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a) by (intros; reflexivity).
clear HE.
unfold cfg_at. change (w64 (bi_PH headamp_bld_B)) with (Z_to_bv 64 HWP_PH).
(* 0x8137c .. 0x813b0: the spills; stop at `bnez a0` 0x813b4 *)
aj_run_to_tok hwp_tbl_ok HS HJ SHOK hwp_Bspan HWP_N.
{ hwp_awr_slot U9 (e_R (x_e rsegs cx)) (x_sp0 rsegs cx). }
hwp_keep KE U9 (e_R (x_e rsegs cx)).
(* 0x813b4 bnez a0, a0 = nprops *)
srr_branch_tok hwp_tbl_ok HS SHOK hwp_Bspan.
- (* nprops <> 0: 0x813bc .. 0x81490, the loop's registers and cells, to N *)
  rewrite branch_ne_U, U_SOff, U_SLit, U35, Z.add_0_r in Hc. unfold zcanon, M64 in Hc.
  rewrite Zmod_mod, (Z.mod_small np), Z.mod_0_l in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
  aj_run_to_tok hwp_tbl_ok HS HJ SHOK hwp_Bspan HWP_N.
  { hwp_awr_slot U9 (e_R (x_e rsegs cx)) (x_sp0 rsegs cx). }
  hwp_keep KE U9 (e_R (x_e rsegs cx)).
  hwp_chunks HS U9.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) =>
    rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ m HS eq_refl) at 1;
    apply (HN ly2 S2 W2 (ms_regs m) (ms_mem m) _ sh np [] r eq_refl) end.
  unfold hsu_cut_N. split; [hwp_core HS E HAE regs2 W2 HJ H234 Hfr Hperm Hio Hmo Hkeep KE|].
  split.
  { unfold hsu_at_cx, hsu_at, hsu_L_N, hsu_Rc1, hsu_Rc0, hsu_Kc, hsu_cur2. cbv zeta. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; hwp_fact HS E HAE regs2 W2. }
  split; [hwp_fsh HS HFSH KE W2 mem2|].
  split; [hwp_pp HS HPP KE W2 mem2 Lpc|].
  split; [exact HIN|]. split; [exact HSUF|].
  split; [split; [exact Hsh8|]; split; [constructor|]; split; [cbn; constructor | cbn; lia]|].
  split; [exact Esh|]. split; [exact Enp|]. split; [cbn; lia|]. split; [lia|].
  rewrite Er. reflexivity.
- (* nprops = 0: `j` 0x813b8 to P *)
  rewrite branch_ne_U, U_SOff, U_SLit, U35, Z.add_0_r in Hc. unfold zcanon, M64 in Hc.
  rewrite Zmod_mod, (Z.mod_small np), Z.mod_0_l in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
  aj_run_to_tok hwp_tbl_ok HS HJ SHOK hwp_Bspan HWP_P.
  { hwp_awr_slot U9 (e_R (x_e rsegs cx)) (x_sp0 rsegs cx). }
  hwp_keep KE U9 (e_R (x_e rsegs cx)).
  hwp_chunks HS U9.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) =>
    rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ m HS eq_refl) at 1;
    apply (HP ly2 S2 W2 (ms_regs m) (ms_mem m) _ sh np [] r) end.
  unfold hsu_cut_P, hsu_Pbody. split; [split|].
  + hwp_core HS E HAE regs2 W2 HJ H234 Hfr Hperm Hio Hmo Hkeep KE.
  + split; [hwp_fsh HS HFSH KE W2 mem2|].
    split; [hwp_pp HS HPP KE W2 mem2 Lpc|].
    split; [exact HIN|]. split; [exact HSUF|].
    split; [split; [exact Hsh8|]; split; [constructor|]; split; [cbn; constructor | cbn; lia]|].
    split; [exact Hlen|]. split; [exact Esh|]. split; [exact Enp|]. split; [cbn; lia|].
    rewrite Er. reflexivity.
  + unfold hsu_at_cx, hsu_at, hsu_L_P. cbv zeta. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; hwp_fact HS E HAE regs2 W2.
Qed.
End d.
End c.

Print Assumptions hsu_piece_W3b_pre_B.
