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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 141 of its 170 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aHead.v at 876d0cb3d0d6; the plain run with
   frame-shadow stores of w6_head, here for reac-pw/fuzz_rate's last run of the walk piece W8 (the stores write 0xf8,
   the run ends at the pod loop's latch instead of a call, and the post is RtPgSteps.rts_post). *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the run lemma rw8_runD of
   lib/A/RtPgW8Kit.v, the last run of the walk piece "write + record" of LLVMFuzzerTestOneInput (pod.h:433):
     0x81ff8  ld a1,0x128(s1)                   a1 := k (only when `first` was set; else entered at 0x81ffc)
     0x81ffc  li a0,-8
     0x82000 .. 0x82034  13 x sb a0,o(s4)       shadow_addr F + 0x1e .. 0x2a := 0xf8 (e goes out of scope)
     0x82030  addiw a1,a1,1                     k + 1
     0x82038  ld a0,0xf0(s1)                    cnt
     0x8203c  bne a1,a0,0x8127c                 the pod loop's head C (k + 1 <> cnt)
     0x82040  j 0x82484                         the params Struct's close CL (k + 1 = cnt)
   Proves no function (kind: segment lemma).
   HOW. One plain engine run (lib/Reusable/YCbq.v aj_run_to over rw8_tblD) per entry pc and per exit, over two
   regions: the real frame's cells [R+0xf0, R+0x130) based at the s1 atom (read only; the chunks at 0xf0 and 0x128
   are cnt and k, the extra env slots 32 and 33), and the 13 shadow bytes [0x1e, 0x2b) of the frame for locals (3,
   pos) based at the s4 atom (write window: the frame's shadow, RtPgSteps.rts_awr_ok_fsh). The latch is not decided by
   the atom ranges, so each exit's start state carries its condition fact (k + 1 <> cnt, or k + 1 = cnt). When the run
   enters at 0x81ffc, a1 is pinned to the k atom. No instrumented check is in the block. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgMem RtPgSteps RtPgW8Kit.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ---- the entry state of the run ---- *)
(* env slot 32 = cnt (the cell R+0xf0), slot 33 = k (the cell R+0x128) *)
Definition rw8D_extra (cnt kk : Z) : list word := [w64 cnt; w64 kk].
Definition rw8D_rR : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xf0 0x130 0 0
   [YP09.mkChunk 0xf0 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x128 (CVal 8 (SOff 33 0))].
Definition rw8D_rS : YP09.region := YP09.mkRegion (Some 20%nat) 0x1e 0x2b 0x1e 0x2b [].
(* the latch's two exits, as condition facts *)
Definition rw8D_cC : acond := mkAC BC_NE (SOff 33 1) (SOff 32 0).
Definition rw8D_cL : acond := mkAC BC_EQ (SOff 33 1) (SOff 32 0).
Definition rw8D_facts (c : acond) : facts := mkFacts [(32%nat, mkAF 1 32 0); (33%nat, mkAF 0 31 0)] [c] [].
(* at 0x81ffc a1 already holds k *)
Definition rw8D_sr (pc0 : Z) : list sv :=
  if pc0 =? RW8_T0 then sr_set sr_atoms (11%bv : bv 5) (SOff 33 0) else sr_atoms.
Definition rw8D_ss (pc0 : Z) (c : acond) : sstate := mkSS pc0 (rw8D_sr pc0) [rw8D_rR; rw8D_rS] None (rw8D_facts c).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* a one-byte chunk of value 0xf8 *)
Lemma rw8D_chunkf8 : forall E H mem base o,
YP09.chunk_ok rsegs E (mrestrict H mem) base (YP09.mkChunk o (CVal 1 (SLit 18446744073709551608))) ->
aview rsegs H mem (base + o) = Some 0xf8.
Proof.
intros E H mem base o Hc. unfold aview. rewrite (rw8_mbyte_chunk1 E _ base o _ Hc). cbn [option_map].
rewrite U_SLit. f_equal; vm_compute; reflexivity.
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

Lemma rw8_runD : rw8_runD_stmt B MT.
Proof using MTL LAWS.
unfold rw8_runD_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pos cnt kk pc0
HJ (HR16 & HRs & HRe & HRlo & Hown & HFe & HFapp & HF32) Hpc H11 H2 H9 H20 Vcnt Vkk Hcnt Hkk.
pose proof rw8_wx as Hwx. pose proof rw8_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
unfold T_SEG_STK, ASTACK, kHighMemBeg in HRlo. unfold T_SEG_STK, ASTACK in HRs.
assert (Hin3 : In (3, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 3 pos HAR Hin3) as (_ & _ & _ & Hfsh).
rewrite <- HFe in Hfsh. change (fs_frame_bytes 3 / 8) with 64 in Hfsh.
destruct (rts_fbounds F HF32 HFapp) as (HFlo & HFc & Hsa0 & Hsac & _ & _).
(* the frame's shadow lies below the high application memory, so below R *)
assert (HSB : shadow_addr F + 64 <= 0x10007fff8000).
{ pose proof ASAN_CEIL_range as (AC & _).
  assert (HF8 : F + 512 <= 140737488355328) by (unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp; lia).
  assert (HF9 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; lia).
  unfold shadow_addr, SHADOW_OFF. lia. }
clear HAR.
(* the entry state's atoms *)
assert (U9 : bv_unsigned (ew (Ereg regs (rw8D_extra cnt kk)) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (U20 : bv_unsigned (ew (Ereg regs (rw8D_extra cnt kk)) 20) = shadow_addr F).
{ rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl), H20. unfold w64. apply unsigned_lit_small. lia. }
assert (E32 : ew (Ereg regs (rw8D_extra cnt kk)) 32 = Z_to_bv 64 cnt)
  by exact (ew_Ereg_extra regs (rw8D_extra cnt kk) 0).
assert (E33 : ew (Ereg regs (rw8D_extra cnt kk)) 33 = Z_to_bv 64 kk)
  by exact (ew_Ereg_extra regs (rw8D_extra cnt kk) 1).
(* the entry state, for either entry pc and either condition fact *)
assert (ENT : forall c, acond_ok (Ereg regs (rw8D_extra cnt kk)) c ->
  st_ok rsegs (Ereg regs (rw8D_extra cnt kk)) (rw8D_ss pc0 c)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc0) memc (seg_rom rsegs)))).
{ intros c Hc. rewrite restrict_mkst_fx. unfold rw8D_ss. apply (entry_st_ok_full rsegs).
  - unfold rw8D_sr. destruct (pc0 =? RW8_T0) eqn:Ht; [|apply regs_ok_Ereg].
    apply Z.eqb_eq in Ht.
    apply rw8_regs_ok_override; [apply regs_ok_Ereg | apply rw8_nz; vm_compute; intros X; discriminate X |].
    rewrite (H11 Ht). apply rts_den_atom; [exact E33 | lia].
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, rw8D_rR.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val rsegs _ _ R 0xf0 8 (SOff 32 0) cnt); [| cbn; lia | cbn; lia | exact Vcnt].
        apply rts_den_atom; [exact E32 | lia].
      * apply (chunk_ok_val rsegs _ _ R 0x128 8 (SOff 33 0) kk); [| cbn; lia | cbn; lia | exact Vkk].
        apply rts_den_atom; [exact E33 | lia].
    + unfold region_ok, rw8D_rS.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U20.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable rsegs). exact (proj1 (Hfsh o ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; [exact I | exact I]].
    unfold extent_disjoint, rw8D_rR, rw8D_rS. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U20.
    lia.
  - unfold facts_ok, rw8D_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [split; [exact Hc | exact I] | exact I]].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, E33.
    rewrite !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    split; [repeat split; lia|]. split; [repeat split; lia | exact I]. }
remember (Ereg regs (rw8D_extra cnt kk)) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (rw8D_extra cnt kk)) E) by (subst E; apply env_agree_refl).
clear HE.
assert (UK1 : U E (SOff 33 1) = kk + 1) by (apply (U_atom_off E 33 kk 1 E33); lia).
assert (UC : U E (SOff 32 0) = cnt) by (apply (U_atom E 32 cnt E32); lia).
unfold cfg_at.
(* one run per exit (the condition fact) and per entry pc *)
destruct (kk + 1 =? cnt) eqn:Heq;
[ pose proof (ENT rw8D_cL ltac:(unfold acond_ok, rw8D_cL; cbn [ac_c ac_a ac_b];
    rewrite branch_eq_U, UK1, UC; exact Heq)) as HS
| pose proof (ENT rw8D_cC ltac:(unfold acond_ok, rw8D_cC; cbn [ac_c ac_a ac_b];
    rewrite branch_ne_U, UK1, UC, Heq; reflexivity)) as HS ];
clear ENT; destruct Hpc as [-> | ->];
lazymatch goal with
| |- SRr _ _ (mkCfg (mkst _ (w64 ?p) _ _) _) (rts_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?pcs _ _ _) =>
  change (w64 p) with (Z_to_bv 64 p);
  let st := eval vm_compute in pcs in aj_run_to rw8_tblD_ok HS HJ st
end.
all: lazymatch goal with
| |- awr_ok _ _ _ _ _ _ _ _ _ =>
  (* the frame's 13 shadow bytes: its own shadow; the real frame's cells are read only *)
  change (ss_mem (rw8D_ss _ _)) with [rw8D_rR; rw8D_rS];
  apply awr_ok_cons_ro; [unfold rw8D_rR; cbn [YP09.r_wlo YP09.r_whi]; lia|];
  apply (rts_awr_ok_fsh _ _ _ _ _ _ _ _ _ _ 20%nat pos);
  [ reflexivity | rewrite U20, HFe; reflexivity | exact Hown
  | unfold rw8D_rS; cbn [YP09.r_wlo]; lia | unfold rw8D_rS; cbn [YP09.r_whi]; lia | apply awr_ok_nil ]
| |- _ =>
  apply SRr_ret; red;
  exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc);
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs (rw8D_extra cnt kk) (w_H W) _ HS HAE);
          vm_compute; reflexivity|];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|];
  split; [apply mo_le_refl; exact MTL|];
  split;
  [ (* every byte outside the 13 shadow bytes is kept *)
    intros a Ha Hn; apply (aview_eq_of rsegs); apply HFr; rewrite unsigned_lit_small by exact Ha;
    intros (r & Hin & Hr); change (ss_mem (rw8D_ss _ _)) with [rw8D_rR; rw8D_rS] in Hin;
    cbn [In] in Hin; destruct Hin as [<- | [<- | []]]; unfold rw8D_rR, rw8D_rS in Hr;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [rewrite U9 in Hr | rewrite U20 in Hr]; lia
  | split;
    [ (* a1 = k + 1 *)
      rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (11%bv : bv 5) HS);
      lazymatch type of HS with st_ok _ _ ?ssf _ =>
        let e := eval vm_compute in (sr_get (ss_regs ssf) (11%bv : bv 5)) in
        change (sr_get (ss_regs ssf) (11%bv : bv 5)) with e end;
      apply (rw8_den_off E 33 kk 1 E33); lia
    | (* the 13 shadow bytes hold 0xf8, from the final region based at s4 *)
      intros i Hi;
      lazymatch type of HS with st_ok _ _ ?ssf _ =>
        let rS := eval vm_compute in (nth_error (ss_mem ssf) 1) in
        lazymatch rS with Some ?r2 =>
          pose proof (rts_region_nth E ssf ms 1 r2 (w_H W) HS ltac:(vm_compute; reflexivity)) as HRS end end;
      rewrite <- Z.add_assoc; apply (rw8D_chunkf8 E);
      apply (rts_chunks E _ 20%nat _ _ _ _ _ _ HRS U20);
      assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/
        i = 10 \/ i = 11 \/ i = 12) by lia;
      repeat (destruct Hc as [Hc | Hc]; [subst i; cbn [In]; repeat (first [left; reflexivity | right]) |]);
      subst i; cbn [In]; repeat (first [left; reflexivity | right]) ] ]
end.
Qed.
End d.
End b.

Print Assumptions rw8_runD.
