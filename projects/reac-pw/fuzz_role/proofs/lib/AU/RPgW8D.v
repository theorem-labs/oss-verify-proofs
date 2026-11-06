(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 156 of its 180 lines of code are new or changed and 302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aHead.v at 876d0cb3d0d6; the plain run with
   frame-shadow stores of w6_head, here for reac-pw/fuzz_rate's last run of the walk piece W8 (the stores write 0xf8,
   the run ends at the pod loop's latch instead of a call, and the post is RtPgSteps.rts_post). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW8D.v at 8f1d7a0a9084 for the same unit's
   image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; the pcs, the cells (cnt at R+0x140, k at R+0x178)
   and the registers (s3 = the frame's shadow base) are image B's; the frame for locals is the class-4 frame (128
   shadow bytes) and the 13 shadow bytes are [66, 79); the run also sets s8 := -8; the prefix rw8_ becomes rbw8_ and
   RtPgSteps' rts_ becomes RtPgStepsB's rtsb_. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgBW8D.v, with its module paths, module names, addresses and numbers changed; 55 of its 177 lines of code are new or changed and 58 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aHead.v at 876d0cb3d0d6; the plain run with
   frame-shadow stores of w6_head, here for reac-pw/fuzz_rate's last run of the walk piece W8 (the stores write 0xf8,
   the run ends at the pod loop's latch instead of a call, and the post is RtPgSteps.rts_post). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW8D.v at 8f1d7a0a9084 for the same unit's
   image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; the pcs, the cells (cnt at R+0x140, k at R+0x178)
   and the registers (s3 = the frame's shadow base) are image B's; the frame for locals is the class-4 frame (128
   shadow bytes) and the 13 shadow bytes are [66, 79); the run also sets s8 := -8; the prefix rw8_ becomes rbw8_ and
   RtPgSteps' rts_ becomes RtPgStepsB's rtsb_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgBW8D.v at 6c65f5a5cf5c for reac-pw/fuzz_role's
   image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments lib/AU/Img0.v rsegs; the pcs and
   the cells (cnt at R+0x128, k at R+0x150) are role B's; the run sets s10 := -8 instead of s8; the prefix rbw8_
   becomes w8_ and RtPgStepsB's rtsb_ becomes RPgSteps' rl_. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the run lemma w8_runD of
   lib/AU/RPgW8Kit.v, the last run of the walk piece "write + record" of LLVMFuzzerTestOneInput (pod.h:433):
     0x81974  ld a1,0x150(s1)                   a1 := k (only after the record copy; else entered at 0x81978)
     0x81978  li a0,-8
     0x8197c .. 0x819b4  13 x sb a0,o(s3)       shadow_addr F + 66 .. 78 := 0xf8 (e62 goes out of scope)
     0x819ac  addiw a1,a1,1                     k + 1
     0x819b0  li s10,-8
     0x819b8  ld a0,0x128(s1)                   cnt
     0x819bc  bne a1,a0,0x80b54                 the pod loop's head C (k + 1 <> cnt)
     0x819c0  j 0x81ccc                         the params Struct's close CL (k + 1 = cnt)
   Proves no function (kind: segment lemma).
   HOW. One plain engine run (lib/Reusable/YCbq.v aj_run_to over w8_tblD) per entry pc and per exit, over two
   regions: the real frame's cells [R+0x128, R+0x158) based at the s1 atom (read only; the chunks at 0x128 and 0x150
   are cnt and k, the extra env slots 32 and 33), and the 13 shadow bytes [66, 79) of the frame for locals (4, pos)
   based at the s3 atom (write window: the frame's shadow, RPgSteps.rl_awr_ok_fsh). The latch is not decided by
   the atom ranges, so each exit's start state carries its condition fact (k + 1 <> cnt, or k + 1 = cnt). When the
   run enters at 0x81978, a1 is pinned to the k atom. No instrumented check is in the block. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgMem RPgSteps RPgW8Kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the entry state of the run ---- *)
(* env slot 32 = cnt (the cell R+0x128), slot 33 = k (the cell R+0x150) *)
Definition w8D_extra (cnt kk : Z) : list word := [w64 cnt; w64 kk].
Definition w8D_rR : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x128 0x158 0 0
   [YP09.mkChunk 0x128 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x150 (CVal 8 (SOff 33 0))].
Definition w8D_rS : YP09.region := YP09.mkRegion (Some 19%nat) 66 79 66 79 [].
(* the latch's two exits, as condition facts *)
Definition w8D_cC : acond := mkAC BC_NE (SOff 33 1) (SOff 32 0).
Definition w8D_cL : acond := mkAC BC_EQ (SOff 33 1) (SOff 32 0).
Definition w8D_facts (c : acond) : facts := mkFacts [(32%nat, mkAF 1 32 0); (33%nat, mkAF 0 31 0)] [c] [].
(* at 0x81978 a1 already holds k *)
Definition w8D_sr (pc0 : Z) : list sv :=
  if pc0 =? W8_T0 then sr_set sr_atoms (11%bv : bv 5) (SOff 33 0) else sr_atoms.
Definition w8D_ss (pc0 : Z) (c : acond) : sstate :=
  mkSS pc0 (w8D_sr pc0) [w8D_rR; w8D_rS] None (w8D_facts c).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* a one-byte chunk of value 0xf8 *)
Lemma w8D_chunkf8 : forall E H mem base o,
YP09.chunk_ok rsegs E (mrestrict H mem) base (YP09.mkChunk o (CVal 1 (SLit 18446744073709551608))) ->
aview rsegs H mem (base + o) = Some 0xf8.
Proof.
intros E H mem base o Hc. unfold aview. rewrite (w8_mbyte_chunk1 E _ base o _ Hc). cbn [option_map].
rewrite U_SLit. f_equal; vm_compute; reflexivity.
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

Lemma w8_runD : w8_runD_stmt B MT.
Proof using MTL LAWS.
unfold w8_runD_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pos cnt kk pc0
HJ (HR16 & HRs & HRe & HRlo & Hown & HFe & HFapp & HF32) Hpc H11 H2 H9 H19 Vcnt Vkk Hcnt Hkk.
pose proof w8_wx as Hwx. pose proof w8_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
unfold T_SEG_STK, ASTACK, kHighMemBeg in HRlo. unfold T_SEG_STK, ASTACK in HRs.
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (_ & _ & _ & Hfsh).
rewrite <- HFe in Hfsh. change (fs_frame_bytes 4 / 8) with 128 in Hfsh.
destruct (rl_fbounds F HF32 HFapp) as (HFlo & HFc & Hsa0 & Hsac & _ & _).
(* the frame's shadow lies below the high application memory, so below R *)
assert (HSB : shadow_addr F + 128 <= 0x10007fff8000).
{ pose proof ASAN_CEIL_range as (AC & _).
  assert (HF8 : F + 1024 <= 140737488355328) by (unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp; lia).
  assert (HF9 : F / 8 <= 17592186044288) by (apply Z.div_le_upper_bound; lia).
  unfold shadow_addr, SHADOW_OFF. lia. }
clear HAR.
(* the entry state's atoms *)
assert (U9 : bv_unsigned (ew (Ereg regs (w8D_extra cnt kk)) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (U19 : bv_unsigned (ew (Ereg regs (w8D_extra cnt kk)) 19) = shadow_addr F).
{ rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl), H19. unfold w64. apply unsigned_lit_small. lia. }
assert (E32 : ew (Ereg regs (w8D_extra cnt kk)) 32 = Z_to_bv 64 cnt)
  by exact (ew_Ereg_extra regs (w8D_extra cnt kk) 0).
assert (E33 : ew (Ereg regs (w8D_extra cnt kk)) 33 = Z_to_bv 64 kk)
  by exact (ew_Ereg_extra regs (w8D_extra cnt kk) 1).
(* the entry state, for either entry pc and either condition fact *)
assert (ENT : forall c, acond_ok (Ereg regs (w8D_extra cnt kk)) c ->
  st_ok rsegs (Ereg regs (w8D_extra cnt kk)) (w8D_ss pc0 c)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc0) memc (seg_rom rsegs)))).
{ intros c Hc. rewrite restrict_mkst_fx. unfold w8D_ss. apply (entry_st_ok_full rsegs).
  - unfold w8D_sr. destruct (pc0 =? W8_T0) eqn:Ht; [|apply regs_ok_Ereg].
    apply Z.eqb_eq in Ht.
    apply w8_regs_ok_override; [apply regs_ok_Ereg | apply w8_nz; vm_compute; intros X; discriminate X |].
    rewrite (H11 Ht). apply rl_den_atom; [exact E33 | lia].
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, w8D_rR.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val rsegs _ _ R 0x128 8 (SOff 32 0) cnt); [| cbn; lia | cbn; lia | exact Vcnt].
        apply rl_den_atom; [exact E32 | lia].
      * apply (chunk_ok_val rsegs _ _ R 0x150 8 (SOff 33 0) kk); [| cbn; lia | cbn; lia | exact Vkk].
        apply rl_den_atom; [exact E33 | lia].
    + unfold region_ok, w8D_rS.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U19.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable rsegs). exact (proj1 (Hfsh o ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; [exact I | exact I]].
    unfold extent_disjoint, w8D_rR, w8D_rS. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19.
    lia.
  - unfold facts_ok, w8D_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [split; [exact Hc | exact I] | exact I]].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, E33.
    rewrite !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    split; [repeat split; lia|]. split; [repeat split; lia | exact I]. }
remember (Ereg regs (w8D_extra cnt kk)) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (w8D_extra cnt kk)) E) by (subst E; apply env_agree_refl).
clear HE.
assert (UK1 : U E (SOff 33 1) = kk + 1) by (apply (U_atom_off E 33 kk 1 E33); lia).
assert (UC : U E (SOff 32 0) = cnt) by (apply (U_atom E 32 cnt E32); lia).
unfold cfg_at.
(* one run per exit (the condition fact) and per entry pc *)
destruct (kk + 1 =? cnt) eqn:Heq;
[ pose proof (ENT w8D_cL ltac:(unfold acond_ok, w8D_cL; cbn [ac_c ac_a ac_b];
    rewrite branch_eq_U, UK1, UC; exact Heq)) as HS
| pose proof (ENT w8D_cC ltac:(unfold acond_ok, w8D_cC; cbn [ac_c ac_a ac_b];
    rewrite branch_ne_U, UK1, UC, Heq; reflexivity)) as HS ];
clear ENT; destruct Hpc as [-> | ->];
lazymatch goal with
| |- SRr _ _ (mkCfg (mkst _ (w64 ?p) _ _) _) (rl_wpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?pcs _ _ _) =>
  change (w64 p) with (Z_to_bv 64 p);
  let st := eval vm_compute in pcs in aj_run_to w8_tblD_ok HS HJ st
end.
all: lazymatch goal with
| |- awr_ok _ _ _ _ _ _ _ _ _ =>
  (* the frame's 13 shadow bytes: its own shadow; the real frame's cells are read only *)
  change (ss_mem (w8D_ss _ _)) with [w8D_rR; w8D_rS];
  apply awr_ok_cons_ro; [unfold w8D_rR; cbn [YP09.r_wlo YP09.r_whi]; lia|];
  apply (rl_awr_ok_fsh _ _ _ _ _ _ _ _ _ _ 19%nat pos);
  [ reflexivity | rewrite U19, HFe; reflexivity | exact Hown
  | unfold w8D_rS; cbn [YP09.r_wlo]; lia | unfold w8D_rS; cbn [YP09.r_whi]; lia | apply awr_ok_nil ]
| |- _ =>
  apply SRr_ret; red;
  exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc);
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs (w8D_extra cnt kk) (w_H W) _ HS HAE);
          vm_compute; reflexivity|];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|];
  split; [apply mo_le_refl; exact MTL|];
  split;
  [ (* every byte outside the 13 shadow bytes is kept *)
    intros a Ha Hn; apply (aview_eq_of rsegs); apply HFr; rewrite unsigned_lit_small by exact Ha;
    intros (r & Hin & Hr); change (ss_mem (w8D_ss _ _)) with [w8D_rR; w8D_rS] in Hin;
    cbn [In] in Hin; destruct Hin as [<- | [<- | []]]; unfold w8D_rR, w8D_rS in Hr;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [rewrite U9 in Hr | rewrite U19 in Hr]; lia
  | split;
    [ (* a1 = k + 1 *)
      rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (11%bv : bv 5) HS);
      lazymatch type of HS with st_ok _ _ ?ssf _ =>
        let e := eval vm_compute in (sr_get (ss_regs ssf) (11%bv : bv 5)) in
        change (sr_get (ss_regs ssf) (11%bv : bv 5)) with e end;
      apply (w8_den_off E 33 kk 1 E33); lia
    | split;
      [ (* s10 = -8 *)
        rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (26%bv : bv 5) HS);
        lazymatch type of HS with st_ok _ _ ?ssf _ =>
          let e := eval vm_compute in (sr_get (ss_regs ssf) (26%bv : bv 5)) in
          change (sr_get (ss_regs ssf) (26%bv : bv 5)) with e end;
        first [ (apply bv_eq; vm_compute; reflexivity)
              | (rewrite denot_lit_U, U_SLit; apply bv_eq; vm_compute; reflexivity) ]
      | (* the 13 shadow bytes hold 0xf8, from the final region based at s3 *)
        intros i Hi;
        lazymatch type of HS with st_ok _ _ ?ssf _ =>
          let rS := eval vm_compute in (nth_error (ss_mem ssf) 1) in
          lazymatch rS with Some ?r2 =>
            pose proof (rl_region_nth E ssf ms 1 r2 (w_H W) HS ltac:(vm_compute; reflexivity)) as HRS end end;
        rewrite <- Z.add_assoc; apply (w8D_chunkf8 E);
        apply (rl_chunks E _ 19%nat _ _ _ _ _ _ HRS U19);
        assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/
          i = 10 \/ i = 11 \/ i = 12) by lia;
        repeat (destruct Hc as [Hc | Hc]; [subst i; cbn [In]; repeat (first [left; reflexivity | right]) |]);
        subst i; cbn [In]; repeat (first [left; reflexivity | right]) ] ] ]
end.
Qed.
End d.
End b.
