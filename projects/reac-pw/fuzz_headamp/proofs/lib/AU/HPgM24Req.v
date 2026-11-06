(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgM24F.v at 22d69e63401; image B's
   modules (lib/AU/Img0U, HPgImgB, HPgSeg, HPgSegM, HPgSteps) in place of image A's, image B's pcs (0x838e4 ..
   0x83900), registers (rc in s9 = x25, 3 max(rc, 0) in s10 = x26) and cut lists (hqu_cut_FIRST, hqu_cut_C6s,
   headamp_B_L67), names hq_ / hs_ / hf_ -> hqu_ / hsu_ / hbr_. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the request of the first
   block in LLVMFuzzerTestOneInput (0x80c40), fuzz_headamp.c:350 and fuzz.h:73, i.e. lib/AU/HPgSegM.v
   hqu_piece_M24_first_stmt (FIRST 0x838e4 -> C6 0x83900) at the concrete segments lib/AU/Img0U.v rsegs.
   Proves no function (kind: segment lemma).

   THE CODE
     0x838e4 sgtz a0,s9 / 0x838e8 slli a1,s9,1 / 0x838ec add a1,a1,s9      a0 = (rc > 0), a1 = 3 rc (s9 = rc)
     0x838f0 neg a0,a0 / 0x838f4 and s10,a0,a1                               s10 = 3 max(rc, 0)
     0x838f8 seqz a0,s10 / 0x838fc add a0,s10,a0                             a0 = s10 + (s10 == 0), the request
     0x83900 jal malloc                                                     the cut C6, not run here
   No load, no store and no instrumented check: the engine (lib/Reusable: st_ok, aj_run_to) runs the seven words
   from an entry state with every register an atom and no region (hbr_entry), so every byte and every register but
   a0, a1 and s10 is as at FIRST. The engine leaves a0 = hbr_a0 and s10 = hbr_s10 over the atom of s9; at FIRST
   s9 = rc with -1 <= rc <= cap <= 9 (hqu_start_M03: e_rc = ans_rc of the parse's answer, Pod/Headamp.v
   parse_props_total, Spec/HeadBytes.v answer_ok_parts), so hbr_vals closes both values by one case split on rc.
   The C6 cut (hqu_cut_C6s) is then the FIRST cut's journal, float state, frame shadow, out bytes and errno cell,
   with image B's list hi_L6 = headamp_B_L67 XRc3NZ: a0 = XRc3NZ, s10 = XRc3 and the registers and real-frame
   cells FIRST names. REGISTERS this file reads: s9 (x25); it writes a0, a1, s10 (x10, x11, x26). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the code table: the eight words 0x838e4 .. 0x83900 (the run stops at the `jal`, which it does not run) ---- *)
Definition HBR_PC0 : Z := 0x838e4.
Definition hbr_tbl : ctable := build_table rsegs HBR_PC0 8 TEmpty.
Lemma hbr_tbl_ok : table_ok rsegs hbr_tbl.
Proof. apply build_table_ok0. unfold HBR_PC0. lia. Qed.

(* ---- the entry state at FIRST: the registers as atoms, no region, no fact (at any float state) ---- *)
Definition hbr_ss : sstate := mkSS HBR_PC0 sr_atoms [] None (mkFacts [] [] []).
Lemma hbr_entry : forall (fx' : YK11.FPState) (W : world rsegs) regs memc,
@st_ok rsegs fx' (Ereg regs rt_extra) hbr_ss
  (restrict (w_H W) (@mkst fx' regs (Z_to_bv 64 HBR_PC0) memc (seg_rom rsegs))).
Proof.
intros fx' W regs memc. rewrite restrict_mkst_fx. unfold hbr_ss. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I.
Qed.

(* ---- the two values the run leaves, over the atom of s9 (the engine's own terms at 0x83900) ---- *)
Definition hbr_s10 : sv :=
  SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 25 0))) (SMd M_MUL (SOff 25 0) (SLit 3)).
Definition hbr_a0 : sv := SAlu ALU_ADD hbr_s10 (SAlu ALU_SLTU hbr_s10 (SLit 1)).
Lemma hbr_cases : forall z, -1 <= z <= 9 ->
z = -1 \/ z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9.
Proof. intros z Hz. lia. Qed.
Lemma hbr_vals : forall E z, -1 <= z <= 9 -> ew E 25 = Z_to_bv 64 z ->
sv_denot E hbr_a0 = w64 (3 * Z.max z 0 + (if 3 * Z.max z 0 =? 0 then 1 else 0)) /\
sv_denot E hbr_s10 = w64 (3 * Z.max z 0).
Proof.
intros E z Hz Ez. unfold hbr_a0, hbr_s10. cbn [sv_denot]. rewrite Ez.
destruct (hbr_cases z Hz) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
split; apply bv_eq; vm_compute; reflexivity.
Qed.

(* the side goals of a register the run did not write *)
Ltac hbr_rk :=
first
[ solve [vm_compute; let Hx := fresh "Hx" in intros Hx; discriminate Hx]
| solve [let Hx := fresh "Hx" in intros Hx; cbn [In] in Hx;
         repeat (destruct Hx as [Hx|Hx]; [apply (f_equal (@bv_unsigned 5)) in Hx; vm_compute in Hx; discriminate Hx|]);
         exact Hx] ].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Theorem hqu_B_piece_M24_first : hqu_piece_M24_first_stmt rsegs B MT.
Proof.
unfold hqu_piece_M24_first_stmt. intros cx POST r ev HS0 HC6.
unfold hqu_from_FIRST. intros fx2 ly2 S2 W2 regs2 mem2 md2 HF.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
(* the segment's start facts: the cap and the parse's answer *)
destruct HS0 as (HP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrc & _ & _).
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcap & _).
assert (Hrcb : -1 <= e_rc (x_e rsegs cx) <= 9).
{ unfold hqu_ans in Hrc.
  pose proof (Headamp.parse_props_total (hd_props (e_null (x_e rsegs cx)) (Model.buf r)) (e_cap (x_e rsegs cx))
    ltac:(lia)) as Hok.
  apply answer_ok_parts in Hok as (Hcase & _). rewrite Hrc.
  destruct Hcase as [(H1 & _)|(H1 & _)]; lia. }
(* the FIRST cut *)
destruct HF as (Hb3 & HL).
destruct Hb3 as (Hcore & Hfxk & Hfsh & _ & _ & _ & Hout & _ & Herr).
pose proof Hcore as (HJ & Hr234 & Hfr & Hperm & Hio & Hmo & Hmem).
unfold hsu_at_cx, hsu_at, hqu_L_frame in HL. cbn [app] in HL.
rewrite !Forall_cons_iff in HL.
destruct HL as (P8 & P9 & P19 & P27 & P20 & P21 & P22 & P25 & Q18 & Q140 & Q148 & Q150 & Q158 & _).
cbn [fst snd hd_at hd_xv] in P8, P9, P19, P27, P20, P21, P22, P25, Q18, Q140, Q148, Q150, Q158.
(* the run: 0x838e4 .. 0x838fc, stop at C6 *)
remember (Ereg regs2 rt_extra) as E eqn:HE.
pose proof (hbr_entry fx2 W2 regs2 mem2) as HS. rewrite <- HE in HS.
assert (HAE : env_agree 32 (Ereg regs2 rt_extra) E) by (subst E; apply env_agree_refl).
assert (E25 : ew E 25 = Z_to_bv 64 (e_rc (x_e rsegs cx)))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 25 (Z_to_bv 5 25) eq_refl); exact P25).
clear HE.
unfold cfg_at. change (w64 HQU_FIRST) with (Z_to_bv 64 HBR_PC0).
aj_run_to hbr_tbl_ok HS HJ HQU_C6.
{ apply awr_ok_nil. }
(* no byte written; every register but a0, a1, s10 its own atom; a0 and s10 the request and 3 max(rc, 0) *)
assert (Em : ms_mem ms = mem2).
{ apply functional_extensionality. intros x. apply HF. intros (rg & Hrg & _). exact Hrg. }
assert (RK : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [Z_to_bv 5 10; Z_to_bv 5 11; Z_to_bv 5 26] ->
  getr (ms_regs ms) rr = getr regs2 rr).
{ eapply (regs_kept_of_st_ok rsegs _ _ ms regs2 rt_extra (w_H W2) _ HS HAE). vm_compute. reflexivity. }
assert (HV : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (hd_xv (x_e rsegs cx) XRc3NZ) /\
             getr (ms_regs ms) (Z_to_bv 5 26) = w64 (hd_xv (x_e rsegs cx) XRc3)).
{ rewrite !(st_ok_restrict_reg rsegs (w_H W2) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ssf _ =>
    replace (sr_get (ss_regs ssf) (Z_to_bv 5 10)) with hbr_a0 by (vm_compute; reflexivity);
    replace (sr_get (ss_regs ssf) (Z_to_bv 5 26)) with hbr_s10 by (vm_compute; reflexivity) end.
  cbn [hd_xv]. exact (hbr_vals E (e_rc (x_e rsegs cx)) Hrcb E25). }
(* the C6 cut *)
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
rewrite Em. rewrite Em in HJ.
apply (HC6 fx2 ly2 S2 W2 (ms_regs ms) mem2 _).
split; [|split; [exact Hfxk|split; [|split; [exact Hfsh | split; [exact Hout | exact Herr]]]]].
- split; [exact HJ|].
  split; [intros rr Hrr; rewrite <- (Hr234 rr Hrr); apply RK; destruct Hrr as [->|[->| ->]]; hbr_rk|].
  split; [exact Hfr|]. split; [exact Hperm|].
  split; [eapply same_io_trans; [exact Hio|];
          let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
  split; [exact Hmo | exact Hmem].
- unfold hd_cut. cbn [hi_L6 headamp_himg_B]. unfold headamp_B_L67.
  repeat (apply Forall_cons;
    [cbn [fst snd hd_at hd_xv];
     first [ exact (proj1 HV) | exact (proj2 HV)
           | (rewrite RK by hbr_rk; rewrite ?Z.add_0_r; assumption)
           | (rewrite ?Z.add_0_r; assumption) ] |]).
  apply Forall_nil.
Qed.
(* inside the Section: the kernel's axioms only (the piece takes no Section hypothesis) *)
Print Assumptions hqu_B_piece_M24_first.
End b.
Print Assumptions hqu_B_piece_M24_first.
