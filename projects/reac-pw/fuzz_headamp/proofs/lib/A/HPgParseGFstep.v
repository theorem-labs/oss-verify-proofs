(* reac-pw/fuzz_headamp: a step that changes only the float registers, between two engine runs (both images). The
   engine's st_ok holds the float registers and the status word of its own float state equal to the machine's, so
   across `fmv.d.x` the symbolic state is the same at the next pc under the new float state; the step itself is
   lib/A/HPgParseFP.v's hfp_tw_fmv_d_x, taken by SRr_step (the model kept up to same_but_materialized).
   Proves no function (kind: helper lemmas for both images' walks). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgParseFP.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section g. Context {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Hypothesis Hwx : wx_segs_nowrap segs.

(* the engine's state after a step that wrote only float registers: the same symbolic state at pc + 4 *)
Lemma hgf_st_ok_freg : forall (F F' : bvmap 5 word) (fc : bv 32) E ss (H : word -> bool) regs mem,
st_ok (fx := mkFP F fc) segs E ss (restrict H (@mkst (mkFP F fc) regs (Z_to_bv 64 (ss_pc ss)) mem (seg_rom segs))) ->
st_ok (fx := mkFP F' fc) segs E (setpc ss (ss_pc ss + 4))
  (restrict H (@mkst (mkFP F' fc) regs (Z_to_bv 64 (ss_pc ss + 4)) mem (seg_rom segs))).
Proof.
intros F F' fc E ss H regs mem (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
unfold st_ok, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts restrict mkst
  ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem fp_regs fp_csr] in *.
do 8 (split; [first [reflexivity | assumption] |]). assumption.
Qed.

(* SRr through `fmv.d.x rd,rs` at the literal pc p *)
Lemma hgf_SRr_fmv_d_x : forall (F : bvmap 5 word) (fc : bv 32) W regs p mem md Q wz (rd rs : bv 5),
clookup tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
decode_any (Z_to_bv 32 wz) = Some (Fmv FMV_F_X FMT_D rd rs, 4%Z) ->
(forall md', same_but_materialized md md' ->
 SRr segs W (mkCfg (@mkst (mkFP (bvmap_set rd (getr regs rs) F) fc) regs (Z_to_bv 64 (p + 4)) mem (seg_rom segs)) md')
   Q) ->
SRr segs W (mkCfg (@mkst (mkFP F fc) regs (Z_to_bv 64 p) mem (seg_rom segs)) md) Q.
Proof.
intros F fc W regs p mem md Q wz rd rs Hl He Hd Hk.
apply (SRr_step segs Hwx W _
  (restrict (w_H W) (@mkst (mkFP (bvmap_set rd (getr regs rs) F) fc) regs (Z_to_bv 64 (p + 4)) mem (seg_rom segs)))
  md Q).
- reflexivity.
- rewrite !restrict_mkst_fx.
  exact (hfp_tw_fmv_d_x segs tbl tbl_ok (mkFP F fc) regs (mrestrict (w_H W) mem) (seg_rom segs) p (p + 4) wz rd rs
    (getr regs rs) Hl He Hd eq_refl eq_refl).
- intros md' Hs. rewrite restrict_mkst_fx, unrestrict_mkst_mrestrict. exact (Hk md' Hs).
Qed.
End g.

Print Assumptions hgf_st_ok_freg.
Print Assumptions hgf_SRr_fmv_d_x.
