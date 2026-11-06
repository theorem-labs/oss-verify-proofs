(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 666 of its 732 lines of code are new or changed and 1212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntHobsS3.v, with its module names changed; 190 of its 227 lines of code are new or changed and 695 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0p YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC1h YC1i YC81 YCjr YCj1 YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut
DiscoArm3JsonC2Defs DiscoArm3JsonC2Mod DiscoArm3JsonK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition c2r_ne : acond := mkAC BC_NE (SOff 10 0) (SLit 0).
Definition c2r_eq : acond := mkAC BC_EQ (SOff 10 0) (SLit 0).
Definition c2r_a0 : acond := mkAC BC_EQ (SOff 22 0) (SLit 0).
Definition c2r_fa : list (nat * afact) := [(22%nat, mkAF 0 0 0)].
Definition c2r_reg (off sh : Z) : smem :=
  [YP09.mkRegion (Some 9%nat) off (off + 8) 0 0 [YP09.mkChunk off (CVal 8 (SOff 23 sh))]].
Definition c2r_rs (kb : nat) : smem :=
  match kb with
  | 1%nat => c2r_reg 408 24 | 2%nat => c2r_reg 368 48 | 3%nat => c2r_reg 360 72
  | 4%nat => c2r_reg 328 96 | 5%nat => c2r_reg 296 120 | _ => []
  end.
Definition c2r_ss (kb : nat) (res : Z) : sstate :=
  mkSS (C2_RET kb) sr_atoms (c2r_rs kb) None
    (mkFacts c2r_fa [if res =? 0 then c2r_eq else c2r_ne; c2r_a0] []).
Definition c2r_span : Z * Z := (SB, SB + 2 ^ 44 - 1).

Ltac c2r_side :=
  first [ cbn [sh_obls]; apply Forall_nil
        | lazymatch goal with |- awr_ok ?E ?rs _ _ _ _ _ _ _ =>
            intros a Ha; exfalso; exact (jk_nowin E rs a ltac:(vm_compute; reflexivity) Ha) end ].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma c2r_hs : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) mem (kb : nat) (res dA jc : Z),
  (kb < 6)%nat -> res = 0 \/ res = 1 ->
  getr regs 9 = w64 dA -> getr regs 23 = w64 jc -> getr regs 10 = w64 res -> getr regs 22 = w64 0 ->
  0 <= dA -> dA + 472 <= 2 ^ 64 -> 0 <= jc -> jc + 120 < 2 ^ 64 ->
  val_mem SEGS (rd W mem) (dA + 408) 8 (jc + 24) ->
  val_mem SEGS (rd W mem) (dA + 368) 8 (jc + 48) ->
  val_mem SEGS (rd W mem) (dA + 360) 8 (jc + 72) ->
  val_mem SEGS (rd W mem) (dA + 328) 8 (jc + 96) ->
  val_mem SEGS (rd W mem) (dA + 296) 8 (jc + 120) ->
  st_ok_pi (fx := fq) SEGS VAL (Eimg (Ereg regs [])) (c2r_ss kb res)
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + C2_RET kb)) mem (YK11.seg_rom SEGS))).
Proof.
  intros fq W regs mem kb res dA jc Hkb Hres R9 R23 R10 R22 HA0 HA1 HJ0 HJ1 V1 V2 V3 V4 V5.
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs r)
    by (intros nn r Hr; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (B9 : bv_unsigned (ew E 9) = dA).
  { rewrite (EE 9%nat 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
  assert (D23 : forall c, 0 <= jc + c < 2 ^ 64 -> sv_denot E (SOff 23 c) = Z_to_bv 64 (jc + c)).
  { intros c Hc. rewrite (denot_lit_U E (SOff 23 c)). f_equal.
    apply (U_atom_off E 23 jc c); [rewrite (EE 23%nat 23%bv eq_refl); exact R23 | lia | lia]. }
  assert (U10 : U E (SOff 10 0) = res).
  { apply (U_atom E 10 res); [rewrite (EE 10%nat 10%bv eq_refl); exact R10 | lia]. }
  assert (U22 : U E (SOff 22 0) = 0).
  { apply (U_atom E 22 0); [rewrite (EE 22%nat 22%bv eq_refl); exact R22 | lia]. }
  assert (HG : facts_ok E (mkFacts c2r_fa [if res =? 0 then c2r_eq else c2r_ne; c2r_a0] [])).
  { unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split; [|exact I]].
    - unfold c2r_fa. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite (EE 22%nat 22%bv eq_refl), R22. unfold w64. rewrite unsigned_lit_small by lia.
      rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
    - cbn [conds_ok]. split; [|split; [|exact I]].
      + destruct Hres as [-> | ->]; cbn [Z.eqb]; unfold acond_ok, c2r_eq, c2r_ne; cbn [ac_c ac_a ac_b].
        * rewrite branch_eq_U, U_lit by lia. rewrite U10. reflexivity.
        * rewrite branch_ne_U, U_lit by lia. rewrite U10. reflexivity.
      + unfold acond_ok, c2r_a0. cbn [ac_c ac_a ac_b].
        rewrite branch_eq_U, U_lit by lia. rewrite U22. reflexivity. }
  unfold c2r_ss. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - destruct kb as [|[|[|[|[|[|kb]]]]]]; [vm_compute; reflexivity ..| lia].
  - destruct kb as [|[|[|[|[|[|kb]]]]]]; cbn [c2r_rs c2r_reg]; try apply Forall_nil; try lia;
      (apply Forall_cons; [|apply Forall_nil]); unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite B9;
      (split; [lia|]); (split; [lia|]); (split; [intros o Ho; lia|]);
      (apply Forall_cons; [|apply Forall_nil]).
    + apply (chunk_ok_val SEGS E _ dA 408 8 (SOff 23 24) (jc + 24)); [apply D23; lia | cbn; lia | cbn; lia | exact V1].
    + apply (chunk_ok_val SEGS E _ dA 368 8 (SOff 23 48) (jc + 48)); [apply D23; lia | cbn; lia | cbn; lia | exact V2].
    + apply (chunk_ok_val SEGS E _ dA 360 8 (SOff 23 72) (jc + 72)); [apply D23; lia | cbn; lia | cbn; lia | exact V3].
    + apply (chunk_ok_val SEGS E _ dA 328 8 (SOff 23 96) (jc + 96)); [apply D23; lia | cbn; lia | cbn; lia | exact V4].
    + apply (chunk_ok_val SEGS E _ dA 296 8 (SOff 23 120) (jc + 120)); [apply D23; lia | cbn; lia | cbn; lia | exact V5].
  - destruct kb as [|[|[|[|[|[|kb]]]]]]; cbn [c2r_rs c2r_reg pairwise_disjoint all_disjoint]; tauto.
  - exact HG.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.

Theorem jc2_hopR : jc2_hopR_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros P kb res W c Hkb HIN.
unfold jc2_ret, jc2_at, jcut, d_arm_at_pf, d_at in HIN.
destruct HIN as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc0 & Hcf & Hfrm0 & HBASE & HJ & HFR & Hk & Hnev &
  HMO & Hacc & Hi & Hn & Hnow & HRL & (R26 & R24 & R25 & HR & R10) & (HSP1 & HTAB & HBUF & (HX & HKB & HRES)) &
  HSP0 & HBODY).
subst c.
pose proof HR as (R21 & R22 & R23).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs19 & Rs18 & Rs20 & Rs27).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJSL & _).
pose proof HJSL as (J408 & J368 & J360 & J328 & J296 & J352).
pose proof (jc2_count P W mem3 HX) as Hcnt.
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K (p_cx P) ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS (p_cx P) ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & _).
pose proof alloc_ceiling_value as Hceil0.
pose proof (d_A_range (p_cx P) ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
assert (Hjc : 0 <= jcur (p_cx P) (p_count P) /\ jcur (p_cx P) (p_count P) + 120 < 2 ^ 64).
{ unfold jcur, d_obj. cbn [dobj_off]. lia. }
assert (Hm8 : jcur (p_cx P) (p_count P) mod 8 = 0).
{ unfold jcur, d_obj. cbn [dobj_off].
  pose proof (Z.div_mod (d_FB (p_cx P)) 32 ltac:(lia)) as DF. rewrite GF32 in DF.
  replace (d_FB (p_cx P) + 240 + 144 * p_count P)
    with ((4 * (d_FB (p_cx P) / 32) + 30 + 18 * p_count P) * 8) by lia.
  apply Z_mod_mult. }
assert (R22z : getr regs 22 = w64 0) by (rewrite R22, Hm8; reflexivity).
assert (Hres : res = 0 \/ res = 1) by (destruct HRES as [(-> & _) | (-> & _)]; [right | left]; reflexivity).
pose proof (c2r_hs fq W regs mem3 kb res (d_A (p_cx P)) (jcur (p_cx P) (p_count P)) Hkb Hres Rs1 R23 R10 R22z
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) J408 J368 J360 J328 J296) as HS.
remember (Eimg (Ereg regs [])) as E0 eqn:HE0.
assert (HEI : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
assert (EE0 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs r)
  by (intros nn r Hr; rewrite HE0; apply ew_Eimg_Ereg_nat; exact Hr).
assert (SHOK : sh_ok SEGS (SOff 19 0) (@nil shent) E0 (rd W mem3)) by constructor.
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
unfold cfg_at, w64.
destruct HRES as [(-> & HJT) | (-> & HJF)]; destruct kb as [|[|[|[|[|[|kb]]]]]]; try lia.
1-6: (paj_run_to_tok RUNTO HS HJ SHOK c2r_span C2_M; try c2r_side).
7-11: (paj_run_tok RUN HS HJ SHOK c2r_span; try c2r_side).
12: (paj_run_to_tok RUNTO HS HJ SHOK c2r_span SLOT_OFF; try c2r_side).
all: assert (Emem : ms_mem ms = mem3) by (apply functional_extensionality; intros x; apply HF;
  apply (jk_nowin _ _ (bv_unsigned x)); vm_compute; reflexivity).
all: rewrite Emem in HJ.
all: prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (8%bv : bv 5) Q8;
  prreg HS (9%bv : bv 5) Q9; prreg HS (18%bv : bv 5) Q18; prreg HS (19%bv : bv 5) Q19; prreg HS (20%bv : bv 5) Q20.
all: prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22; prreg HS (23%bv : bv 5) Q23;
  prreg HS (24%bv : bv 5) Q24; prreg HS (25%bv : bv 5) Q25; prreg HS (26%bv : bv 5) Q26;
  prreg HS (27%bv : bv 5) Q27.
all: rewrite (EE0 2%nat 2%bv eq_refl) in Q2; rewrite (EE0 3%nat 3%bv eq_refl) in Q3;
  rewrite (EE0 4%nat 4%bv eq_refl) in Q4; rewrite (EE0 8%nat 8%bv eq_refl) in Q8;
  rewrite (EE0 9%nat 9%bv eq_refl) in Q9; rewrite (EE0 18%nat 18%bv eq_refl) in Q18;
  rewrite (EE0 19%nat 19%bv eq_refl) in Q19; rewrite (EE0 20%nat 20%bv eq_refl) in Q20.
all: rewrite (EE0 21%nat 21%bv eq_refl) in Q21; rewrite (EE0 22%nat 22%bv eq_refl) in Q22;
  rewrite (EE0 23%nat 23%bv eq_refl) in Q23; rewrite (EE0 24%nat 24%bv eq_refl) in Q24;
  rewrite (EE0 25%nat 25%bv eq_refl) in Q25; rewrite (EE0 26%nat 26%bv eq_refl) in Q26;
  rewrite (EE0 27%nat 27%bv eq_refl) in Q27.
all: prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
  prreg HS (12%bv : bv 5) Q12.
all: pmkst HS; rewrite Emem; apply SRr_ret.
1-6: left; unfold jc2_mat, jc2_at, jcut, d_arm_at_pf, d_at.
7-11: right; left; split; [lia|]; unfold jc2_call, jc2_at, jcut, d_arm_at_pf, d_at.
12: right; right; unfold jc2_out, jslot_in, jcut, d_arm_at_pf, d_at.
all: split; [exact HFROM|].
all: exists fq, ly3, S3, (ms_regs ms), mem3, (with_vm_backing (m_vm_lazy md3) mat md3), k, acc0.
all: split; [try unfold cfg_at; try unfold w64;
  first [reflexivity | rewrite pa_sigma_jtok_is; reflexivity]|].
all: split; [exact Hfrm0|]; split; [exact HBASE|]; split; [exact HJ|]; split; [exact HFR|]; split; [exact Hk|];
  split; [exact Hnev|];
  split; [exact HMO|]; split; [exact Hacc|]; split; [exact Hi|]; split; [exact Hn|]; split; [exact Hnow|].
all: split; [unfold d_rL, spZ; rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q20, Q27; exact HRL|].
12: pose proof (jc2_kb_end P (jc2_kb_step P 5 Hkb HKB HJF)) as Hnone.
12: pose proof (jc2_none P W mem3 HX Hnone) as Hc2.
12: pose proof (jc2_ws P W mem3 HX) as HWS.
12: pose proof (jc2_c2_ok P W mem3 HX) as (Hl6 & HFA6).
12: pose proof HX as (HFIN & Hip & Hc0 & Hlacc & _ & _ & _ & HCONT & _ & _ & _ & _ & HMEM & _).
12: rewrite HWS in HCONT; rewrite <- Hc2 in HMEM.
12: split; [split; [rewrite Q26; exact R26|]; split; [rewrite Q24; exact R24|];
      split; [rewrite Q25; exact R25|];
      split; [rewrite Q21; exact R21|]; split; [rewrite Q22; exact R22|]; rewrite Q23; exact R23|];
    split; [split; [exact HSP1|]; split; [exact HTAB|]; split; [exact HBUF|];
      split; [exact HFIN|]; split; [exact Hip|]; split; [exact Hc0|]; split; [exact Hlacc|];
      split; [exact HCONT|]; split; [exact Hl6|]; split; [exact HFA6|]; split; [exact HMEM|]; exact HJSL|];
    split; [exact HSP0 | exact HBODY].
7-11: split; [split; [rewrite Q26; exact R26|]; split; [rewrite Q24; exact R24|];
        split; [rewrite Q25; exact R25|];
        split; [unfold jc2_R; split; [rewrite Q21; exact R21|]; split; [rewrite Q22; exact R22|];
                rewrite Q23; exact R23|];
        split; [rewrite Q1; reflexivity|];
        split; [rewrite Q10, (EE0 9%nat 9%bv eq_refl), Rs1; unfold w64; rewrite unsigned_lit_small by lia;
                reflexivity|];
        split; [rewrite Q11; reflexivity|];
        rewrite Q12, HE0, Eimg_img by (unfold A_TEXT, A_LIM; lia); reflexivity|];
      split; [split; [exact HSP1|]; split; [exact HTAB|]; split; [exact HBUF|];
        split; [exact HX | apply jc2_kb_step; assumption]|];
      split; [exact HSP0 | exact HBODY].
all: split; [split; [rewrite Q26; exact R26|]; split; [rewrite Q24; exact R24|];
        split; [rewrite Q25; exact R25|];
        split; [unfold jc2_R; split; [rewrite Q21; exact R21|]; split; [rewrite Q22; exact R22|];
                rewrite Q23; exact R23|];
        rewrite ?(EE0 23%nat 23%bv eq_refl) in Q10;
        rewrite ?R23 in Q10; unfold w64 in Q10 |- *;
        rewrite ?unsigned_lit_small in Q10 by lia;
        rewrite Q10; unfold p_slot; f_equal; lia|];
      split; [split; [exact HSP1|]; split; [exact HTAB|]; split; [exact HBUF|];
        split; [exact HX | apply jc2_kb_hit; assumption]|];
      split; [exact HSP0 | exact HBODY].
Qed.

End h.
End f.
End d.
