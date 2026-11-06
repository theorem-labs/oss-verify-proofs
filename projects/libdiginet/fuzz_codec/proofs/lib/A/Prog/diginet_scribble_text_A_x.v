(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run / keep / branch / leaf tactics, kept_run and same_io_wvb are the text of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgSlots.v:123-188 (made there from proofs/libreac/fuzz_knock/lib/A/APgStep.v,
   origin/ossv/recipes 6ebe35ba632), the stack-slot write tactics that of QPgCheck.v:52-69, the entry regions those of
   QPgRt.v:61-65 / 193-243, the shadow entry that of proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec.v:354-370
   (origin/ossv/recipes 4b6f0df50aa7), cw_U_sx32_eqb that of proofs/libreac/fuzz_knock/lib/A/APgStep.v:54-68
   (U_sx32_eqb, origin/ossv/recipes 4b6f0df50aa7), cw_join_win that of proofs/reac-pw/fuzz_qdisc/lib/A/QPgLoop0.v:169-196
   (ra_join_win, a working branch b0f706c04a19), cw_bcmp_at that of lib/Reusable/YCbq.v:2262-2310 (aj_bcmp_at) with
   the wrapper's same_but_materialized kept in its post, cw_st_ok_at that of lib/Reusable/YI04.v:342-356 (entry_st_ok_full)
   with the env apart from the registers, renamed with the prefix cw_ and moved to libdiginet/fuzz_codec's ASan
   build (image A); the leaf ends in lib/A/Prog/CPgBase.v's cdc_post, whose memory clause is CodecCJ's tcj_kept. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalk.v, with its module paths and module names changed; 127 of its 171 lines of code are new or changed and 589 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/diginet_scribble_text_B_x.v, with its module paths, module names and numbers changed; 16 of its 146 lines of code are new or changed and 41 lines of the source are left out. *)
(* diginet_scribble_text in image A (fuzz_codec.asan, 0x85cc4): the segment X of diginet_scribble_text_A_inv.v --
   from the return 0x85df4 to the `ret` at 0x85e04 and on to the contract's post (sc_seg_X).

   The code: 0x85df4 mv a0,s0; 0x85df8 ld ra,8(sp); 0x85dfc ld s0,0(sp); 0x85e00 addi sp,sp,16; 0x85e04 ret.
   One run, which writes nothing, then CPgWalk's cw_leaf.

   The symbolic state at 0x85df4 is built over the ENTRY registers (atoms 0..31), so that the two restores give the
   leaf's register clause: atom 33 + i holds the boundary value of register i; gp, tp, s1..s11 keep their entry
   atoms (sc_common), sp is entry atom 2 - 16, and the frame holds the entry s0 at -16 and the entry ra at -8. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import diginet_scribble_text_A_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at 0x85df4 --------------------------------------------------------------------------- *)
(* The boundary values of the 32 registers; the atoms 33 .. 64 hold them. *)
Definition sx_regs32 (rg : bvmap 5 word) : list Z :=
[bv_unsigned (getr rg (0%bv)); bv_unsigned (getr rg (1%bv)); bv_unsigned (getr rg (2%bv));
 bv_unsigned (getr rg (3%bv)); bv_unsigned (getr rg (4%bv)); bv_unsigned (getr rg (5%bv));
 bv_unsigned (getr rg (6%bv)); bv_unsigned (getr rg (7%bv)); bv_unsigned (getr rg (8%bv));
 bv_unsigned (getr rg (9%bv)); bv_unsigned (getr rg (10%bv)); bv_unsigned (getr rg (11%bv));
 bv_unsigned (getr rg (12%bv)); bv_unsigned (getr rg (13%bv)); bv_unsigned (getr rg (14%bv));
 bv_unsigned (getr rg (15%bv)); bv_unsigned (getr rg (16%bv)); bv_unsigned (getr rg (17%bv));
 bv_unsigned (getr rg (18%bv)); bv_unsigned (getr rg (19%bv)); bv_unsigned (getr rg (20%bv));
 bv_unsigned (getr rg (21%bv)); bv_unsigned (getr rg (22%bv)); bv_unsigned (getr rg (23%bv));
 bv_unsigned (getr rg (24%bv)); bv_unsigned (getr rg (25%bv)); bv_unsigned (getr rg (26%bv));
 bv_unsigned (getr rg (27%bv)); bv_unsigned (getr rg (28%bv)); bv_unsigned (getr rg (29%bv));
 bv_unsigned (getr rg (30%bv)); bv_unsigned (getr rg (31%bv))].
(* x0; gp, tp, s1..s11 their entry atoms; sp the entry atom 2 - 16; every other register (ra too: the runtime call
   writes it) its atom 33 + i. *)
Definition sx_sr : list sv :=
[SLit 0; SOff 34 0; SOff 2 (-16); SOff 3 0; SOff 4 0; SOff 38 0; SOff 39 0; SOff 40 0;
 SOff 41 0; SOff 9 0; SOff 43 0; SOff 44 0; SOff 45 0; SOff 46 0; SOff 47 0; SOff 48 0;
 SOff 49 0; SOff 50 0; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0;
 SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 61 0; SOff 62 0; SOff 63 0; SOff 64 0].
(* The frame [sp - 16, sp), read only: the entry s0 at -16, the entry ra at -8. *)
Definition sx_rsave : YP09.region := YP09.mkRegion (Some 2%nat) (-16) 0 0 0
  [YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition sx_ss0 : sstate := mkSS PC_X sx_sr [sx_rsave] None (mkFacts cw_atoms [] []).

(* one case of regs_ok at the start state; rg0 is the entry register file *)
Ltac sx_reg_case rg0 :=
lazymatch goal with |- _ = sv_denot _ (sr_get ?sr ?r2) =>
  let v := eval vm_compute in (sr_get sr r2) in change (sr_get sr r2) with v end;
first
[ cbn [sv_denot]; exact (getr_zero _)
| rewrite sv_denot_SOff0;
  first
  [ lazymatch goal with |- _ = ew _ ?n =>
      let j := eval vm_compute in (n - 33)%nat in change n with (33 + j)%nat end;
    rewrite cw_ew_x; cbn [nth sx_regs32]; rewrite Z_to_bv_bv_unsigned; reflexivity
  | lazymatch goal with |- getr _ ?r = ew _ ?n => rewrite (cw_ew_reg rg0 _ n r eq_refl) end;
    first [assumption | match goal with H : getr _ _ = getr _ _ |- _ => exact H end] ]
| lazymatch goal with R : getr _ _ = w64 (_ - 16) |- getr _ _ = _ => etransitivity; [exact R|] end;
  rewrite denot_lit_U;
  lazymatch goal with |- _ = Z_to_bv 64 (U ?Ev _) =>
    rewrite (cw_U_offx Ev 2 (spZ rg0) (-16)
      ltac:(rewrite (cw_ew_reg rg0 _ 2 (2%bv) eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned)
      ltac:(unfold spZ; apply sc_u64)) end;
  unfold w64; rewrite Z.mod_small by lia; f_equal; lia ].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem sx_holds : sc_seg_X B MT.
Proof.
unfold sc_seg_X. intros g W2 c2 Hpre Hcut.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hcut as (-> & regs2 & mem2 & md2 & Hc2 & HJ & Hio & HC & HPX).
destruct (sc_stack B g Hpre) as (Hceil & H47 & H46 & Hal & Hwin & Hsp0 & Hprs).
destruct (sc_out B g Hpre) as (Ho0 & Hon & Hn & Hoff & HTD & HTW & _ & _ & Hamo & _).
pose proof (sc_amem47 (sg_o g) (sg_n g) ltac:(lia) ltac:(lia) Hamo) as Ho47.
pose proof Hpre as (HE & _).
pose proof HE as (HJ0 & Hra & Hra4 & Hgp & Htp & _).
destruct HC as (HK & R2 & Vra & Vs0 & KE & KP).
repeat (apply Forall_cons_iff in HK as (? & HK)). cbv beta in *.
unfold sg_sp in *. unfold T_scribble_text, ESTACK in *.
(* ---- the start state ---- *)
assert (E2 : ew (Ereg (sg_regs g) (cw_extra (sx_regs32 regs2))) 2 = getr (sg_regs g) (2%bv))
  by (apply (cw_ew_reg (sg_regs g) (sx_regs32 regs2) 2%nat (2%bv)); reflexivity).
assert (U2 : bv_unsigned (ew (Ereg (sg_regs g) (cw_extra (sx_regs32 regs2))) 2) = spZ (sg_regs g)) by (rewrite E2; reflexivity).
assert (HS : st_ok tfibsegs (Ereg (sg_regs g) (cw_extra (sx_regs32 regs2))) sx_ss0
  (restrict (w_H (sg_W g)) (mkst regs2 (Z_to_bv 64 PC_X) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold sx_ss0. apply cw_st_ok_at.
  - apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [sx_reg_case (sg_regs g) | ]). destruct Hr.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, sx_rsave.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val tfibsegs _ _ (spZ (sg_regs g)) (-16) 8 (SOff 8 0) (bv_unsigned (getr (sg_regs g) (8%bv))));
      [rewrite sv_denot_SOff0, (cw_ew_reg (sg_regs g) (sx_regs32 regs2) 8%nat (8%bv) eq_refl);
       symmetry; apply Z_to_bv_bv_unsigned
      | change (8 * Z.of_N 8) with 64; apply sc_u64 | cbn; lia |].
      replace (spZ (sg_regs g) + -16) with (spZ (sg_regs g) - 16) by lia. exact Vs0.
    + apply (chunk_ok_val tfibsegs _ _ (spZ (sg_regs g)) (-8) 8 (SOff 1 0) (raZ (sg_regs g)));
      [rewrite sv_denot_SOff0, (cw_ew_reg (sg_regs g) (sx_regs32 regs2) 1%nat (1%bv) eq_refl);
       symmetry; apply Z_to_bv_bv_unsigned
      | change (8 * Z.of_N 8) with 64; apply sc_u64 | cbn; lia |].
      replace (spZ (sg_regs g) + -8) with (spZ (sg_regs g) - 8) by lia. exact Vra.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [|split; exact I]. cbn [f_atoms cw_atoms app atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, cw_ew_SB, unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
    unfold SB. repeat split; first [exact I | lia]. }
assert (HAE : env_agree 32 (Ereg (sg_regs g) (cw_extra (sx_regs32 regs2))) (Ereg (sg_regs g) (cw_extra (sx_regs32 regs2)))) by apply env_agree_refl.
assert (E1 : ew (Ereg (sg_regs g) (cw_extra (sx_regs32 regs2))) 1 = getr (sg_regs g) (1%bv))
  by (apply (cw_ew_reg (sg_regs g) (sx_regs32 regs2) 1%nat (1%bv)); reflexivity).
assert (B2 : bv_unsigned (ew (Ereg (sg_regs g) (cw_extra (sx_regs32 regs2))) 2) = spZ (sg_regs g)) by exact U2.
assert (SHOK : sh_ok tfibsegs CW_Bx [] (Ereg (sg_regs g) (cw_extra (sx_regs32 regs2))) (mrestrict (w_H (sg_W g)) mem2))
  by apply Forall_nil.
(* ---- the run: a0 := s0, the two restores, sp += 16, up to the ret ---- *)
subst c2. unfold cfg_at, w64.
pose proof HJ as HJ1. clear HJ. rename HJ1 into HJ.
cw_run cw_awr_stk.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem2) (mrestrict _ ?m3) |- _ =>
  assert (K2 : forall a, 0 <= a < 2 ^ 64 ->
    aview tfibsegs (w_H (sg_W g)) m3 a = aview tfibsegs (w_H (sg_W g)) mem2 a)
  by (intros a Ha; exact (cw_kept_run (fun _ => False) _ _ _ mem2 mem2 m3 (fun _ _ _ => eq_refl) HFr
        ltac:(cw_kwr_ro) a Ha (fun x => x))) end.
cw_keep cw_kwr_ro.
cw_leaf ltac:(idtac; cw_kept HJ0 KE
    ltac:(intros a Hx Him; exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low (sg_lyc g) (sg_Sc g) (sg_W g)
            (sg_memc g) (sg_mdc g) (sg_o g) (sg_n g) a (proj1 HJ0) HTD Hx Him))
    ltac:(intros a Hz; unfold sc_zone, sg_sp, T_scribble_text, ESTACK in Hz; exact Hz))
  ltac:(idtac).
destruct HPX as (P8 & Pout). split.
- rewrite R10, sv_denot_SOff0. change 41%nat with (33 + 8)%nat.
  rewrite (cw_ew_x (sg_regs g) (sx_regs32 regs2) 8%nat). cbn [nth sx_regs32]. rewrite Z_to_bv_bv_unsigned. exact P8.
- apply (sc_garr8_kept (mrestrict (w_H (sg_W g)) mem2)); [|exact Pout].
  intros x Hx. apply (mbyte_of_aview tfibsegs). apply K2.
  assert (Hl : Z.of_nat (length (fst (sc_res g))) = sg_n g)
    by (unfold sc_res, scribble_text_spec; rewrite sc_lib_len; lia).
  lia.
Time Qed.
End h.
End d.
