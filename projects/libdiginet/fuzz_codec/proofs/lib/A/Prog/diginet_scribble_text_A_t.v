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
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalk.v; 312 of its 358 lines of code are new or changed and 587 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/check_bytes_A.v, with its module names changed; 1071 of its 1123 lines of code are new or changed and 306 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/diginet_ring_encode_A.v, with its module paths and module names changed; 397 of its 429 lines of code are new or changed and 1091 lines of the source are left out. *)
(* diginet_scribble_text in image A (fuzz_codec.asan, 0x85cc4): the segment T of diginet_scribble_text_A_inv.v --
   the store 0x85d64 back to the loop head 0x85d1c or on to the padding 0x85de0 (sc_seg_T).

   The code: a3 := a1 + a5 = o + j, the instrumented check of it, sb t1 at o + j; s0 += t2 (i += d);
   a3 := a0 + s0 = q + i + d, the instrumented check of it, lbu t1 := q[i + d]; a5 += 1; t1 = 0 goes to the
   padding, else j + 1 < n goes back to the loop head and j + 1 = n to the padding.

   The state at 0x85d64 is built over the boundary's own registers (atoms 0 .. 31), the shadow offset (32), and
   three values of its own: 33 the text byte at i + d, 34 the address o + j it writes, 35 the address q + i + d. *)
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

Definition t_xs (g : sc_ctx) (i j d : Z) : list Z :=
[nth (Z.to_nat (i + d)) (sg_tb g) 0; sg_o g + j; sg_q g + i + d].
Definition t_AF : list (nat * afact) :=
[(32%nat, mkAF SB SB 0); (6%nat, mkAF 0 255 0); (7%nat, mkAF 1 2 0); (8%nat, mkAF 0 (2 ^ 47 - 1) 0);
 (10%nat, mkAF 1 (2 ^ 47 - 1) 0); (11%nat, mkAF 1 (2 ^ 47 - 1) 0); (12%nat, mkAF 0 4294967295 0);
 (15%nat, mkAF 0 4294967295 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 1 (2 ^ 47 - 1) 0);
 (35%nat, mkAF 1 (2 ^ 47 - 1) 0)].
(* the output byte the step writes, and the text byte it then reads *)
Definition t_rout : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 1 [].
Definition t_rtx : YP09.region := YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].

Ltac ewpeel := repeat (first [ rewrite ew_havoc_old by nat_side | rewrite ew_ewset_other by nat_side ]).
Ltac sreg := lazymatch goal with HS : st_ok ?segs ?Ev ?ss (restrict ?H ?msv) |- context [getr (ms_regs ?msv) ?r] =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  let R := fresh "R" in
  assert (R : getr (ms_regs msv) r = sv_denot Ev e)
    by (refine (eq_trans (st_ok_restrict_reg segs H Ev ss msv r HS) _); reflexivity);
  rewrite R; clear R end.
Ltac slit := sreg; reflexivity.
Ltac tval := sreg; rewrite sv_denot_SOff0; ewpeel; eassumption.
Ltac t_io := let rec kio := first [assumption | apply same_io_refl
  | eapply same_io_trans; [| apply cw_same_io_wvb]; kio
  | eapply same_io_trans; [| apply same_io_materialized; eassumption]; kio] in kio.
Ltac t_cfg pcv := lazymatch goal with HSv : st_ok _ _ _ (restrict _ _) |- _ =>
  norm_ss HSv; unfold cfg_at, w64; cbv [pcv];
  let Hms := fresh "Hms" in
  pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HSv eq_refl) as Hms; cbn [ss_pc] in Hms;
  rewrite <- Hms; reflexivity end.
Ltac t_kregs :=
  let HKf := fresh "HKf" in
  lazymatch goal with HKv : Forall _ sc_kregs |- _ => pose proof (proj1 (Forall_forall _ _) HKv) as HKf end;
  rewrite Forall_forall; intros rr Hrr;
  etransitivity; [| exact (HKf rr Hrr)];
  unfold sc_kregs in Hrr; cbn in Hrr;
  destruct Hrr as [Ex|[Ex|[Ex|[Ex|[Ex|[Ex|[Ex|[Ex|[Ex|[Ex|[Ex|[Ex|[Ex|[]]]]]]]]]]]]]];
  rewrite <- Ex; sreg; rewrite sv_denot_SOff0; ewpeel;
  lazymatch goal with EEv : forall n (r0 : bv 5), _ -> ew _ n = _ |- _ =>
    lazymatch goal with |- ew _ ?nn = getr _ ?r0 => exact (EEv nn r0 eq_refl) end end.
Ltac t_kp m0 := lazymatch goal with HG : mem_grows _ (mrestrict ?Hh ?m2) |- _ =>
  let KQ := fresh "KQ" in
  lazymatch goal with KPv : forall a, apresent _ _ a -> apresent _ _ a |- _ =>
    assert (KQ : forall a, apresent Hh m0 a -> apresent Hh m2 a)
      by (intros a Ha; eapply apresent_grows; [exact HG | exact (KPv a Ha)]);
    clear KPv; rename KQ into KP end end.
(* the write window of out[j] *)
Ltac t_awr Bv gg ov HTWv :=
idtac; lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?sp0v ?fp ?b0 ?bc ?lyv ?ownv =>
let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk sp0v fp b0 bc lyv ownv) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply (cw_awr_ok_cons_twr Bv _ _ _ (sg_STK gg) (sg_sp0 gg) (sg_FP gg) (sg_ly gg) (sg_S gg) (sg_lyc gg)
    (sg_Sc gg) (sg_own gg) (sg_W gg) (sg_memc gg) (spZ (sg_regs gg)) ov 1 34%nat);
  [ reflexivity
  | ewpeel; lazymatch goal with E34v : ew _ 34%nat = _ |- _ => rewrite E34v end;
    apply unsigned_lit_small; lia
  | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia
  | intros aa Haa; exact (HTWv aa ltac:(lia)) | ] ].
Ltac t_awr0 := idtac;
lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?sp0v ?fp ?b0 ?bc ?lyv ?ownv =>
  let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk sp0v fp b0 bc lyv ownv) end;
repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [azlit_tac|]].
Ltac tadd na nb xa xb := sreg;
  lazymatch goal with |- sv_denot ?Ev _ = _ =>
    first [ rewrite (denot_add2 Ev na nb xa xb ltac:(ewpeel; eassumption) ltac:(ewpeel; eassumption)
              ltac:(lia) ltac:(lia) ltac:(lia))
          | rewrite (denot_add2 Ev nb na xb xa ltac:(ewpeel; eassumption) ltac:(ewpeel; eassumption)
              ltac:(lia) ltac:(lia) ltac:(lia)) ] end;
  f_equal; lia.
Ltac toff nn cc := sreg; rewrite denot_lit_U; unfold w64; f_equal;
  lazymatch goal with |- U ?Ev (SOff nn cc) = _ =>
    rewrite (cw_U_offx Ev nn _ cc ltac:(ewpeel; eassumption) ltac:(lia)) end;
  rewrite Z.mod_small by lia; lia.
Ltac t_out2 gg memb outsv vv jv :=
lazymatch goal with HSv : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
  assert (Hout2 : garr8 tfibsegs (mrestrict (w_H (sg_W gg)) (ms_mem msv)) (sg_o gg) (outsv ++ [vv]));
  [ apply sc_garr8_snoc;
    [ apply (sc_garr8_kept (mrestrict (w_H (sg_W gg)) memb));
      [ intros xx Hxx; apply (mbyte_of_aview tfibsegs);
        lazymatch goal with KEv : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ => apply KEv; [lia | lia] end
      | assumption ]
    | lazymatch goal with Hlenv : Z.of_nat (length outsv) = jv |- _ => rewrite Hlenv end;
      replace (sg_o gg + jv) with (sg_o gg + jv + 0) by lia;
      apply (field_of_region Ev _ 34%nat (sg_o gg + jv) [YP09.mkChunk 0 (CVal 1 (SOff 6 0))] 0 1 0 1 0 1 (SOff 6 0));
      [ exact (st_ok_region_nth Ev ssv (restrict (w_H (sg_W gg)) msv) 1%nat _ HSv eq_refl)
      | ewpeel; lazymatch goal with E34v : ew _ 34%nat = _ |- _ => rewrite E34v end;
        apply unsigned_lit_small; lia
      | cbn [YP09.r_chunks In]; left; reflexivity
      | cbn [sv_denot]; ewpeel; lazymatch goal with E6v : ew _ 6%nat = _ |- _ => rewrite E6v end;
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia ]
    | lia ] | ] end.
Ltac t_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
    rewrite ?ew_ewset_other, ?ew_havoc_old in Hb by lia;
    first [ lia
          | lazymatch goal with E34v : ew _ 34%nat = _ |- _ => rewrite E34v in Hb end;
            rewrite unsigned_lit_small in Hb by lia; lia ] | ]);
destruct Hr.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem st_holds : sc_seg_T B.
Proof.
unfold sc_seg_T. intros g fuel W2 c2 Hpre Hcut.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hcut as (-> & regs2 & mem2 & md2 & -> & HJ & Hio & HC & HPT).
destruct HPT as (i & j & v & d & outs & R8 & R15 & R6 & R7 & HL & Hi0 & Hd12 & Hv255 & Hin1 & Hfuel & Hj
  & Hlen & Hout & Hspec).
destruct HL as (R10 & R11 & R12 & R14 & R16 & R17 & R5).
destruct (sc_stack B g Hpre) as (Hceil & H47 & H46 & Hal & Hwin & Hsp0 & Hprs).
destruct (sc_text B g Hpre) as (Hq0 & Hql & Hin0 & Hlen0 & HGT & HRAq & Hamq & Hoffq).
destruct (sc_out B g Hpre) as (Ho0 & Hon & Hn & Hoff & HTD & HTW & HRAo & Hhull & Hamo & HDJ).
pose proof (sc_amem47 (sg_q g) (sg_len g) ltac:(lia) ltac:(lia) Hamq) as Hq47.
pose proof (sc_amem47 (sg_o g) (sg_n g) ltac:(lia) ltac:(lia) Hamo) as Ho47.
pose proof Hpre as (HE & _). pose proof HE as (HJ0 & Hra & Hra4 & Hgp & Htp & _).
destruct HC as (HK & R2 & Vra & Vs0 & KC & KPc).
pose proof HK as HK'. repeat (apply Forall_cons_iff in HK' as (? & HK')). cbv beta in *.
unfold sg_sp, sg_len in *. unfold T_scribble_text, ESTACK in *.
pose proof (sc_in_skipn_lt 0 (sg_tb g) (Z.to_nat (i + d)) Hin1) as Hilt.
destruct (HGT (Z.to_nat (i + d)) ltac:(lia)) as (Hbv & Hbr).
set (b := nth (Z.to_nat (i + d)) (sg_tb g) 0) in *.
(* ---- the state at 0x85d64 ---- *)
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
  ew (Ereg regs2 (cw_extra (t_xs g i j d))) n = getr regs2 rr)
  by (intros nn rr Hnn; apply ew_Ereg_nat; exact Hnn).
assert (E33 : ew (Ereg regs2 (cw_extra (t_xs g i j d))) 33 = Z_to_bv 64 b)
  by exact (cw_ew_x regs2 (t_xs g i j d) 0).
assert (E34 : ew (Ereg regs2 (cw_extra (t_xs g i j d))) 34 = Z_to_bv 64 (sg_o g + j))
  by exact (cw_ew_x regs2 (t_xs g i j d) 1).
assert (E35 : ew (Ereg regs2 (cw_extra (t_xs g i j d))) 35 = Z_to_bv 64 (sg_q g + i + d))
  by exact (cw_ew_x regs2 (t_xs g i j d) 2).
assert (E32 : ew (Ereg regs2 (cw_extra (t_xs g i j d))) 32 = Z_to_bv 64 SB) by apply cw_ew_SB.
assert (E5 : ew (Ereg regs2 (cw_extra (t_xs g i j d))) 5 = Z_to_bv 64 8)
  by (rewrite (EE 5%nat 5%bv eq_refl); exact R5).
assert (E6 : ew (Ereg regs2 (cw_extra (t_xs g i j d))) 6 = Z_to_bv 64 v)
  by (rewrite (EE 6%nat 6%bv eq_refl); exact R6).
assert (E7 : ew (Ereg regs2 (cw_extra (t_xs g i j d))) 7 = Z_to_bv 64 d)
  by (rewrite (EE 7%nat 7%bv eq_refl); exact R7).
assert (E8 : ew (Ereg regs2 (cw_extra (t_xs g i j d))) 8 = Z_to_bv 64 i)
  by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E10 : ew (Ereg regs2 (cw_extra (t_xs g i j d))) 10 = Z_to_bv 64 (sg_q g))
  by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (E11 : ew (Ereg regs2 (cw_extra (t_xs g i j d))) 11 = Z_to_bv 64 (sg_o g))
  by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
assert (E12 : ew (Ereg regs2 (cw_extra (t_xs g i j d))) 12 = Z_to_bv 64 (sg_n g))
  by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
assert (E15 : ew (Ereg regs2 (cw_extra (t_xs g i j d))) 15 = Z_to_bv 64 j)
  by (rewrite (EE 15%nat 15%bv eq_refl); exact R15).
assert (E16 : ew (Ereg regs2 (cw_extra (t_xs g i j d))) 16 = Z_to_bv 64 (sg_q g + 1))
  by (rewrite (EE 16%nat 16%bv eq_refl); exact R16).
assert (E17 : ew (Ereg regs2 (cw_extra (t_xs g i j d))) 17 = Z_to_bv 64 46)
  by (rewrite (EE 17%nat 17%bv eq_refl); exact R17).
assert (HAF : atoms_ok (Ereg regs2 (cw_extra (t_xs g i j d))) t_AF).
{ unfold t_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E32, E6, E7, E8, E10, E11, E12, E15, E33, E34, E35.
  rewrite !unsigned_lit_small by (try unfold SB; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia. }
assert (HS : st_ok tfibsegs (Ereg regs2 (cw_extra (t_xs g i j d)))
  (mkSS PC_T sr_atoms [] None (mkFacts t_AF [] []))
  (restrict (w_H (sg_W g)) (mkst regs2 (Z_to_bv 64 PC_T) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact HAF | split; exact I]. }
remember (Ereg regs2 (cw_extra (t_xs g i j d))) as E eqn:HEE. clear HEE.
lazymatch goal with HSv : st_ok _ ?Ev ?ssv ?msv |- _ =>
  let HS3 := fresh "HS" in
  pose proof (st_ok_pin_rege Ev ssv msv (14%bv : bv 5) (SOff 32 0) HSv ltac:(intros X; discriminate X)
    ltac:(cbn [sv_denot]; rewrite E32; rewrite unsigned_lit_small by (unfold SB; lia); rewrite Z.add_0_r;
          cbn [ms_regs restrict mkst]; symmetry; exact R14)) as HS3;
  clear HSv; rename HS3 into HS; norm_ss HS end.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H (sg_W g)) mem2)) by apply Forall_nil.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (sg_o g + j <= a < sg_o g + j + 1) ->
  aview tfibsegs (w_H (sg_W g)) mem2 a = aview tfibsegs (w_H (sg_W g)) mem2 a) by (intros; reflexivity).
assert (KP : forall a, apresent (w_H (sg_W g)) mem2 a -> apresent (w_H (sg_W g)) mem2 a) by (intros; assumption).
unfold cfg_at. change (w64 PC_T) with (Z_to_bv 64 PC_T).
pose proof HJ as HJ1. clear HJ. rename HJ1 into HJ.
(* 0x85d64: a3 := a1 + a5 = o + j *)
cw_run_to t_awr0 0x85d68. t_kp mem2. cw_keep cw_kwr_ro.
lazymatch goal with HSv : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
  assert (Ra3 : getr (ms_regs msv) 13 = w64 (sg_o g + j)) by (unfold w64; tadd 11%nat 15%nat (sg_o g) j) end.
lazymatch goal with HSv : st_ok _ ?Ev ?ssv ?msv |- _ =>
  let HS3 := fresh "HS" in
  pose proof (st_ok_pin_rege Ev ssv msv (13%bv : bv 5) (SOff 34 0) HSv ltac:(intros X; discriminate X)
    ltac:(cbn [ms_regs restrict mkst]; rewrite Ra3; cbn [sv_denot]; ewpeel;
          rewrite E34; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity)) as HS3;
  clear HSv; rename HS3 into HS; norm_ss HS end.
(* the one byte of the output this step writes *)
lazymatch goal with HSv : st_ok _ ?Ev ?ssv ?msv |- _ =>
  let HS3 := fresh "HS" in
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv t_rout HSv eq_refl
    ltac:(unfold region_ok, t_rout;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
          ewpeel; rewrite E34; rewrite unsigned_lit_small by lia;
          split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
          intros oo Hoo; apply (apresent_writable tfibsegs); apply KP; apply KPc;
          exact (proj1 (proj2 (HTW (sg_o g + j + oo) ltac:(lia)))))
    ltac:(unfold t_rout;
          lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
            let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; exact I)) as HS3;
  clear HSv; rename HS3 into HS; norm_ss HS end.
clear SHOK.
lazymatch goal with HSv : st_ok _ ?Ev _ (restrict _ ?msv) |- _ =>
  assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 34 1 0] Ev (mrestrict (w_H (sg_W g)) (ms_mem msv)));
  [ apply Forall_cons; [|apply Forall_nil];
    apply (shent_app_of_app tfibsegs Ev CW_Bx 34%nat (sg_o g + j) 0 1);
    [ apply cw_U_Bx; ewpeel; exact E32
    | apply cw_U_atom0; [ewpeel; exact E34 | lia]
    | rewrite Z.add_0_r;
      exact (proj2 (cj_dst_byte tfibsegs B LAWS (sg_lyc g) (sg_Sc g) (sg_W g) (sg_memc g) (sg_mdc g)
               (sg_o g) (sg_n g) (sg_o g + j) (proj1 HJ0) HTD ltac:(lia)))
    | lia ] | ] end.
(* 0x85d68-0x85d80: the check, the store, s0 += t2, a3 := a0 + s0 *)
lazymatch goal with HSv : st_ok _ _ _ _, HJv : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
                    SHOKv : sh_ok _ _ _ _ _ |- _ =>
  aj_run_to_tok tfibtbl_lib_ok HSv HJv SHOKv CW_Bspan 0x85d84 end;
[ rewrite (cw_U_atom0 _ 34 (sg_o g + j) ltac:(ewpeel; exact E34) ltac:(lia));
  apply (sc_obl_of (sg_W g) _ _ _ _ (sg_o g) (sg_n g));
  [ apply (sc_ra_kept B g _ Hpre);
    first [ intros aa Haa Hzz; etransitivity;
            [ apply KE; [exact Haa | unfold sc_zone, sg_sp, T_scribble_text, ESTACK in Hzz; lia]
            | exact (KC aa Haa Hzz) ]
          | exact Hamo | exact HRAo | lia ]
  | ewpeel; exact E32 | lia | lia ]
| t_awr B g (sg_o g + j) HTW
| idtac ].
t_kp mem2. cw_keep t_kwr.
(* the byte the store left at o + j *)
lazymatch goal with HSv : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
  assert (Hstore : val_mem tfibsegs (mrestrict (w_H (sg_W g)) (ms_mem msv)) (sg_o g + j) 1 v);
  [ replace (sg_o g + j) with (sg_o g + j + 0) by lia;
    apply (field_of_region Ev _ 34%nat (sg_o g + j) [YP09.mkChunk 0 (CVal 1 (SOff 6 0))] 0 1 0 1 0 1 (SOff 6 0));
    [ exact (st_ok_region_nth Ev ssv (restrict (w_H (sg_W g)) msv) 0%nat _ HSv eq_refl)
    | ewpeel; rewrite E34; apply unsigned_lit_small; lia
    | cbn [YP09.r_chunks In]; left; reflexivity
    | cbn [sv_denot]; ewpeel; rewrite E6; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | cbn; lia | cbn; lia ] | ] end.
(* a3 = a0 + s0 = q + i + d: the next text byte *)
(* a3 = a0 + s0 = q + i + d, the next text byte *)
lazymatch goal with HSv : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
  assert (Ra3b : getr (ms_regs msv) 13 = w64 (sg_q g + i + d))
    by (unfold w64; sreg;
        rewrite (sc_denot_add3l Ev 7 8 10 d i (sg_q g)
          ltac:(ewpeel; exact E7) ltac:(ewpeel; exact E8) ltac:(ewpeel; exact E10)
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia));
        f_equal; lia) end.
lazymatch goal with HSv : st_ok _ ?Ev ?ssv ?msv |- _ =>
  let HS3 := fresh "HS" in
  pose proof (st_ok_pin_rege Ev ssv msv (13%bv : bv 5) (SOff 35 0) HSv ltac:(intros X; discriminate X)
    ltac:(cbn [ms_regs restrict mkst]; rewrite Ra3b; cbn [sv_denot]; ewpeel;
          rewrite E35; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity)) as HS3;
  clear HSv; rename HS3 into HS; norm_ss HS end.
lazymatch goal with HSv : st_ok _ ?Ev ?ssv ?msv |- _ =>
  let HS3 := fresh "HS" in
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv t_rtx HSv eq_refl
    ltac:(unfold region_ok, t_rtx;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
          ewpeel; rewrite E35; rewrite unsigned_lit_small by lia;
          split; [lia|]; split; [lia|]; split; [intros oo Hoo; lia|];
          apply Forall_cons; [|apply Forall_nil];
          apply (chunk_ok_val tfibsegs Ev _ (sg_q g + i + d) 0 1 (SOff 33 0) b);
          [ cbn [sv_denot]; ewpeel; rewrite E33; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | cbn; lia | cbn; lia |];
          rewrite Z.add_0_r;
          pose proof (proj1 (sc_text_val B g _ Hpre
            ltac:(intros aa Haa Hzz; etransitivity;
                  [ apply KE; [exact Haa | unfold sc_zone, sg_sp, T_scribble_text, ESTACK in Hzz; lia]
                  | exact (KC aa Haa Hzz) ])
            (Z.to_nat (i + d)) ltac:(lia))) as Hv1;
          replace (sg_q g + Z.of_nat (Z.to_nat (i + d))) with (sg_q g + i + d) in Hv1 by lia;
          exact Hv1)
    ltac:(unfold t_rtx;
          lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
            let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          ewpeel; rewrite E35, E34; rewrite !unsigned_lit_small by lia;
          first [split; [lia | exact I] | lia])) as HS3;
  clear HSv; rename HS3 into HS; norm_ss HS end.
cw_run_ob ltac:(t_awr B g (sg_o g + j) HTW)
  ltac:(idtac; lazymatch goal with |- context [U ?Ev (SOff 35 0)] =>
          rewrite (cw_U_atom0 Ev 35 (sg_q g + i + d) ltac:(ewpeel; exact E35) ltac:(lia)) end;
        apply (sc_obl_of (sg_W g) _ _ _ _ (sg_q g) (Z.of_nat (length (sg_tb g))));
        [ apply (sc_ra_kept B g _ Hpre);
          first [ intros aa Haa Hzz; etransitivity;
                  [ apply KE; [exact Haa | unfold sc_zone, sg_sp, T_scribble_text, ESTACK in Hzz; lia]
                  | exact (KC aa Haa Hzz) ]
                | exact Hamq | exact HRAq | lia ]
        | ewpeel; exact E32 | lia | lia ]).
t_kp mem2. cw_keep t_kwr.
cw_branch Hz.
all: rewrite branch_eq_U in Hz;
     lazymatch type of Hz with context [U ?Ev (SOff 33 0)] =>
       rewrite (cw_U_atom0 Ev 33 b ltac:(ewpeel; exact E33) ltac:(lia)) in Hz end;
     rewrite U_SLit in Hz; hc_prop Hz; replace (zcanon 0) with 0 in Hz by reflexivity.
- (* the text ends here: the padding *)
  cw_run_to ltac:(t_awr B g (sg_o g + j) HTW) PC_P. t_kp mem2. cw_keep t_kwr.
  t_out2 g mem2 outs v j.
  apply SRr_ret. right.
  lazymatch goal with HSv : st_ok _ _ _ (restrict _ ?msv) |- _ =>
    split; [reflexivity|]; exists (ms_regs msv), (ms_mem msv); eexists end.
  split; [t_cfg PC_P|]. split; [eassumption|]. split; [t_io|].
  split;
  [ split; [t_kregs|];
    split; [sreg; rewrite sv_denot_SOff0; ewpeel;
            etransitivity;
            [ lazymatch goal with EEv : forall n (r0 : bv 5), _ -> ew _ n = _ |- _ =>
                exact (EEv 2%nat 2%bv eq_refl) end
            | assumption]|];
    split; [unfold sg_sp; apply (sc_val_mem_kept (mrestrict (w_H (sg_W g)) mem2));
            [intros xx Hxx; apply (mbyte_of_aview tfibsegs); apply KE; [lia | lia] | assumption]|];
    split; [unfold sg_sp; apply (sc_val_mem_kept (mrestrict (w_H (sg_W g)) mem2));
            [intros xx Hxx; apply (mbyte_of_aview tfibsegs); apply KE; [lia | lia] | assumption]|];
    split; [intros aa Haa Hzz; etransitivity;
            [ apply KE; [exact Haa | unfold sc_zone, sg_sp, T_scribble_text, ESTACK in Hzz; lia]
            | exact (KC aa Haa Hzz) ]|];
    intros aa Haa; apply KP; apply KPc; exact Haa
  |];
  exists (i + d), (j + 1), (outs ++ [v]).
  split; [unfold w64; tadd 7%nat 8%nat d i|]. split; [toff 15%nat 1|].
  split; [tval|]. split; [tval|].
  split; [lia|]. split; [lia|]. split; [rewrite length_app; cbn [length]; lia|].
  split; [exact Hout2|].
  rewrite Hspec. rewrite (sc_lib_at_zero (sg_tb g) (Z.to_nat (i + d)) (Z.to_nat (sg_n g - (j + 1)))
    ltac:(lia) ltac:(exact Hz)).
  cbv [fst snd]. f_equal; lia.
- (* the text goes on *)
  cw_run ltac:(t_awr B g (sg_o g + j) HTW). t_kp mem2. cw_keep t_kwr.
  cw_branch Hlt.
  all: rewrite branch_ltu_U in Hlt;
       lazymatch type of Hlt with context [U ?Ev (SOff 15 1)] =>
         rewrite (cw_U_offx Ev 15 j 1 ltac:(ewpeel; exact E15) ltac:(lia)) in Hlt;
         rewrite (cw_U_atom0 Ev 12 (sg_n g) ltac:(ewpeel; exact E12) ltac:(lia)) in Hlt end;
       rewrite (Z.mod_small (j + 1) (2 ^ 64)) in Hlt by lia; hc_prop Hlt.
  + (* j + 1 < n: back to the loop head *)
    cw_run_to ltac:(t_awr B g (sg_o g + j) HTW) PC_H. t_kp mem2. cw_keep t_kwr.
    t_out2 g mem2 outs v j.
    apply SRr_ret. left.
    lazymatch goal with HSv : st_ok _ _ _ (restrict _ ?msv) |- _ =>
      split; [reflexivity|]; exists (ms_regs msv), (ms_mem msv); eexists end.
    split; [t_cfg PC_H|]. split; [eassumption|]. split; [t_io|].
  split;
  [ split; [t_kregs|];
    split; [sreg; rewrite sv_denot_SOff0; ewpeel;
            etransitivity;
            [ lazymatch goal with EEv : forall n (r0 : bv 5), _ -> ew _ n = _ |- _ =>
                exact (EEv 2%nat 2%bv eq_refl) end
            | assumption]|];
    split; [unfold sg_sp; apply (sc_val_mem_kept (mrestrict (w_H (sg_W g)) mem2));
            [intros xx Hxx; apply (mbyte_of_aview tfibsegs); apply KE; [lia | lia] | assumption]|];
    split; [unfold sg_sp; apply (sc_val_mem_kept (mrestrict (w_H (sg_W g)) mem2));
            [intros xx Hxx; apply (mbyte_of_aview tfibsegs); apply KE; [lia | lia] | assumption]|];
    split; [intros aa Haa Hzz; etransitivity;
            [ apply KE; [exact Haa | unfold sc_zone, sg_sp, T_scribble_text, ESTACK in Hzz; lia]
            | exact (KC aa Haa Hzz) ]|];
    intros aa Haa; apply KP; apply KPc; exact Haa
  |];
    exists (i + d), (j + 1), b, (outs ++ [v]).
    split; [unfold w64; tadd 7%nat 8%nat d i|]. split; [toff 15%nat 1|]. split; [tval|].
    split.
    { split; [tval|]. split; [tval|]. split; [tval|]. split; [tval|].
      split; [tval|]. split; [tval|]. tval. }
    split; [lia|]. split; [reflexivity|]. split; [exact Hz|].
    split; [replace (Z.to_nat (i + d) + 1)%nat with (S (Z.to_nat (i + d))) by lia;
            apply (sc_in0_S (sg_tb g) (Z.to_nat (i + d))); [exact Hin1 | exact Hz]|].
    split; [unfold sg_len; lia|]. split; [lia|].
    split; [rewrite length_app; cbn [length]; lia|]. split; [exact Hout2|].
    exact Hspec.
  + (* j + 1 = n: the padding *)
    cw_run_to ltac:(t_awr B g (sg_o g + j) HTW) PC_P. t_kp mem2. cw_keep t_kwr.
    t_out2 g mem2 outs v j.
    apply SRr_ret. right.
    lazymatch goal with HSv : st_ok _ _ _ (restrict _ ?msv) |- _ =>
      split; [reflexivity|]; exists (ms_regs msv), (ms_mem msv); eexists end.
    split; [t_cfg PC_P|]. split; [eassumption|]. split; [t_io|].
  split;
  [ split; [t_kregs|];
    split; [sreg; rewrite sv_denot_SOff0; ewpeel;
            etransitivity;
            [ lazymatch goal with EEv : forall n (r0 : bv 5), _ -> ew _ n = _ |- _ =>
                exact (EEv 2%nat 2%bv eq_refl) end
            | assumption]|];
    split; [unfold sg_sp; apply (sc_val_mem_kept (mrestrict (w_H (sg_W g)) mem2));
            [intros xx Hxx; apply (mbyte_of_aview tfibsegs); apply KE; [lia | lia] | assumption]|];
    split; [unfold sg_sp; apply (sc_val_mem_kept (mrestrict (w_H (sg_W g)) mem2));
            [intros xx Hxx; apply (mbyte_of_aview tfibsegs); apply KE; [lia | lia] | assumption]|];
    split; [intros aa Haa Hzz; etransitivity;
            [ apply KE; [exact Haa | unfold sc_zone, sg_sp, T_scribble_text, ESTACK in Hzz; lia]
            | exact (KC aa Haa Hzz) ]|];
    intros aa Haa; apply KP; apply KPc; exact Haa
  |];
    exists (i + d), (j + 1), (outs ++ [v]).
    split; [unfold w64; tadd 7%nat 8%nat d i|]. split; [toff 15%nat 1|].
    split; [tval|]. split; [tval|].
    split; [lia|]. split; [lia|]. split; [rewrite length_app; cbn [length]; lia|].
    split; [exact Hout2|].
    rewrite Hspec. replace (Z.to_nat (sg_n g - (j + 1))) with 0%nat by lia.
    rewrite sc_lib_0. cbv [fst snd]. cbn [repeat]. rewrite app_nil_r. f_equal; lia.
Time Qed.


End h.
End d.
