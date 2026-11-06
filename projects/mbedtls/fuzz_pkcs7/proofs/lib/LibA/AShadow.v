(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Export ALazy.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AShadow () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.LibA.ALazy.shadow_of"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.LibA.ALazy.al_got"; "OSSVerify.KrLib.LibA.ALazy.al_gsb"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "OSSVerify.KrLib.LibA.ALazy.al_img_lo"; "OSSVerify.KrLib.LibA.ALazy.al_img_hi"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "WithSegs.shadow_val_ok"; "Corelib.Init.Datatypes.option"; "WithSegs.aobj"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.Some"; "WithSegs.shadow_val_okN"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.bv_unsigned"; "stdpp.bitvector.definitions.bv_signed"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Lib.Step.ro_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "WithSegs.shadow_ok"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "OSSVerify.KrLib.Lib.Mem.wa"; "Corelib.Init.Logic.or"; "WithSegs.abase"; "OSSVerify.KrLib.Lib.Frame.ivl"; "WithSegs.Frame.w_client"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "OSSVerify.KrLib.Lib.Frame.disjoint_from"].


Section WithSegs.
Variable segs : list Segment.
Variable L : asan_layout.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cs_ok (CS : Z -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_AShadow ()) "(0.Pc,$1.P,A1.O1.R1.(0.(0.(2.=R2.)(3.R2.(4.+2.+40.)))(0.(2.=(5.VL,R2.))(0.(3.(5.VL,R2.)(4.+2.+40.))(6.A1.O1.(5.VL,R2.)))))(0.Pi,$1.P,(0.(2.=R1.)(3.R1.+8.))(0.(6.A1.O1.(7.(8.VL,)R2.))(6.A1.O1.(7.(9.VL,)R2.)))(0.Pc,$1.Pi,$1.P,A1.O1.R2.P,(0.(2.=R2.)(3.R2.+8.))(0.(6.(:.$1.(5.VL,R4.)(7.(8.VL,)R3.)))(6.(:.$1.(5.VL,R4.)(7.(9.VL,)R3.))))(0.(2.=(;.VL,))(3.(;.VL,)(4.+2.+40.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition al_wf : Prop := ltac2:(CDefT.buildp (gd_tbl_AShadow ()) "(0.(2.=(<.VL,))(0.(3.(=.VL,)(4.+2.+40.))(0.(2.(<.VL,)(8.VL,))(0.(2.(7.(8.VL,)+8.)(=.VL,))(0.(2.(<.VL,)(9.VL,))(2.(7.(9.VL,)+8.)(=.VL,)))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma cs_ok_sb : forall CS, cs_ok CS -> 0 <= al_sb L < 2^64.
Proof. intros CS (_ & _ & _ & H); exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition shadow_val_ok (a : Z) (k : byte) : Prop :=
  bv_unsigned k = 0 \/ (a mod 8 < bv_unsigned k <= 7).

Definition shadow_ok (m : mem) (A n : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AShadow ()) "Pa,$1.P,(0.(2.O2.R1.)(3.R1.(7.O2.O1.)))(>.(?.&8.)Lk,(?.&8.)(0.(10.Vsegs,O3.(5.VL,R3.)(11.(?.&8.)R1.(12.(?.&8.))))(13.R3.R1.)))")
(* [comment removed for export] *).

#[using="Type"] Lemma bytes_at_read1 : forall m s k, bytes_at segs m s [k] -> ov_read_bytes segs m (Z_to_bv 64 s) 1 = Some [k].
Proof.
  intros m s k B. pose proof (bytes_at_ov_read segs m s [k] 0 1 B ltac:(cbn; lia)) as R.
  rewrite Z.add_0_r in R. exact R.
Qed.

Definition aobj (CS : Z -> Prop) (m : mem) (A n : Z) : Prop :=
  crange CS A n /\ shadow_ok m A n.

#[using="Type"] Lemma aobj_crange : forall CS m A n, aobj CS m A n -> crange CS A n.
Proof. intros CS m A n [H _]; exact H. Qed.

#[using="Type"] Lemma aobj_sub : forall CS m A n B k, aobj CS m A n -> A <= B -> B + k <= A + n -> aobj CS m B k.
Proof.
  intros CS m A n B k [HC HS] H1 H2. split; [eapply crange_sub; eauto|].
  intros a Ha. apply HS. lia.
Qed.

#[using="Type"] Lemma aobj_cs_mono : forall (CS CS' : Z -> Prop) m A n,
  (forall x, CS x -> CS' x) -> aobj CS m A n -> aobj CS' m A n.
Proof. intros CS CS' m A n HS [HC HSH]. split; [eapply crange_mono; eauto| exact HSH]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aobj_shadow1_at : ltac2:(CDefT.buildp (gd_tbl_AShadow ()) "PCS,P,$1.SpPm,P,(?.&40.)(14.(?.&8.))PA,$1.Pn,$1.Pc,$1.Ps,$1.P,(15.R6.R5.R4.R3.)P,(0.(2.R5.R3.)(3.R3.(7.R5.R4.)))P,(:.$1.R3.(5.VL,R4.))(>.(?.&8.)Lk,(?.&8.)(0.(:.(14.(16.(?.&8.)))(17.Vsegs,R9.(18.&40.R5.)#1.)(19.(16.(?.&8.))(11.(?.&8.)R1.(12.(?.&8.)))))(13.R6.R1.)))")
(* [comment removed for export] *).
Proof.
  intros CS m A n c s [_ HS] Hc ->. destruct (HS c Hc) as (k & B & HK). exists k. split; [|exact HK].
  apply bytes_at_read1. exact B.
Qed.

(* [comment removed for export] *)
Definition shadow_val_okN (c n : Z) (k : byte) : Prop :=
  bv_unsigned k = 0 \/ (c mod 8 + (n - 1) < bv_unsigned k <= 7).

#[using="Type"] Lemma bytes_at_func1 : forall m s k k', bytes_at segs m s [k] -> bytes_at segs m s [k'] -> k = k'.
Proof.
  intros m s k k' (_ & _ & H) (_ & _ & H'). specialize (H 0%nat ltac:(cbn; lia)). specialize (H' 0%nat ltac:(cbn; lia)).
  cbn in H, H'. congruence.
Qed.

#[using="Type"] Lemma shadow_of_granule' : forall c c', c - c mod 8 <= c' < c - c mod 8 + 8 -> shadow_of L c' = shadow_of L c.
Proof.
  intros c c' H. unfold shadow_of. f_equal.
  pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.mod_pos_bound c 8 ltac:(lia)).
  replace c' with ((c' - (c - c mod 8)) + c / 8 * 8) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

#[using="Type"] Lemma aobj_shadowN_at : ltac2:(CDefT.buildp (gd_tbl_AShadow ()) "PCS,P,$1.SpPm,P,(?.&40.)(14.(?.&8.))PA,$1.Psz,$1.Pc,$1.Pn,$1.Ps,$1.P,(15.R7.R6.R5.R4.)P,(2.R6.R4.)P,(2.(7.R5.R4.)(7.R7.R6.))P,(2.+1.R5.)P,(:.$1.R5.(5.VL,R7.))(>.(?.&8.)Lk,(?.&8.)(0.(:.(14.(16.(?.&8.)))(17.Vsegs,R<.(18.&40.R7.)#1.)(19.(16.(?.&8.))(11.(?.&8.)R1.(12.(?.&8.)))))(1:.R9.R8.R1.)))")
(* [comment removed for export] *).
Proof.
  intros CS m A sz c n s [_ HS] H1 H2 Hn ->.
  destruct (HS c ltac:(lia)) as (k & B & HK). exists k. split; [apply bytes_at_read1; exact B|].
  destruct HK as [HK|HK]; [left; exact HK| right].
  pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as MB.
  destruct (Z_lt_le_dec (c mod 8 + (n - 1)) (bv_unsigned k)) as [|GE]; [lia|]. exfalso.
  (* [comment removed for export] *)
  set (c' := c - c mod 8 + bv_unsigned k).
  destruct (HS c' ltac:(subst c'; lia)) as (k' & B' & HK').
  rewrite (shadow_of_granule' c c') in B' by (subst c'; lia).
  pose proof (bytes_at_func1 _ _ _ _ B B') as <-.
  assert (E : c' mod 8 = bv_unsigned k).
  { subst c'. pose proof (Z.div_mod c 8 ltac:(lia)).
    replace (c - c mod 8 + bv_unsigned k) with (bv_unsigned k + (c / 8) * 8) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  destruct HK' as [HK'|HK']; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shadow_of_granule : forall c g, g mod 8 = 0 -> g <= c < g + 8 -> shadow_of L c = shadow_of L g.
Proof.
  intros c g Hg Hc. unfold shadow_of. f_equal.
  replace c with ((c - g) + g / 8 * 8) by (pose proof (Z.div_mod g 8 ltac:(lia)); lia).
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

#[using="Type"] Lemma aobj_shadow0_at : ltac2:(CDefT.buildp (gd_tbl_AShadow ()) "PCS,P,$1.SpPm,P,(?.&40.)(14.(?.&8.))PA,$1.Pn,$1.Pc,$1.Pg,$1.Ps,$1.P,(15.R7.R6.R5.R4.)P,(:.$1.(1;.R3.+8.)=)P,(0.(2.R4.R5.)(3.R5.(7.R4.+8.)))P,(2.R8.R5.)P,(2.(7.R6.+8.)(7.R9.R8.))P,(:.$1.R6.(5.VL,R8.))(:.(14.(16.(?.&8.)))(17.Vsegs,R<.(18.&40.R7.)#1.)(19.(16.(?.&8.))(11.(?.&8.)(18.&8.=)(12.(?.&8.)))))")
(* [comment removed for export] *).
Proof.
  intros CS m A n c g s [_ HS] Hg Hc H1 H2 ->.
  destruct (HS (g + 7) ltac:(lia)) as (k & RD & HK).
  rewrite (shadow_of_granule c g), <- (shadow_of_granule (g + 7) g) by lia.
  rewrite (bytes_at_read1 _ _ _ RD). do 2 f_equal. apply bv_eq. change (bv_unsigned (Z_to_bv 8 0)) with 0.
  destruct HK as [HK|HK]; [exact HK|].
  replace ((g + 7) mod 8) with 7 in HK; [lia|].
  rewrite <- Z.add_mod_idemp_l by lia. rewrite Hg. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aobj_shadow0_al : ltac2:(CDefT.buildp (gd_tbl_AShadow ()) "PCS,P,$1.SpPm,P,(?.&40.)(14.(?.&8.))PA,$1.Pn,$1.Pc,$1.Ps,$1.P,(15.R6.R5.R4.R3.)P,(:.$1.(1;.R3.+8.)=)P,(2.R6.R4.)P,(2.(7.R5.+8.)(7.R7.R6.))P,(:.$1.R5.(5.VL,R6.))(:.(14.(16.(?.&8.)))(17.Vsegs,R:.(18.&40.R6.)#1.)(19.(16.(?.&8.))(11.(?.&8.)(18.&8.=)(12.(?.&8.)))))")
(* [comment removed for export] *).
Proof. intros. eapply aobj_shadow0_at with (g := c); eauto; lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shadow_val_signedN : ltac2:(CDefT.buildp (gd_tbl_AShadow ()) "Pa,$1.Pn,$1.Pk,(?.&8.)P,(1:.R3.R2.R1.)P,(6.(:.$1.(1<.&8.R2.)=))(0.(:.$1.(1=.&8.R3.)(1<.&8.R3.))(0.(3.(7.(1;.R5.+8.)(1>.R4.+1.))(1<.&8.R3.))(2.(1<.&8.R3.)+7.)))")
(* [comment removed for export] *).
Proof.
  intros a n k [H|H] NZ; [contradiction|]. split; [|exact H].
  pose proof (bv_unsigned_in_range 8 k) as KR. unfold bv_modulus in KR.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8) with 256 in *. change (2 ^ (Z.of_N 8 - 1)) with 128.
  rewrite Z.mod_small; lia.
Qed.

#[using="Type"] Lemma shadow_val_signed : ltac2:(CDefT.buildp (gd_tbl_AShadow ()) "Pa,$1.Pk,(?.&8.)P,(13.R2.R1.)P,(6.(:.$1.(1<.&8.R2.)=))(0.(:.$1.(1=.&8.R3.)(1<.&8.R3.))(0.(3.(1;.R4.+8.)(1<.&8.R3.))(2.(1<.&8.R3.)+7.)))")
(* [comment removed for export] *).
Proof.
  intros a k [H|H] NZ; [contradiction|]. split; [|exact H].
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (2 ^ (Z.of_N 8 - 1)) with 128.
  rewrite Z.mod_small; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition abase (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AShadow ()) "(0.(1?.Vsegs,O1.(8.VL,)(11.$20.(21.(18.&40.(9.VL,)))(12.$20.)))(1?.Vsegs,O1.(9.VL,)(11.$20.(21.(18.&40.(;.VL,)))(12.$20.))))")
(* [comment removed for export] *).

#[using="Type"] Lemma abase_got : forall m, abase m -> ro_cells segs m (al_got L) [C8 (Z_to_bv 64 (al_gsb L))].
Proof. intros m [H _]; exact H. Qed.
#[using="Type"] Lemma abase_gsb : forall m, abase m -> ro_cells segs m (al_gsb L) [C8 (Z_to_bv 64 (al_sb L))].
Proof. intros m [_ H]; exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Frame.
Variable CS : Z -> Prop.
Hypothesis CSOK : cs_ok CS.

#[using="CSOK"] Lemma shadow_ok_frame : ltac2:(CDefT.buildp (gd_tbl_AShadow ()) "Pm,P,(?.&40.)(14.(?.&8.))PA,$1.Pn,$1.Pa,$1.Pbs,(16.(?.&8.))P,(22.VCS,R4.R3.)P,(22.VCS,R3.(23.(24.(?.&8.)R2.)))P,(2.=R4.)P,(2.(7.R5.(23.(24.(?.&8.)R4.)))(4.+2.+40.))P,(25.R9.R8.R7.)(25.(26.R:.(27.R7.)R6.)R9.R8.)")
(* [comment removed for export] *).
Proof.
  intros m A n a bs HA Ha Ha0 Ha1 HS c Hc.
  destruct (HS c Hc) as (k & RD & HK). exists k. split; [|exact HK].
  destruct CSOK as (C1 & _ & _ & _).
  destruct (C1 c (HA c Hc)) as (R0 & R1 & R2 & NCS).
  apply bytes_at_write_other; [exact RD| lia| lia|]. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ].
  destruct (Z_lt_le_dec (shadow_of L c) a); [left; lia|].
  destruct (Z_lt_le_dec (shadow_of L c) (a + Z.of_nat (length bs))); [|right; lia].
  exfalso. apply NCS. replace (shadow_of L c) with (a + (shadow_of L c - a)) by lia. apply Ha. lia.
Qed.

#[using="CSOK"] Lemma aobj_frame : ltac2:(CDefT.buildp (gd_tbl_AShadow ()) "Pm,P,(?.&40.)(14.(?.&8.))PA,$1.Pn,$1.Pa,$1.Pbs,(16.(?.&8.))P,(15.VCS,R5.R4.R3.)P,(22.VCS,R3.(23.(24.(?.&8.)R2.)))P,(2.=R4.)P,(2.(7.R5.(23.(24.(?.&8.)R4.)))(4.+2.+40.))(15.VCS,(26.R9.(27.R6.)R5.)R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros m A n a bs [HC HS] Ha Ha0 Ha1. split; [exact HC|]. eapply shadow_ok_frame; eauto.
Qed.

#[using="Type"] Lemma range_apart_of_cs : ltac2:(CDefT.buildp (gd_tbl_AShadow ()) "Pa,$1.Pn,$1.PG,$1.P,(22.VCS,R3.R2.)P,(3.=R3.)P,Pi,$1.P,(0.(2.=R1.)(3.R1.+8.))(6.A1.VCS,(7.R5.R2.))(28.(2.(7.R4.+8.)R6.)(2.(7.R6.R5.)R4.))")
(* [comment removed for export] *).
Proof.
  intros a n G Ha Hn NG.
  destruct (Z_lt_le_dec (G + 8) (a + 1)); [left; lia|].
  destruct (Z_lt_le_dec G (a + n)); [|right; lia].
  exfalso. destruct (Z_lt_le_dec a G).
  - apply (NG 0 ltac:(lia)). apply Ha. lia.
  - apply (NG (a - G) ltac:(lia)). replace (G + (a - G)) with a by lia. apply Ha. lia.
Qed.

#[using="CSOK"] Lemma abase_frame : ltac2:(CDefT.buildp (gd_tbl_AShadow ()) "Pm,P,(?.&40.)(14.(?.&8.))Pa,$1.Pbs,(16.(?.&8.))P,(29.R3.)P,(22.VCS,R3.(23.(24.(?.&8.)R2.)))P,(3.=(23.(24.(?.&8.)R3.)))P,(2.=R5.)P,(2.(7.R6.(23.(24.(?.&8.)R5.)))(4.+2.+40.))(29.(26.R8.(27.R7.)R6.))")
(* [comment removed for export] *).
Proof.
  intros m a bs [G1 G2] Ha Hn Ha0 Ha1. destruct CSOK as (_ & C2 & _ & _).
  split.
  - apply ro_cells_frame; [exact G1| lia | lia |]. cbn [cells_size csize Nat.add].
    apply range_apart_of_cs; [exact Ha| exact Hn|]. intros i Hi. exact (proj1 (C2 i Hi)).
  - apply ro_cells_frame; [exact G2| lia | lia |]. cbn [cells_size csize Nat.add].
    apply range_apart_of_cs; [exact Ha| exact Hn|]. intros i Hi. exact (proj2 (C2 i Hi)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition w_client (W : list ivl) : Prop := Forall (fun iv => crange CS (fst iv) (snd iv - fst iv)) W.

#[using="Type"] Lemma outside_of_not_cs : forall W x, w_client W -> ~ CS x -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros x HW Hx; [exact I|].
  inversion HW; subst. split; [| apply IH; assumption].
  cbn in H1. intros Hr. apply Hx. replace x with (lo + (x - lo)) by lia. apply H1. lia.
Qed.

#[using="Type"] Lemma disjoint1_of_not_cs : forall W x, w_client W -> ~ CS x -> disjoint_from W x 1.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros x HW Hx; [exact I|].
  inversion HW; subst. split; [| apply IH; assumption].
  cbn in H1. destruct (Z_lt_le_dec x lo); [left; lia|]. destruct (Z_lt_le_dec x hi); [|right; lia].
  exfalso. apply Hx. apply H1. lia.
Qed.

#[using="CSOK"] Lemma shadow_ok_munch : ltac2:(CDefT.buildp (gd_tbl_AShadow ()) "PW,(16.$2:.)Pm,P,(?.&40.)(14.(?.&8.))Pm',P,(?.&40.)(14.(?.&8.))PA,$1.Pn,$1.P,(2;.R5.)P,(22.VCS,R3.R2.)P,(2<.R7.R6.R5.)P,(25.R7.R5.R4.)(25.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros W m m' A n HW HA MU HS c Hc.
  destruct (HS c Hc) as (k & RD & HK). exists k. split; [|exact HK].
  destruct CSOK as (C1 & _). destruct (C1 c (HA c Hc)) as (R0 & R1 & R2 & NCS).
  eapply bytes_at_transport; [exact RD| exact MU|]. cbn [length Z.of_nat Pos.of_succ_nat].
  apply disjoint1_of_not_cs; assumption.
Qed.

#[using="CSOK"] Lemma aobj_munch : forall W m m' A n,
  w_client W -> munch W m m' -> aobj CS m A n -> aobj CS m' A n.
Proof. intros W m m' A n HW MU [HC HS]. split; [exact HC|]. eapply shadow_ok_munch; eauto. Qed.

#[using="Type"] Lemma disjoint_of_cs : ltac2:(CDefT.buildp (gd_tbl_AShadow ()) "PW,(16.$2:.)PG,$1.P,(2;.R2.)P,(2=.(2>.$1.$1.)Liv,(2>.$1.$1.)(3.(2?.$1.$1.R1.)(30.$1.$1.R1.))R3.)P,Pi,$1.P,(0.(2.=R1.)(3.R1.+8.))(6.A1.VCS,(7.R5.R2.))(31.R5.R4.+8.)")
(* [comment removed for export] *).
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros G HW HL NG; [exact I|].
  inversion HW; subst. inversion HL; subst. cbn in *. split; [| apply IH; assumption].
  pose proof (range_apart_of_cs lo (hi - lo) G H1 ltac:(lia) NG). lia.
Qed.

#[using="CSOK"] Lemma abase_munch : ltac2:(CDefT.buildp (gd_tbl_AShadow ()) "PW,(16.$2:.)Pm,P,(?.&40.)(14.(?.&8.))Pm',P,(?.&40.)(14.(?.&8.))P,(2;.R3.)P,(2=.(2>.$1.$1.)Liv,(2>.$1.$1.)(3.(2?.$1.$1.R1.)(30.$1.$1.R1.))R4.)P,(2<.R5.R4.R3.)P,(29.R5.)(29.R5.)")
(* [comment removed for export] *).
Proof.
  intros W m m' HW HL MU [G1 G2]. destruct CSOK as (_ & C2 & _).
  split.
  - eapply ro_cells_transport; [exact G1| exact MU|]. cbn [cells_size csize Nat.add].
    apply disjoint_of_cs; [assumption| assumption|]. intros i Hi. exact (proj1 (C2 i Hi)).
  - eapply ro_cells_transport; [exact G2| exact MU|]. cbn [cells_size csize Nat.add].
    apply disjoint_of_cs; [assumption| assumption|]. intros i Hi. exact (proj2 (C2 i Hi)).
Qed.

End Frame.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End WithSegs.
