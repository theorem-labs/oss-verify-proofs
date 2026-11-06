(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface AInstanceM AInstanceU.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2 AInstanceU2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require ExhFirst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadPre.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Local Notation AIu2 := (AInstanceU2.AIu2 ExhFirst.exh_first).
Definition IMGX_IMG : list iv := map (fun r => (fst r, snd r - fst r)) aci_I.
Definition IMGX_SH : list iv :=
  [(0x7fffa000, 0x258c); (0x7fffc58c, 0xe0);
   (0x800b7820, 2); (0x800b7822, 0x2006);
   (0x800b9828, 0x158); (0x800b9998, 0x4050); (0x800bd9f0, 0x190); (0x800bdb88, 0x7d); (0x800bdc06, 0xa2)].
Definition IMGX_LIT : list iv := IMGX_IMG ++ IMGX_SH.

Definition lit_ok (v : iv) : bool :=
  (0 <=? snd v) &&
  (existsb (fun r => (fst r <=? fst v) && (fst v + snd v <=? snd r)) aci_I
   || existsb (fun r => (fst r <=? 8 * (fst v - 2147450880)) && (8 * (fst v - 2147450880) + 8 * snd v <=? snd r)) aci_I).
Lemma IMGX_LIT_ok : forallb lit_ok IMGX_LIT = true.
Proof. vm_compute. reflexivity. Qed.

Section Imgx.
Context {rc : runConstT}.

Definition IMGX_A : list iv := IMGX_LIT ++ [(shad ATOP, Shadow.KHIGH - shad ATOP)].

Lemma shad_atop : shad ATOP = 2147450880 + ATOP / 8.
Proof. pose proof atop_range as ATR. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by (clear - ATR; lia). reflexivity. Qed.

Theorem IMGX_A_ok : imgx_ok AIu2 IMGX_A.
Proof.
  intros v Hv. unfold IMGX_A in Hv. apply in_app_or in Hv as [Hv|[<-|[]]].
  - pose proof (proj1 (forallb_forall _ _) IMGX_LIT_ok v Hv) as Q. unfold lit_ok in Q.
    apply andb_prop in Q as [Q0 Q]. apply Z.leb_le in Q0. split; [exact Q0|].
    apply orb_prop in Q as [Q|Q]; apply existsb_exists in Q as (r & Hr & Q); apply andb_prop in Q as [Q1 Q2]; apply Z.leb_le in Q1, Q2.
    + left. exists r. change (aci AIu2) with aci_I. auto.
    + right; left. exists r. change (aci AIu2) with aci_I. unfold ASHOFF. auto.
  - pose proof atop_range as ATR. pose proof ATOP_al16 as A16. cbn [fst snd]. rewrite shad_atop. unfold Shadow.KHIGH, ASHOFF.
    split; [clear - ATR; Z.div_mod_to_equations; lia|]. right; right. clear - ATR A16. Z.div_mod_to_equations; lia.
Qed.

Lemma in_lit : forall v a, In v IMGX_LIT -> in_iv v a -> in_ivs IMGX_A a.
Proof. intros v a Hv Ha. unfold in_ivs, IMGX_A. apply Exists_exists. exists v. split; [apply in_or_app; left; exact Hv| exact Ha]. Qed.
Lemma in_sh : forall v a, In v IMGX_SH -> in_iv v a -> in_ivs IMGX_A a.
Proof. intros v a Hv Ha. apply (in_lit v a); [unfold IMGX_LIT; apply in_or_app; right; exact Hv| exact Ha]. Qed.
Lemma in_aci_img : forall r a, In r aci_I -> fst r <= a < snd r -> in_ivs IMGX_A a.
Proof.
  intros r a Hr Ha. apply (in_lit (fst r, snd r - fst r) a).
  - unfold IMGX_LIT, IMGX_IMG. apply in_or_app. left. apply in_map_iff. exists r. auto.
  - unfold in_iv. cbn [fst snd]. lia.
Qed.

Theorem IMGX_A_stage : forall a, ReadPre.STAGE <= a < ReadPre.STAGE + 65536 -> in_ivs IMGX_A a.
Proof.
  intros a Ha. unfold ReadPre.STAGE in Ha. apply (in_aci_img (0x5fc110, 0x60cc28) a); [| cbn [fst snd]; lia].
  unfold aci_I, AInstanceM.msg_img_ranges. cbn [In]. tauto.
Qed.

Theorem IMGX_A_pool : forall a, 0x60c160 <= a < 0x60c370 -> in_ivs IMGX_A a.
Proof.
  intros a Ha. apply (in_aci_img (0x5fc110, 0x60cc28) a); [| cbn [fst snd]; lia].
  unfold aci_I, AInstanceM.msg_img_ranges. cbn [In]. tauto.
Qed.

Theorem IMGX_A_rs3 : forall a, 0x10000 <= a < 0x10000 + 65536 -> in_ivs IMGX_A a.
Proof.
  intros a Ha. apply (in_aci_img (0x10000, 0x22c60) a); [| cbn [fst snd]; lia].
  unfold aci_I, AInstanceM.msg_img_ranges. cbn [In]. tauto.
Qed.

Theorem IMGX_A_stksh : forall a', ATOP <= a' < 2 ^ 47 -> in_ivs IMGX_A (shad a').
Proof.
  intros a' Ha. pose proof atop_range as ATR. unfold in_ivs, IMGX_A. apply Exists_exists. exists (shad ATOP, Shadow.KHIGH - shad ATOP).
  split; [apply in_or_app; right; left; reflexivity|]. unfold in_iv. cbn [fst snd]. rewrite shad_atop.
  unfold shad, ASHOFF, Shadow.KHIGH. rewrite Z.shiftr_div_pow2 by lia. clear - Ha ATR. Z.div_mod_to_equations; lia.
Qed.

Theorem IMGX_A_shlit : forall v a, In v SHLIT -> fst v <= a < snd v -> in_ivs IMGX_A a.
Proof.
  intros v a Hv Ha. unfold SHLIT, Actr.ActrA.IMGSH, STGSH, PUBSH in Hv. cbn [app In] in Hv.
  destruct Hv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst snd] in Ha.
  - destruct (Z_lt_le_dec a 0x7fffc58c); [apply (in_sh (0x7fffa000, 0x258c) a)| apply (in_sh (0x7fffc58c, 0xe0) a)];
      try (unfold IMGX_SH; cbn [In]; tauto); unfold in_iv; cbn [fst snd]; lia.
  - destruct (Z_lt_le_dec a 0x800b7822); [apply (in_sh (0x800b7820, 2) a)| apply (in_sh (0x800b7822, 0x2006) a)];
      try (unfold IMGX_SH; cbn [In]; tauto); unfold in_iv; cbn [fst snd]; lia.
  - apply (in_sh (0x800b9828, 0x158) a); [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia].
  - apply (in_sh (0x800b9998, 0x4050) a); [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia].
  - apply (in_sh (0x800bd9f0, 0x190) a); [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia].
  - apply (in_sh (0x800bdb88, 0x7d) a); [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia].
  - apply (in_sh (0x800bdc06, 0xa2) a); [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia].
Qed.

Definition sh_aci_b (v : iv) : bool :=
  existsb (fun r => (fst r <=? 8 * (fst v - 2147450880)) && (8 * (fst v - 2147450880) + 8 * snd v <=? snd r)) aci_I.
Lemma IMGX_SH_aci : forallb sh_aci_b IMGX_SH = true.
Proof. vm_compute. reflexivity. Qed.
Theorem IMGSH_aci_A : forall v a, In v SHLIT -> fst v <= a < snd v -> exists a', in_ranges (aci AIu2) a' /\ a = shad a'.
Proof.
  intros v a Hv Ha.
  assert (C : exists w, In w IMGX_SH /\ in_iv w a).
  { unfold SHLIT, Actr.ActrA.IMGSH, STGSH, PUBSH in Hv. cbn [app In] in Hv.
    destruct Hv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst snd] in Ha.
    - destruct (Z_lt_le_dec a 0x7fffc58c); [exists (0x7fffa000, 0x258c)| exists (0x7fffc58c, 0xe0)];
        (split; [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia]).
    - destruct (Z_lt_le_dec a 0x800b7822); [exists (0x800b7820, 2)| exists (0x800b7822, 0x2006)];
        (split; [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia]).
    - exists (0x800b9828, 0x158). split; [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia].
    - exists (0x800b9998, 0x4050). split; [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia].
    - exists (0x800bd9f0, 0x190). split; [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia].
    - exists (0x800bdb88, 0x7d). split; [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia].
    - exists (0x800bdc06, 0xa2). split; [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia]. }
  destruct C as (w & Hw & Hin). unfold in_iv in Hin.
  pose proof (proj1 (forallb_forall _ _) IMGX_SH_aci w Hw) as Q. unfold sh_aci_b in Q.
  apply existsb_exists in Q as (r & Hr & Q). apply andb_prop in Q as [Q1 Q2]. apply Z.leb_le in Q1, Q2.
  exists (8 * (a - ASHOFF)). unfold ASHOFF. split.
  - exists r. change (aci AIu2) with aci_I. split; [exact Hr| lia].
  - symmetry. apply shad_unshad.
Qed.

Lemma ACI_mtx_A : In (0xd7370, 0xd7378) (aci AIu2).   Proof. change (aci AIu2) with aci_I. unfold aci_I, AInstanceM.msg_img_ranges. cbn [In]. tauto. Qed.
Lemma ACI_glob_A : In (0x22c60, 0x23360) (aci AIu2).  Proof. change (aci AIu2) with aci_I. unfold aci_I, AInstanceM.msg_img_ranges. cbn [In]. tauto. Qed.
Lemma ACI_desc_A : In (0xd5e90, 0xd6408) (aci AIu2).  Proof. change (aci AIu2) with aci_I. unfold aci_I, AInstanceM.msg_img_ranges. cbn [In]. tauto. Qed.
Lemma ACI_stage_A : exists iv0, In iv0 (aci AIu2) /\ fst iv0 <= ReadPre.STAGE /\ ReadPre.STAGE + 65536 <= snd iv0.
Proof. exists (0x5fc110, 0x60cc28). change (aci AIu2) with aci_I. unfold aci_I, AInstanceM.msg_img_ranges, ReadPre.STAGE. cbn [In fst snd]. split; [tauto| lia]. Qed.
Lemma ACI_errno_A : exists iv0, In iv0 (aci AIu2) /\ fst iv0 <= ReadPre.ERRNO /\ ReadPre.ERRNO + 4 <= snd iv0.
Proof. exists (0x5fc110, 0x60cc28). change (aci AIu2) with aci_I. unfold aci_I, AInstanceM.msg_img_ranges, ReadPre.ERRNO. cbn [In fst snd]. split; [tauto| lia]. Qed.

Definition sh_lit_b (v : iv) : bool := existsb (fun s => (fst s <=? fst v) && (fst v + snd v <=? snd s)) SHLIT.
Lemma IMGX_SH_lit : forallb sh_lit_b IMGX_SH = true.
Proof. vm_compute. reflexivity. Qed.
Lemma IMGX_IMG_img : forallb (fun v => (0x10000 <=? fst v) && (fst v + snd v <=? 0x62f000)) IMGX_IMG = true.
Proof. vm_compute. reflexivity. Qed.

Theorem IMGX_A_cov : forall v a, In v IMGX_A -> in_iv v a -> C0 a \/ sh_cov a.
Proof.
  intros v a Hv Ha. unfold IMGX_A, IMGX_LIT in Hv. unfold in_iv in Ha.
  apply in_app_or in Hv as [Hv|[<-|[]]]; [apply in_app_or in Hv as [Hv|Hv]|].
  - left. left. pose proof (proj1 (forallb_forall _ _) IMGX_IMG_img v Hv) as Q. apply andb_prop in Q as [Q1 Q2]. apply Z.leb_le in Q1, Q2.
    unfold AIMG_HI. lia.
  - right. right. pose proof (proj1 (forallb_forall _ _) IMGX_SH_lit v Hv) as Q. unfold sh_lit_b in Q.
    apply existsb_exists in Q as (s & Hs & Q). apply andb_prop in Q as [Q1 Q2]. apply Z.leb_le in Q1, Q2. exists s. split; [exact Hs| lia].
  - right. left. pose proof atop_range as ATR. pose proof ATOP_al16 as A16. cbn [fst snd] in Ha. rewrite shad_atop in Ha. unfold Shadow.KHIGH in Ha.
    exists (8 * (a - ASHOFF)). unfold ASHOFF. split; [clear - Ha ATR A16; Z.div_mod_to_equations; lia|]. symmetry. apply shad_unshad.
Qed.
End Imgx.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB AInstanceM.TwinB AInstanceU.TwinB.
Import AMalloc_iface2.TwinB AInstanceU2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import Ledger.TwinB Op.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Local Notation AIu2 := (AInstanceU2.TwinB.AIu2 ExhFirst.TwinB.exh_first).
Definition IMGX_IMG : list iv := map (fun r => (fst r, snd r - fst r)) aci_I.
Definition IMGX_SH : list iv :=
  [(0x7fffa000, 0x25a0); (0x7fffc5a0, 0x100);
   (0x800b7c58, 2); (0x800b7c5a, 0x2006);
   (0x800b9c60, 0x158); (0x800b9dd0, 0x4050); (0x800bde28, 0x190); (0x800bdfc0, 0x7d); (0x800be03e, 0xa2)].
Definition IMGX_LIT : list iv := IMGX_IMG ++ IMGX_SH.

Definition lit_ok (v : iv) : bool :=
  (0 <=? snd v) &&
  (existsb (fun r => (fst r <=? fst v) && (fst v + snd v <=? snd r)) aci_I
   || existsb (fun r => (fst r <=? 8 * (fst v - 2147450880)) && (8 * (fst v - 2147450880) + 8 * snd v <=? snd r)) aci_I).
Lemma IMGX_LIT_ok : forallb lit_ok IMGX_LIT = true.
Proof. vm_compute. reflexivity. Qed.

Section Imgx.
Context {rc : runConstT}.

Definition IMGX_A : list iv := IMGX_LIT ++ [(shad ATOP, Shadow.KHIGH - shad ATOP)].

Lemma shad_atop : shad ATOP = 2147450880 + ATOP / 8.
Proof. pose proof atop_range as ATR. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by (clear - ATR; lia). reflexivity. Qed.

Theorem IMGX_A_ok : imgx_ok AIu2 IMGX_A.
Proof.
  intros v Hv. unfold IMGX_A in Hv. apply in_app_or in Hv as [Hv|[<-|[]]].
  - pose proof (proj1 (forallb_forall _ _) IMGX_LIT_ok v Hv) as Q. unfold lit_ok in Q.
    apply andb_prop in Q as [Q0 Q]. apply Z.leb_le in Q0. split; [exact Q0|].
    apply orb_prop in Q as [Q|Q]; apply existsb_exists in Q as (r & Hr & Q); apply andb_prop in Q as [Q1 Q2]; apply Z.leb_le in Q1, Q2.
    + left. exists r. change (aci AIu2) with aci_I. auto.
    + right; left. exists r. change (aci AIu2) with aci_I. unfold ASHOFF. auto.
  - pose proof atop_range as ATR. pose proof ATOP_al16 as A16. cbn [fst snd]. rewrite shad_atop. unfold Shadow.KHIGH, ASHOFF.
    split; [clear - ATR; Z.div_mod_to_equations; lia|]. right; right. clear - ATR A16. Z.div_mod_to_equations; lia.
Qed.

Lemma in_lit : forall v a, In v IMGX_LIT -> in_iv v a -> in_ivs IMGX_A a.
Proof. intros v a Hv Ha. unfold in_ivs, IMGX_A. apply Exists_exists. exists v. split; [apply in_or_app; left; exact Hv| exact Ha]. Qed.
Lemma in_sh : forall v a, In v IMGX_SH -> in_iv v a -> in_ivs IMGX_A a.
Proof. intros v a Hv Ha. apply (in_lit v a); [unfold IMGX_LIT; apply in_or_app; right; exact Hv| exact Ha]. Qed.
Lemma in_aci_img : forall r a, In r aci_I -> fst r <= a < snd r -> in_ivs IMGX_A a.
Proof.
  intros r a Hr Ha. apply (in_lit (fst r, snd r - fst r) a).
  - unfold IMGX_LIT, IMGX_IMG. apply in_or_app. left. apply in_map_iff. exists r. auto.
  - unfold in_iv. cbn [fst snd]. lia.
Qed.

Theorem IMGX_A_stage : forall a, ReadPre.TwinB.STAGE <= a < ReadPre.TwinB.STAGE + 65536 -> in_ivs IMGX_A a.
Proof.
  intros a Ha. unfold ReadPre.TwinB.STAGE in Ha. apply (in_aci_img (0x5fe2d0, 0x60ede8) a); [| cbn [fst snd]; lia].
  unfold aci_I, AInstanceM.TwinB.msg_img_ranges. cbn [In]. tauto.
Qed.

Theorem IMGX_A_pool : forall a, 0x60e320 <= a < 0x60e530 -> in_ivs IMGX_A a.
Proof.
  intros a Ha. apply (in_aci_img (0x5fe2d0, 0x60ede8) a); [| cbn [fst snd]; lia].
  unfold aci_I, AInstanceM.TwinB.msg_img_ranges. cbn [In]. tauto.
Qed.

Theorem IMGX_A_rs3 : forall a, 0x10000 <= a < 0x10000 + 65536 -> in_ivs IMGX_A a.
Proof.
  intros a Ha. apply (in_aci_img (0x10000, 0x22d00) a); [| cbn [fst snd]; lia].
  unfold aci_I, AInstanceM.TwinB.msg_img_ranges. cbn [In]. tauto.
Qed.

Theorem IMGX_A_stksh : forall a', ATOP <= a' < 2 ^ 47 -> in_ivs IMGX_A (shad a').
Proof.
  intros a' Ha. pose proof atop_range as ATR. unfold in_ivs, IMGX_A. apply Exists_exists. exists (shad ATOP, Shadow.KHIGH - shad ATOP).
  split; [apply in_or_app; right; left; reflexivity|]. unfold in_iv. cbn [fst snd]. rewrite shad_atop.
  unfold shad, ASHOFF, Shadow.KHIGH. rewrite Z.shiftr_div_pow2 by lia. clear - Ha ATR. Z.div_mod_to_equations; lia.
Qed.

Theorem IMGX_A_shlit : forall v a, In v SHLIT -> fst v <= a < snd v -> in_ivs IMGX_A a.
Proof.
  intros v a Hv Ha. unfold SHLIT, Actr.TwinB.ActrA.IMGSH, STGSH, PUBSH in Hv. cbn [app In] in Hv.
  destruct Hv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst snd] in Ha.
  - destruct (Z_lt_le_dec a 0x7fffc5a0); [apply (in_sh (0x7fffa000, 0x25a0) a)| apply (in_sh (0x7fffc5a0, 0x100) a)];
      try (unfold IMGX_SH; cbn [In]; tauto); unfold in_iv; cbn [fst snd]; lia.
  - destruct (Z_lt_le_dec a 0x800b7c5a); [apply (in_sh (0x800b7c58, 2) a)| apply (in_sh (0x800b7c5a, 0x2006) a)];
      try (unfold IMGX_SH; cbn [In]; tauto); unfold in_iv; cbn [fst snd]; lia.
  - apply (in_sh (0x800b9c60, 0x158) a); [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia].
  - apply (in_sh (0x800b9dd0, 0x4050) a); [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia].
  - apply (in_sh (0x800bde28, 0x190) a); [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia].
  - apply (in_sh (0x800bdfc0, 0x7d) a); [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia].
  - apply (in_sh (0x800be03e, 0xa2) a); [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia].
Qed.

Definition sh_aci_b (v : iv) : bool :=
  existsb (fun r => (fst r <=? 8 * (fst v - 2147450880)) && (8 * (fst v - 2147450880) + 8 * snd v <=? snd r)) aci_I.
Lemma IMGX_SH_aci : forallb sh_aci_b IMGX_SH = true.
Proof. vm_compute. reflexivity. Qed.
Theorem IMGSH_aci_A : forall v a, In v SHLIT -> fst v <= a < snd v -> exists a', in_ranges (aci AIu2) a' /\ a = shad a'.
Proof.
  intros v a Hv Ha.
  assert (C : exists w, In w IMGX_SH /\ in_iv w a).
  { unfold SHLIT, Actr.TwinB.ActrA.IMGSH, STGSH, PUBSH in Hv. cbn [app In] in Hv.
    destruct Hv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst snd] in Ha.
    - destruct (Z_lt_le_dec a 0x7fffc5a0); [exists (0x7fffa000, 0x25a0)| exists (0x7fffc5a0, 0x100)];
        (split; [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia]).
    - destruct (Z_lt_le_dec a 0x800b7c5a); [exists (0x800b7c58, 2)| exists (0x800b7c5a, 0x2006)];
        (split; [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia]).
    - exists (0x800b9c60, 0x158). split; [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia].
    - exists (0x800b9dd0, 0x4050). split; [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia].
    - exists (0x800bde28, 0x190). split; [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia].
    - exists (0x800bdfc0, 0x7d). split; [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia].
    - exists (0x800be03e, 0xa2). split; [unfold IMGX_SH; cbn [In]; tauto| unfold in_iv; cbn [fst snd]; lia]. }
  destruct C as (w & Hw & Hin). unfold in_iv in Hin.
  pose proof (proj1 (forallb_forall _ _) IMGX_SH_aci w Hw) as Q. unfold sh_aci_b in Q.
  apply existsb_exists in Q as (r & Hr & Q). apply andb_prop in Q as [Q1 Q2]. apply Z.leb_le in Q1, Q2.
  exists (8 * (a - ASHOFF)). unfold ASHOFF. split.
  - exists r. change (aci AIu2) with aci_I. split; [exact Hr| lia].
  - symmetry. apply shad_unshad.
Qed.

Lemma ACI_mtx_A : In (0xd9530, 0xd9538) (aci AIu2).   Proof. change (aci AIu2) with aci_I. unfold aci_I, AInstanceM.TwinB.msg_img_ranges. cbn [In]. tauto. Qed.
Lemma ACI_glob_A : In (0x22d00, 0x23500) (aci AIu2).  Proof. change (aci AIu2) with aci_I. unfold aci_I, AInstanceM.TwinB.msg_img_ranges. cbn [In]. tauto. Qed.
Lemma ACI_desc_A : In (0xd7fb0, 0xd85c8) (aci AIu2).  Proof. change (aci AIu2) with aci_I. unfold aci_I, AInstanceM.TwinB.msg_img_ranges. cbn [In]. tauto. Qed.
Lemma ACI_stage_A : exists iv0, In iv0 (aci AIu2) /\ fst iv0 <= ReadPre.TwinB.STAGE /\ ReadPre.TwinB.STAGE + 65536 <= snd iv0.
Proof. exists (0x5fe2d0, 0x60ede8). change (aci AIu2) with aci_I. unfold aci_I, AInstanceM.TwinB.msg_img_ranges, ReadPre.TwinB.STAGE. cbn [In fst snd]. split; [tauto| lia]. Qed.
Lemma ACI_errno_A : exists iv0, In iv0 (aci AIu2) /\ fst iv0 <= ReadPre.TwinB.ERRNO /\ ReadPre.TwinB.ERRNO + 4 <= snd iv0.
Proof. exists (0x5fe2d0, 0x60ede8). change (aci AIu2) with aci_I. unfold aci_I, AInstanceM.TwinB.msg_img_ranges, ReadPre.TwinB.ERRNO. cbn [In fst snd]. split; [tauto| lia]. Qed.

Definition sh_lit_b (v : iv) : bool := existsb (fun s => (fst s <=? fst v) && (fst v + snd v <=? snd s)) SHLIT.
Lemma IMGX_SH_lit : forallb sh_lit_b IMGX_SH = true.
Proof. vm_compute. reflexivity. Qed.
Lemma IMGX_IMG_img : forallb (fun v => (0x10000 <=? fst v) && (fst v + snd v <=? 0x631000)) IMGX_IMG = true.
Proof. vm_compute. reflexivity. Qed.

Theorem IMGX_A_cov : forall v a, In v IMGX_A -> in_iv v a -> C0 a \/ sh_cov a.
Proof.
  intros v a Hv Ha. unfold IMGX_A, IMGX_LIT in Hv. unfold in_iv in Ha.
  apply in_app_or in Hv as [Hv|[<-|[]]]; [apply in_app_or in Hv as [Hv|Hv]|].
  - left. left. pose proof (proj1 (forallb_forall _ _) IMGX_IMG_img v Hv) as Q. apply andb_prop in Q as [Q1 Q2]. apply Z.leb_le in Q1, Q2.
    unfold AIMG_HI. lia.
  - right. right. pose proof (proj1 (forallb_forall _ _) IMGX_SH_lit v Hv) as Q. unfold sh_lit_b in Q.
    apply existsb_exists in Q as (s & Hs & Q). apply andb_prop in Q as [Q1 Q2]. apply Z.leb_le in Q1, Q2. exists s. split; [exact Hs| lia].
  - right. left. pose proof atop_range as ATR. pose proof ATOP_al16 as A16. cbn [fst snd] in Ha. rewrite shad_atop in Ha. unfold Shadow.KHIGH in Ha.
    exists (8 * (a - ASHOFF)). unfold ASHOFF. split; [clear - Ha ATR A16; Z.div_mod_to_equations; lia|]. symmetry. apply shad_unshad.
Qed.
End Imgx.
End TwinB.
