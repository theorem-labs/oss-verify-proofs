(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface AInstanceM AInstanceU.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2 AInstanceU2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require ExhFirst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Ops.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.EH Require Pool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require GlueA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadPre ReadPost StackSh LowImg StrReg PubImg GshC GshImg.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import St Ops.
Open Scope Z_scope.
Unset Lia Cache.

Local Notation AIu2 := (AInstanceU2.AIu2 ExhFirst.exh_first).
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.

Section Comps.
Context {rc : runConstT}.

Definition agree_on (fp : list (Z * Z)) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < W64.two64 -> Exists (fun iv => fst iv <= a < snd iv) fp -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a).
Definition no_unmap (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < W64.two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None.

Definition pres_set (a : Z) : Prop :=
  in_ranges (aci AIu2) a \/ (exists a', in_ranges (aci AIu2) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Definition pres2 (a : Z) : Prop := in_ranges (aci AIu2) a \/ (exists a', in_ranges (aci AIu2) a' /\ a = shad a').
Lemma pres2_set : forall a, pres2 a -> pres_set a.
Proof. intros a [H|H]; [left; exact H| right; left; exact H]. Qed.
Definition wb_pres (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < W64.two64 -> pres_set a -> wb asegs m a = true -> wb asegs m' a = true.

Lemma wb_keep : forall m m' a, no_unmap m m' -> wb asegs m a = true -> wb asegs m' a = true.
Proof.
  intros m m' a DM H. apply (GlueA.wb_wviewA asegs). apply (GlueA.wmono_ofA asegs m m' DM). apply (GlueA.wb_wviewA asegs). exact H.
Qed.

Lemma agree_one : forall lo hi m m' a, agree_on [(lo, hi)] m m' -> 0 <= a < W64.two64 -> lo <= a < hi -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a).
Proof. intros lo hi m m' a AG Ha IN. apply AG; [exact Ha|]. apply Exists_cons_hd. cbn [fst snd]. exact IN. Qed.

Lemma unshad : forall a, ASHOFF <= a -> a = shad (8 * (a - ASHOFF)).
Proof. intros a Ha. symmetry. apply shad_unshad. Qed.

Ltac in_aci lo hi := change (aci AIu2) with aci_I; unfold aci_I, AInstanceM.msg_img_ranges, in_ranges; exists (lo, hi); split; [cbn [In]; tauto| cbn [fst snd]; lia].

Definition shmap_c : opcomp.
Proof.
  refine (OpComp (fun _ m _ => UnreggPre.shmap_holds m) (fun _ => []) _).
  intros args m m' mo _ DM H a Ha. exact (wb_keep m m' a DM (H a Ha)).
Defined.
Lemma shmap_pres : forall args m m' mo, oc_holds shmap_c args m mo -> agree_on (oc_fp shmap_c args) m m' -> wb_pres m m' -> oc_holds shmap_c args m' mo.
Proof.
  intros args m m' mo H _ WP a Ha. cbn [oc_holds shmap_c] in H. apply (WP a); [unfold UnreggPre.SH_LO, UnreggPre.SH_HI, UnreggPre.ASH_LO, UnreggPre.ASH_HI, W64.two64 in *; lia| | exact (H a Ha)].
  right; left. exists (8 * (a - ASHOFF)). unfold UnreggPre.SH_LO, UnreggPre.SH_HI, UnreggPre.ASH_LO, UnreggPre.ASH_HI in Ha.
  split; [| apply unshad; unfold ASHOFF; lia]. unfold ASHOFF.
  destruct Ha as [Ha|Ha]; [destruct (Z_lt_le_dec a 0x7fffc66c); [in_aci 0x22c60 0x23360| in_aci 0x23360 0x3b000]| in_aci 0xd5e90 0xd6408].
Qed.

Definition ssh_c : opcomp.
Proof.
  refine (OpComp (fun _ m _ => StackSh.ssh_holds m) (fun _ => []) _).
  intros args m m' mo _ DM H a Ha. exact (wb_keep m m' a DM (H a Ha)).
Defined.
Lemma ssh_pres : forall args m m' mo, oc_holds ssh_c args m mo -> agree_on (oc_fp ssh_c args) m m' -> wb_pres m m' -> oc_holds ssh_c args m' mo.
Proof.
  intros args m m' mo H _ WP a Ha. cbn [oc_holds ssh_c] in H. pose proof atop_range as ATR. pose proof ATOP_al16 as A16.
  assert (KH : Shadow.KHIGH = shad (2 ^ 47)) by reflexivity.
  assert (SA : shad ATOP = ASHOFF + ATOP / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  apply (WP a); [unfold Shadow.KHIGH, W64.two64 in *; rewrite SA in Ha; unfold ASHOFF in *; lia| | exact (H a Ha)].
  right; right. exists (8 * (a - ASHOFF)). rewrite SA in Ha. unfold Shadow.KHIGH, ASHOFF in *.
  split; [Z.div_mod_to_equations; lia| apply unshad; unfold ASHOFF; lia].
Qed.

Definition zro_c : opcomp.
Proof.
  refine (OpComp (fun _ m _ => LowImg.zro_holds m) (fun _ => [(LowImg.ZRO_LO, LowImg.ZRO_HI)]) _).
  intros args m m' mo AG DM H s Hs. destruct (H s Hs) as [Z0 W0]. split; [| exact (wb_keep m m' s DM W0)].
  unfold AM.wa in *. rewrite <- (agree_one _ _ m m' s AG ltac:(unfold LowImg.ZRO_LO, LowImg.ZRO_HI, W64.two64 in *; lia) Hs). exact Z0.
Defined.
Lemma zro_pres : forall args m m' mo, oc_holds zro_c args m mo -> agree_on (oc_fp zro_c args) m m' -> wb_pres m m' -> oc_holds zro_c args m' mo.
Proof.
  intros args m m' mo H AG WP s Hs. cbn [oc_holds zro_c] in H. destruct (H s Hs) as [Z0 W0].
  assert (R : 0 <= s < W64.two64) by (unfold LowImg.ZRO_LO, LowImg.ZRO_HI, W64.two64 in *; lia).
  split; [unfold AM.wa in *; rewrite <- (agree_one _ _ m m' s AG R Hs); exact Z0|].
  apply (WP s R); [| exact W0]. right; left. exists (8 * (s - ASHOFF)). unfold LowImg.ZRO_LO, LowImg.ZRO_HI in Hs.
  split; [unfold ASHOFF; in_aci 0x10000 0x22c60| apply unshad; unfold ASHOFF; lia].
Qed.

Lemma zpbw_aci : forall s, PubImg.in_zpbw s -> 0 <= s < W64.two64 /\ exists a', in_ranges (aci AIu2) a' /\ s = shad a'.
Proof.
  intros s (w & Hw & Hs). unfold PubImg.ZPBW in Hw. cbn [In] in Hw. unfold W64.two64.
  destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hs; (split; [lia|]); exists (8 * (s - ASHOFF)).
  - split; [unfold ASHOFF; in_aci 0x5fc110 0x60cc28| apply unshad; unfold ASHOFF; lia].
  - split; [unfold ASHOFF; in_aci 0x60ccb0 0x62cf40| apply unshad; unfold ASHOFF; lia].
  - split; [unfold ASHOFF; in_aci 0x62cf48 0x62dc18| apply unshad; unfold ASHOFF; lia].
  - split; [unfold ASHOFF; in_aci 0x62dc20 0x62e028| apply unshad; unfold ASHOFF; lia].
  - split; [unfold ASHOFF; in_aci 0x62e030 0x62e560| apply unshad; unfold ASHOFF; lia].
Qed.
Lemma zpbw_fp : forall s, PubImg.in_zpbw s <-> Exists (fun iv => fst iv <= s < snd iv) PubImg.ZPBW.
Proof.
  intros s. split.
  - intros (w & Hw & Hs). apply Exists_exists. exists w. split; assumption.
  - intros H. apply Exists_exists in H as (w & Hw & Hs). exists w. split; assumption.
Qed.
Definition zpb_c : opcomp.
Proof.
  refine (OpComp (fun _ m _ => PubImg.zpb_holds m) (fun _ => PubImg.ZPBW) _).
  intros args m m' mo AG DM H s Hs. destruct (H s Hs) as [Z0 W0]. split; [| exact (wb_keep m m' s DM W0)].
  unfold AM.wa in *. rewrite <- (AG s (proj1 (zpbw_aci s Hs)) (proj1 (zpbw_fp s) Hs)). exact Z0.
Defined.
Lemma zpb_pres : forall args m m' mo, oc_holds zpb_c args m mo -> agree_on (oc_fp zpb_c args) m m' -> wb_pres m m' -> oc_holds zpb_c args m' mo.
Proof.
  intros args m m' mo H AG WP s Hs. cbn [oc_holds zpb_c] in H. destruct (H s Hs) as [Z0 W0].
  destruct (zpbw_aci s Hs) as [R AC].
  split; [unfold AM.wa in *; rewrite <- (AG s R (proj1 (zpbw_fp s) Hs)); exact Z0|].
  apply (WP s R); [| exact W0]. right; left. exact AC.
Qed.

Definition FLA : int := 6340960%uint63.
Lemma FLA8 : to_Z FLA mod 8 = 0. Proof. reflexivity. Qed.
Lemma FLAB : to_Z FLA + 1024 < 2 ^ 62. Proof. reflexivity. Qed.
Lemma pool_agree : forall args (m m' : word -> option byte) (model : Model),
  agree_on (Pool.Pool.pool_fp FLA args) m m' -> Pool.Pool.pool_holds FLA asegs args m model -> Pool.Pool.pool_holds FLA asegs args m' model.
Proof.
  intros args m m' model AG H. unfold agree_on in AG. destruct args as [|sel [|? ?]]; cbn [Pool.Pool.pool_holds] in *; try exact H.
  pose proof (Pool.PoolSnd.HB_val FLA FLAB) as HBv. change (to_Z FLA) with 6340960 in *.
  destruct H as [M|[(s & Hs & Hlt & HF)|(l & Hl & Hlt & HF)]]; [left; exact M| right; left| right; right].
  - exists s. split; [exact Hs|]. split; [exact Hlt|].
    apply Forall_forall. intros e He i Hi. pose proof (proj1 (Forall_forall _ _) HF e He i Hi) as B.
    destruct (Pool.PoolSnd.tbl_facts FLA FLA8 FLAB s e He) as (C1 & C2 & C3 & C4 & C5 & C6 & C7). change (to_Z FLA) with 6340960 in *.
    rewrite <- B. unfold rb. rewrite (AG (to_Z (Pool.Pool.pe_addr e) + i)); [reflexivity| unfold W64.two64; lia|].
    unfold Pool.Pool.pool_fp. rewrite Hs. replace (Z.of_nat s =? 3) with false by (symmetry; apply Z.eqb_neq; unfold Pool.Pool.NSTATES in Hlt; lia).
    replace (Z.of_nat s <? 3) with true by (symmetry; apply Z.ltb_lt; unfold Pool.Pool.NSTATES in Hlt; lia).
    rewrite HBv. change (to_Z FLA) with 6340960. destruct C6 as [C6|C6]; [left; cbn [fst snd]; lia| right; left; cbn [fst snd]; lia].
  - exists l. split; [exact Hl|]. split; [exact Hlt|].
    apply Forall_forall. intros e He i Hi. pose proof (proj1 (Forall_forall _ _) HF e He i Hi) as B.
    destruct (Pool.PoolSnd.ptbl_facts FLA FLA8 FLAB l e He) as (C1 & C2 & C3 & C4 & C5 & C6 & C7). change (to_Z FLA) with 6340960 in *.
    rewrite <- B. unfold rb. rewrite (AG (to_Z (Pool.Pool.pe_addr e) + i)); [reflexivity| unfold W64.two64; lia|].
    unfold Pool.Pool.pool_fp. rewrite Hl. replace (4 + Z.of_nat l =? 3) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (4 + Z.of_nat l <? 3) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite HBv. change (to_Z FLA) with 6340960. destruct C6 as [C6|[C6|C6]]; [left; cbn [fst snd]; lia| right; left; cbn [fst snd]; lia| right; right; left; cbn [fst snd]; lia].
Qed.
Definition pool_c : opcomp := OpComp (Pool.Pool.pool_holds FLA asegs) (Pool.Pool.pool_fp FLA) (fun args m m' mo AG _ H => pool_agree args m m' mo AG H).
Lemma pool_fp_hull : forall args a, Exists (fun iv => fst iv <= a < snd iv) (oc_fp pool_c args) -> 0x60c160 <= a < 0x60c370.
Proof.
  intros args a H. cbn [oc_fp pool_c] in H. unfold Pool.Pool.pool_fp in H. destruct args as [|sel [|? ?]]; try (apply Exists_nil in H; destruct H).
  pose proof (Pool.PoolSnd.HB_val FLA FLAB) as HBv. rewrite HBv in H. change (to_Z FLA) with 6340960 in H.
  destruct (bv_unsigned sel =? 3); [apply Exists_nil in H; destruct H|].
  destruct (bv_unsigned sel <? 3); apply Exists_exists in H as (iv & Hiv & Ha); cbn [In] in Hiv;
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Ha; lia|]); destruct Hiv.
Qed.
Lemma pool_fp_class : forall args a, Exists (fun iv => fst iv <= a < snd iv) (oc_fp pool_c args) -> pres2 a.
Proof. intros args a H. pose proof (pool_fp_hull args a H) as B. left. in_aci 0x5fc110 0x60cc28. Qed.

Lemma gsh_hull : forall s, Exists (fun iv => fst iv <= s < snd iv) (GshImg.gsh_fp GshC.GshC.GSH_TAB_ASAN) -> 0x7fffc58c <= s < 0x7fffc66c.
Proof.
  intros s H. apply Exists_exists in H as (iv & Hiv & Hs).
  assert (C : forallb (fun iv => (0x7fffc58c <=? fst iv) && (snd iv <=? 0x7fffc66c))%bool (GshImg.gsh_fp GshC.GshC.GSH_TAB_ASAN) = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) C iv Hiv) as Q. apply andb_prop in Q as [Q1 Q2]. apply Z.leb_le in Q1, Q2. lia.
Qed.
Lemma gsh_aci : forall s, Exists (fun iv => fst iv <= s < snd iv) (GshImg.gsh_fp GshC.GshC.GSH_TAB_ASAN) ->
  0 <= s < W64.two64 /\ exists a', in_ranges (aci AIu2) a' /\ s = shad a'.
Proof.
  intros s H. pose proof (gsh_hull s H) as B. unfold W64.two64. split; [lia|]. exists (8 * (s - ASHOFF)).
  split; [unfold ASHOFF; in_aci 0x22c60 0x23360| apply unshad; unfold ASHOFF; lia].
Qed.
Lemma gsh_in_fp : forall a n v i, In (a, n, v) GshC.GshC.GSH_TAB_ASAN -> 0 <= i < n ->
  Exists (fun iv => fst iv <= a + i < snd iv) (GshImg.gsh_fp GshC.GshC.GSH_TAB_ASAN).
Proof.
  intros a n v i Hin Hi. apply Exists_exists. exists (a, a + n). split; [| cbn [fst snd]; lia].
  unfold GshImg.gsh_fp. apply in_map_iff. exists (a, n, v). split; [reflexivity| exact Hin].
Qed.
Definition gsh_c : opcomp.
Proof.
  refine (OpComp (fun _ m _ => GshImg.gsh_holds GshC.GshC.GSH_TAB_ASAN m) (fun _ => GshImg.gsh_fp GshC.GshC.GSH_TAB_ASAN) _).
  intros args m m' mo AG DM H a n v Hin i Hi. pose proof (gsh_in_fp a n v i Hin Hi) as FP.
  unfold AM.wa in *. rewrite <- (AG (a + i) (proj1 (gsh_aci _ FP)) FP). exact (H a n v Hin i Hi).
Defined.
Lemma gsh_pres : forall args m m' mo, oc_holds gsh_c args m mo -> agree_on (oc_fp gsh_c args) m m' -> wb_pres m m' -> oc_holds gsh_c args m' mo.
Proof.
  intros args m m' mo H AG WP a n v Hin i Hi. cbn [oc_holds gsh_c] in H. pose proof (gsh_in_fp a n v i Hin Hi) as FP.
  unfold AM.wa in *. rewrite <- (AG (a + i) (proj1 (gsh_aci _ FP)) FP). exact (H a n v Hin i Hi).
Qed.
Lemma gsh_fp_class : forall args a, Exists (fun iv => fst iv <= a < snd iv) (oc_fp gsh_c args) -> pres2 a.
Proof. intros args a H. cbn [oc_fp gsh_c] in H. right. exact (proj2 (gsh_aci a H)). Qed.

Lemma ACI_hull : forall a', 0x5fc100 <= a' < 0x5fc110 -> in_ranges (aci AIu2) a'.
Proof. intros a' H. in_aci 0x5fc100 0x5fc110. Qed.

Definition zsh_c : opcomp.
Proof.
  refine (OpComp (fun _ m _ => ReadPre.zsh_holds m) (fun _ => [(ReadPre.ZSC_LO, ReadPre.ZSC_HI)]) _).
  intros args m m' mo AG DM [HW HZ]. split.
  - intros a Ha. exact (wb_keep m m' a DM (HW a Ha)).
  - intros a Ha. rewrite <- (agree_one _ _ m m' a AG ltac:(unfold ReadPre.ZSC_LO, ReadPre.ZSC_HI, W64.two64 in *; lia) Ha). exact (HZ a Ha).
Defined.
Lemma zsh_pres : forall args m m' mo, oc_holds zsh_c args m mo -> agree_on (oc_fp zsh_c args) m m' -> wb_pres m m' -> oc_holds zsh_c args m' mo.
Proof.
  intros args m m' mo [HW HZ] AG WP. split.
  - intros a Ha. assert (R : 0 <= a < W64.two64) by (unfold ReadPre.ZSH_LO, ReadPre.ZSH_HI, W64.two64 in *; lia).
    apply (WP a R); [| exact (HW a Ha)]. right; left. exists (8 * (a - ASHOFF)). unfold ReadPre.ZSH_LO, ReadPre.ZSH_HI in Ha.
    split; [| apply unshad; unfold ASHOFF; lia]. unfold ASHOFF.
    destruct (Z_lt_ge_dec (8 * (a - 2147450880)) 0x5fc110) as [LT|GE]; [apply ACI_hull; lia| in_aci 0x5fc110 0x60cc28].
  - intros a Ha. rewrite <- (agree_one _ _ m m' a AG ltac:(unfold ReadPre.ZSC_LO, ReadPre.ZSC_HI, W64.two64 in *; lia) Ha). exact (HZ a Ha).
Qed.

Definition zarg_fp (args : list word) : list (Z * Z) :=
  match args with [az] => [(shad (Z.max (bv_unsigned az + 7) ATOP), Shadow.KHIGH)] | _ => [] end.
Definition zarg_holds_c (args : list word) (m : word -> option byte) : Prop :=
  match args with [az] => ATOP <= bv_unsigned az /\ StrReg.zarg_holds az m | _ => False end.
Definition zarg_c : opcomp.
Proof.
  refine (OpComp (fun args m _ => zarg_holds_c args m) zarg_fp _).
  intros args m m' mo AG DM H. destruct args as [|az [|? ?]]; try exact H. cbn [zarg_fp] in AG. cbn [zarg_holds_c] in *.
  destruct H as [LO [B H]]. split; [exact LO|]. split; [exact B|]. intros s Hs. destruct (H s Hs) as [Z0 W0]. split; [| exact (wb_keep m m' s DM W0)].
  rewrite Z.max_l in AG by lia.
  assert (R : 0 <= s < W64.two64).
  { pose proof (bv_unsigned_in_range _ az). unfold shad, Shadow.KHIGH, W64.two64 in *. rewrite Z.shiftr_div_pow2 in Hs by lia. unfold ASHOFF in Hs. Z.div_mod_to_equations; lia. }
  unfold AM.wa in *. rewrite <- (agree_one _ _ m m' s AG R Hs). exact Z0.
Defined.
Lemma zarg_pres : forall args m m' mo, oc_holds zarg_c args m mo -> agree_on (oc_fp zarg_c args) m m' -> wb_pres m m' -> oc_holds zarg_c args m' mo.
Proof.
  intros args m m' mo H AG WP. destruct args as [|az [|? ?]]; try exact H. cbn [oc_holds zarg_c zarg_holds_c] in *. cbn [oc_fp zarg_c zarg_fp] in AG.
  destruct H as [LO [B H]]. split; [exact LO|]. split; [exact B|]. intros s Hs. destruct (H s Hs) as [Z0 W0].
  rewrite Z.max_l in AG by lia. pose proof atop_range as ATR.
  assert (SA : shad (bv_unsigned az + 7) = ASHOFF + (bv_unsigned az + 7) / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (R : 0 <= s < W64.two64) by (rewrite SA in Hs; unfold Shadow.KHIGH, W64.two64, ASHOFF in *; Z.div_mod_to_equations; lia).
  split; [unfold AM.wa in *; rewrite <- (agree_one _ _ m m' s AG R Hs); exact Z0|].
  apply (WP s R); [| exact W0]. right; right. exists (8 * (s - ASHOFF)). rewrite SA in Hs. unfold Shadow.KHIGH, ASHOFF in *.
  split; [Z.div_mod_to_equations; lia| apply unshad; unfold ASHOFF; lia].
Qed.

Variable file : list byte.
Definition rstv_c : opcomp.
Proof.
  refine (OpComp (fun args m _ => ReadPost.rstage_holds_v file args m) (fun _ => [(ReadPre.STAGE, ReadPre.STAGE + 65536)]) _).
  intros args m m' mo AG _ H. destruct args as [|off [|n [|? ?]]]; try exact H. cbn [ReadPost.rstage_holds_v] in *.
  destruct H as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite <- (H3 i Hi). unfold rb.
  rewrite <- (agree_one _ _ m m' (ReadPre.STAGE + i) AG ltac:(unfold ReadPre.STAGE, W64.two64; lia) ltac:(lia)). reflexivity.
Defined.
Lemma rstv_pres : forall args m m' mo, oc_holds rstv_c args m mo -> agree_on (oc_fp rstv_c args) m m' -> wb_pres m m' -> oc_holds rstv_c args m' mo.
Proof.
  intros args m m' mo H AG _. destruct args as [|off [|n [|? ?]]]; try exact H. cbn [oc_holds rstv_c ReadPost.rstage_holds_v] in *.
  destruct H as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite <- (H3 i Hi). unfold rb.
  rewrite <- (agree_one _ _ m m' (ReadPre.STAGE + i) AG ltac:(unfold ReadPre.STAGE, W64.two64; lia) ltac:(lia)). reflexivity.
Qed.

Lemma zro_fp_class : forall args a, Exists (fun iv => fst iv <= a < snd iv) (oc_fp zro_c args) -> pres2 a.
Proof.
  intros args a H. apply Exists_exists in H as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold LowImg.ZRO_LO, LowImg.ZRO_HI in Ha.
  right. exists (8 * (a - ASHOFF)). split; [unfold ASHOFF; in_aci 0x10000 0x22c60| apply unshad; unfold ASHOFF; lia].
Qed.
Lemma zpb_fp_class : forall args a, Exists (fun iv => fst iv <= a < snd iv) (oc_fp zpb_c args) -> pres2 a.
Proof. intros args a H. cbn [oc_fp zpb_c] in H. right. exact (proj2 (zpbw_aci a (proj2 (zpbw_fp a) H))). Qed.
Lemma zsh_fp_class : forall args a, Exists (fun iv => fst iv <= a < snd iv) (oc_fp zsh_c args) -> pres2 a.
Proof.
  intros args a H. apply Exists_exists in H as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold ReadPre.ZSC_LO, ReadPre.ZSC_HI in Ha.
  right. exists (8 * (a - ASHOFF)). split; [unfold ASHOFF; in_aci 0x5fc110 0x60cc28| apply unshad; unfold ASHOFF; lia].
Qed.
Lemma rstv_fp_class : forall args a, Exists (fun iv => fst iv <= a < snd iv) (oc_fp rstv_c args) -> pres2 a.
Proof.
  intros args a H. apply Exists_exists in H as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold ReadPre.STAGE in Ha.
  left. in_aci 0x5fc110 0x60cc28.
Qed.
Lemma zarg_fp_stk : forall args a, Exists (fun iv => fst iv <= a < snd iv) (oc_fp zarg_c args) -> exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a'.
Proof.
  intros args a H. destruct args as [|az [|? ?]]; cbn [oc_fp zarg_c zarg_fp] in H; try (apply Exists_nil in H; destruct H).
  apply Exists_exists in H as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. pose proof atop_range as ATR. pose proof ATOP_al16 as A16.
  set (b := Z.max (bv_unsigned az + 7) ATOP) in *. assert (Bb : ATOP <= b) by (unfold b; lia).
  assert (SA : shad b = ASHOFF + b / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  rewrite SA in Ha. exists (8 * (a - ASHOFF)). unfold Shadow.KHIGH, ASHOFF in *.
  split; [Z.div_mod_to_equations; lia| apply unshad; unfold ASHOFF; lia].
Qed.
Lemma zarg_fp_class : forall args a, Exists (fun iv => fst iv <= a < snd iv) (oc_fp zarg_c args) -> pres_set a.
Proof. intros args a H. right; right. exact (zarg_fp_stk args a H). Qed.

Lemma pres2_not_stk : forall a, pres2 a -> ~ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Proof.
  intros a P (a1 & R1 & E1). pose proof atop_range as ATR.
  assert (S1 : shad a1 = ASHOFF + a1 / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  destruct P as [(iv & Hi & R)|(a2 & (iv & Hi & R) & E2)]; pose proof (AI_aci_img AIu2 iv Hi) as HI; pose proof (AI_aci_lo AIu2 iv Hi) as LO; unfold AIMG_HI in HI.
  - rewrite E1, S1 in R. unfold ASHOFF in R. Z.div_mod_to_equations; lia.
  - assert (S2 : shad a2 = ASHOFF + a2 / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    rewrite E1, S1, S2 in E2. Z.div_mod_to_equations; lia.
Qed.

Lemma zarg_fp_zero : forall args m mo a, oc_holds zarg_c args m mo -> Exists (fun iv => fst iv <= a < snd iv) (oc_fp zarg_c args) -> m (AM.wa a) = Some (Z_to_bv 8 0).
Proof.
  intros args m mo a H E. destruct args as [|az [|? ?]]; try (exfalso; exact H). cbn [oc_holds zarg_c zarg_holds_c] in H. cbn [oc_fp zarg_c zarg_fp] in E.
  destruct H as [LO [_ H]]. rewrite Z.max_l in E by lia. apply Exists_exists in E as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. exact (proj1 (H a Ha)).
Qed.

Definition ext_asan (id : int) : opcomp :=
  if PrimInt63.eqb id 7%uint63 then pool_c
  else if PrimInt63.eqb id 10%uint63 then shmap_c
  else if PrimInt63.eqb id 11%uint63 then zsh_c
  else if PrimInt63.eqb id 12%uint63 then ssh_c
  else if PrimInt63.eqb id 13%uint63 then zro_c
  else if PrimInt63.eqb id 14%uint63 then zarg_c
  else if PrimInt63.eqb id 15%uint63 then rstv_c
  else if PrimInt63.eqb id 16%uint63 then zpb_c
  else if PrimInt63.eqb id 17%uint63 then gsh_c
  else oc_true.
End Comps.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB AInstanceM.TwinB AInstanceU.TwinB.
Import AMalloc_iface2.TwinB AInstanceU2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Ops.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import St Ops.
Open Scope Z_scope.
Unset Lia Cache.

Local Notation AIu2 := (AInstanceU2.TwinB.AIu2 ExhFirst.TwinB.exh_first).
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.

Section Comps.
Context {rc : runConstT}.

Definition agree_on (fp : list (Z * Z)) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < W64.two64 -> Exists (fun iv => fst iv <= a < snd iv) fp -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a).
Definition no_unmap (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < W64.two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None.

Definition pres_set (a : Z) : Prop :=
  in_ranges (aci AIu2) a \/ (exists a', in_ranges (aci AIu2) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Definition pres2 (a : Z) : Prop := in_ranges (aci AIu2) a \/ (exists a', in_ranges (aci AIu2) a' /\ a = shad a').
Lemma pres2_set : forall a, pres2 a -> pres_set a.
Proof. intros a [H|H]; [left; exact H| right; left; exact H]. Qed.
Definition wb_pres (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < W64.two64 -> pres_set a -> wb bsegs m a = true -> wb bsegs m' a = true.

Lemma wb_keep : forall m m' a, no_unmap m m' -> wb bsegs m a = true -> wb bsegs m' a = true.
Proof.
  intros m m' a DM H. apply (GlueA.TwinB.wb_wviewA bsegs). apply (GlueA.TwinB.wmono_ofA bsegs m m' DM). apply (GlueA.TwinB.wb_wviewA bsegs). exact H.
Qed.

Lemma agree_one : forall lo hi m m' a, agree_on [(lo, hi)] m m' -> 0 <= a < W64.two64 -> lo <= a < hi -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a).
Proof. intros lo hi m m' a AG Ha IN. apply AG; [exact Ha|]. apply Exists_cons_hd. cbn [fst snd]. exact IN. Qed.

Lemma unshad : forall a, ASHOFF <= a -> a = shad (8 * (a - ASHOFF)).
Proof. intros a Ha. symmetry. apply shad_unshad. Qed.

Ltac in_aci lo hi := change (aci AIu2) with aci_I; unfold aci_I, AInstanceM.TwinB.msg_img_ranges, in_ranges; exists (lo, hi); split; [cbn [In]; tauto| cbn [fst snd]; lia].

Definition shmap_c : opcomp.
Proof.
  refine (OpComp (fun _ m _ => UnreggPre.TwinB.shmap_holds m) (fun _ => []) _).
  intros args m m' mo _ DM H a Ha. exact (wb_keep m m' a DM (H a Ha)).
Defined.
Lemma shmap_pres : forall args m m' mo, oc_holds shmap_c args m mo -> agree_on (oc_fp shmap_c args) m m' -> wb_pres m m' -> oc_holds shmap_c args m' mo.
Proof.
  intros args m m' mo H _ WP a Ha. cbn [oc_holds shmap_c] in H. apply (WP a); [unfold UnreggPre.TwinB.SH_LO, UnreggPre.TwinB.SH_HI, UnreggPre.TwinB.ASH_LO, UnreggPre.TwinB.ASH_HI, W64.two64 in *; lia| | exact (H a Ha)].
  right; left. exists (8 * (a - ASHOFF)). unfold UnreggPre.TwinB.SH_LO, UnreggPre.TwinB.SH_HI, UnreggPre.TwinB.ASH_LO, UnreggPre.TwinB.ASH_HI in Ha.
  split; [| apply unshad; unfold ASHOFF; lia]. unfold ASHOFF.
  destruct Ha as [Ha|Ha]; [in_aci 0x22d00 0x23500| in_aci 0xd7fb0 0xd85c8].
Qed.

Definition ssh_c : opcomp.
Proof.
  refine (OpComp (fun _ m _ => StackSh.TwinB.ssh_holds m) (fun _ => []) _).
  intros args m m' mo _ DM H a Ha. exact (wb_keep m m' a DM (H a Ha)).
Defined.
Lemma ssh_pres : forall args m m' mo, oc_holds ssh_c args m mo -> agree_on (oc_fp ssh_c args) m m' -> wb_pres m m' -> oc_holds ssh_c args m' mo.
Proof.
  intros args m m' mo H _ WP a Ha. cbn [oc_holds ssh_c] in H. pose proof atop_range as ATR. pose proof ATOP_al16 as A16.
  assert (KH : Shadow.KHIGH = shad (2 ^ 47)) by reflexivity.
  assert (SA : shad ATOP = ASHOFF + ATOP / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  apply (WP a); [unfold Shadow.KHIGH, W64.two64 in *; rewrite SA in Ha; unfold ASHOFF in *; lia| | exact (H a Ha)].
  right; right. exists (8 * (a - ASHOFF)). rewrite SA in Ha. unfold Shadow.KHIGH, ASHOFF in *.
  split; [Z.div_mod_to_equations; lia| apply unshad; unfold ASHOFF; lia].
Qed.

Definition zro_c : opcomp.
Proof.
  refine (OpComp (fun _ m _ => LowImg.TwinB.zro_holds m) (fun _ => [(LowImg.TwinB.ZRO_LO, LowImg.TwinB.ZRO_HI)]) _).
  intros args m m' mo AG DM H s Hs. destruct (H s Hs) as [Z0 W0]. split; [| exact (wb_keep m m' s DM W0)].
  unfold AM.wa in *. rewrite <- (agree_one _ _ m m' s AG ltac:(unfold LowImg.TwinB.ZRO_LO, LowImg.TwinB.ZRO_HI, W64.two64 in *; lia) Hs). exact Z0.
Defined.
Lemma zro_pres : forall args m m' mo, oc_holds zro_c args m mo -> agree_on (oc_fp zro_c args) m m' -> wb_pres m m' -> oc_holds zro_c args m' mo.
Proof.
  intros args m m' mo H AG WP s Hs. cbn [oc_holds zro_c] in H. destruct (H s Hs) as [Z0 W0].
  assert (R : 0 <= s < W64.two64) by (unfold LowImg.TwinB.ZRO_LO, LowImg.TwinB.ZRO_HI, W64.two64 in *; lia).
  split; [unfold AM.wa in *; rewrite <- (agree_one _ _ m m' s AG R Hs); exact Z0|].
  apply (WP s R); [| exact W0]. right; left. exists (8 * (s - ASHOFF)). unfold LowImg.TwinB.ZRO_LO, LowImg.TwinB.ZRO_HI in Hs.
  split; [unfold ASHOFF; in_aci 0x10000 0x22d00| apply unshad; unfold ASHOFF; lia].
Qed.

Lemma zpbw_aci : forall s, PubImg.TwinB.in_zpbw s -> 0 <= s < W64.two64 /\ exists a', in_ranges (aci AIu2) a' /\ s = shad a'.
Proof.
  intros s (w & Hw & Hs). unfold PubImg.TwinB.ZPBW in Hw. cbn [In] in Hw. unfold W64.two64.
  destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hs; (split; [lia|]); exists (8 * (s - ASHOFF)).
  - split; [unfold ASHOFF; in_aci 0x5fe2d0 0x60ede8| apply unshad; unfold ASHOFF; lia].
  - split; [unfold ASHOFF; in_aci 0x60ee70 0x62f100| apply unshad; unfold ASHOFF; lia].
  - split; [unfold ASHOFF; in_aci 0x62f108 0x62fdd8| apply unshad; unfold ASHOFF; lia].
  - split; [unfold ASHOFF; in_aci 0x62fde0 0x6301e8| apply unshad; unfold ASHOFF; lia].
  - split; [unfold ASHOFF; in_aci 0x6301f0 0x630720| apply unshad; unfold ASHOFF; lia].
Qed.
Lemma zpbw_fp : forall s, PubImg.TwinB.in_zpbw s <-> Exists (fun iv => fst iv <= s < snd iv) PubImg.TwinB.ZPBW.
Proof.
  intros s. split.
  - intros (w & Hw & Hs). apply Exists_exists. exists w. split; assumption.
  - intros H. apply Exists_exists in H as (w & Hw & Hs). exists w. split; assumption.
Qed.
Definition zpb_c : opcomp.
Proof.
  refine (OpComp (fun _ m _ => PubImg.TwinB.zpb_holds m) (fun _ => PubImg.TwinB.ZPBW) _).
  intros args m m' mo AG DM H s Hs. destruct (H s Hs) as [Z0 W0]. split; [| exact (wb_keep m m' s DM W0)].
  unfold AM.wa in *. rewrite <- (AG s (proj1 (zpbw_aci s Hs)) (proj1 (zpbw_fp s) Hs)). exact Z0.
Defined.
Lemma zpb_pres : forall args m m' mo, oc_holds zpb_c args m mo -> agree_on (oc_fp zpb_c args) m m' -> wb_pres m m' -> oc_holds zpb_c args m' mo.
Proof.
  intros args m m' mo H AG WP s Hs. cbn [oc_holds zpb_c] in H. destruct (H s Hs) as [Z0 W0].
  destruct (zpbw_aci s Hs) as [R AC].
  split; [unfold AM.wa in *; rewrite <- (AG s R (proj1 (zpbw_fp s) Hs)); exact Z0|].
  apply (WP s R); [| exact W0]. right; left. exact AC.
Qed.

Definition FLA : int := 6349600%uint63.
Lemma FLA8 : to_Z FLA mod 8 = 0. Proof. reflexivity. Qed.
Lemma FLAB : to_Z FLA + 1024 < 2 ^ 62. Proof. reflexivity. Qed.
Lemma pool_agree : forall args (m m' : word -> option byte) (model : Model),
  agree_on (Pool.Pool.pool_fp FLA args) m m' -> Pool.Pool.pool_holds FLA bsegs args m model -> Pool.Pool.pool_holds FLA bsegs args m' model.
Proof.
  intros args m m' model AG H. unfold agree_on in AG. destruct args as [|sel [|? ?]]; cbn [Pool.Pool.pool_holds] in *; try exact H.
  pose proof (Pool.PoolSnd.HB_val FLA FLAB) as HBv. change (to_Z FLA) with 6349600 in *.
  destruct H as [M|[(s & Hs & Hlt & HF)|(l & Hl & Hlt & HF)]]; [left; exact M| right; left| right; right].
  - exists s. split; [exact Hs|]. split; [exact Hlt|].
    apply Forall_forall. intros e He i Hi. pose proof (proj1 (Forall_forall _ _) HF e He i Hi) as B.
    destruct (Pool.PoolSnd.tbl_facts FLA FLA8 FLAB s e He) as (C1 & C2 & C3 & C4 & C5 & C6 & C7). change (to_Z FLA) with 6349600 in *.
    rewrite <- B. unfold rb. rewrite (AG (to_Z (Pool.Pool.pe_addr e) + i)); [reflexivity| unfold W64.two64; lia|].
    unfold Pool.Pool.pool_fp. rewrite Hs. replace (Z.of_nat s =? 3) with false by (symmetry; apply Z.eqb_neq; unfold Pool.Pool.NSTATES in Hlt; lia).
    replace (Z.of_nat s <? 3) with true by (symmetry; apply Z.ltb_lt; unfold Pool.Pool.NSTATES in Hlt; lia).
    rewrite HBv. change (to_Z FLA) with 6349600. destruct C6 as [C6|C6]; [left; cbn [fst snd]; lia| right; left; cbn [fst snd]; lia].
  - exists l. split; [exact Hl|]. split; [exact Hlt|].
    apply Forall_forall. intros e He i Hi. pose proof (proj1 (Forall_forall _ _) HF e He i Hi) as B.
    destruct (Pool.PoolSnd.ptbl_facts FLA FLA8 FLAB l e He) as (C1 & C2 & C3 & C4 & C5 & C6 & C7). change (to_Z FLA) with 6349600 in *.
    rewrite <- B. unfold rb. rewrite (AG (to_Z (Pool.Pool.pe_addr e) + i)); [reflexivity| unfold W64.two64; lia|].
    unfold Pool.Pool.pool_fp. rewrite Hl. replace (4 + Z.of_nat l =? 3) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (4 + Z.of_nat l <? 3) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite HBv. change (to_Z FLA) with 6349600. destruct C6 as [C6|[C6|C6]]; [left; cbn [fst snd]; lia| right; left; cbn [fst snd]; lia| right; right; left; cbn [fst snd]; lia].
Qed.
Definition pool_c : opcomp := OpComp (Pool.Pool.pool_holds FLA bsegs) (Pool.Pool.pool_fp FLA) (fun args m m' mo AG _ H => pool_agree args m m' mo AG H).
Lemma pool_fp_hull : forall args a, Exists (fun iv => fst iv <= a < snd iv) (oc_fp pool_c args) -> 0x60e320 <= a < 0x60e530.
Proof.
  intros args a H. cbn [oc_fp pool_c] in H. unfold Pool.Pool.pool_fp in H. destruct args as [|sel [|? ?]]; try (apply Exists_nil in H; destruct H).
  pose proof (Pool.PoolSnd.HB_val FLA FLAB) as HBv. rewrite HBv in H. change (to_Z FLA) with 6349600 in H.
  destruct (bv_unsigned sel =? 3); [apply Exists_nil in H; destruct H|].
  destruct (bv_unsigned sel <? 3); apply Exists_exists in H as (iv & Hiv & Ha); cbn [In] in Hiv;
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Ha; lia|]); destruct Hiv.
Qed.
Lemma pool_fp_class : forall args a, Exists (fun iv => fst iv <= a < snd iv) (oc_fp pool_c args) -> pres2 a.
Proof. intros args a H. pose proof (pool_fp_hull args a H) as B. left. in_aci 0x5fe2d0 0x60ede8. Qed.

Lemma gsh_hull : forall s, Exists (fun iv => fst iv <= s < snd iv) (GshImg.TwinB.gsh_fp GshC.TwinB.GshC.GSH_TAB_ASAN) -> 0x7fffc5a0 <= s < 0x7fffc6a0.
Proof.
  intros s H. apply Exists_exists in H as (iv & Hiv & Hs).
  assert (C : forallb (fun iv => (0x7fffc5a0 <=? fst iv) && (snd iv <=? 0x7fffc6a0))%bool (GshImg.TwinB.gsh_fp GshC.TwinB.GshC.GSH_TAB_ASAN) = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) C iv Hiv) as Q. apply andb_prop in Q as [Q1 Q2]. apply Z.leb_le in Q1, Q2. lia.
Qed.
Lemma gsh_aci : forall s, Exists (fun iv => fst iv <= s < snd iv) (GshImg.TwinB.gsh_fp GshC.TwinB.GshC.GSH_TAB_ASAN) ->
  0 <= s < W64.two64 /\ exists a', in_ranges (aci AIu2) a' /\ s = shad a'.
Proof.
  intros s H. pose proof (gsh_hull s H) as B. unfold W64.two64. split; [lia|]. exists (8 * (s - ASHOFF)).
  split; [unfold ASHOFF; in_aci 0x22d00 0x23500| apply unshad; unfold ASHOFF; lia].
Qed.
Lemma gsh_in_fp : forall a n v i, In (a, n, v) GshC.TwinB.GshC.GSH_TAB_ASAN -> 0 <= i < n ->
  Exists (fun iv => fst iv <= a + i < snd iv) (GshImg.TwinB.gsh_fp GshC.TwinB.GshC.GSH_TAB_ASAN).
Proof.
  intros a n v i Hin Hi. apply Exists_exists. exists (a, a + n). split; [| cbn [fst snd]; lia].
  unfold GshImg.TwinB.gsh_fp. apply in_map_iff. exists (a, n, v). split; [reflexivity| exact Hin].
Qed.
Definition gsh_c : opcomp.
Proof.
  refine (OpComp (fun _ m _ => GshImg.TwinB.gsh_holds GshC.TwinB.GshC.GSH_TAB_ASAN m) (fun _ => GshImg.TwinB.gsh_fp GshC.TwinB.GshC.GSH_TAB_ASAN) _).
  intros args m m' mo AG DM H a n v Hin i Hi. pose proof (gsh_in_fp a n v i Hin Hi) as FP.
  unfold AM.wa in *. rewrite <- (AG (a + i) (proj1 (gsh_aci _ FP)) FP). exact (H a n v Hin i Hi).
Defined.
Lemma gsh_pres : forall args m m' mo, oc_holds gsh_c args m mo -> agree_on (oc_fp gsh_c args) m m' -> wb_pres m m' -> oc_holds gsh_c args m' mo.
Proof.
  intros args m m' mo H AG WP a n v Hin i Hi. cbn [oc_holds gsh_c] in H. pose proof (gsh_in_fp a n v i Hin Hi) as FP.
  unfold AM.wa in *. rewrite <- (AG (a + i) (proj1 (gsh_aci _ FP)) FP). exact (H a n v Hin i Hi).
Qed.
Lemma gsh_fp_class : forall args a, Exists (fun iv => fst iv <= a < snd iv) (oc_fp gsh_c args) -> pres2 a.
Proof. intros args a H. cbn [oc_fp gsh_c] in H. right. exact (proj2 (gsh_aci a H)). Qed.

Lemma ACI_hull : forall a', 0x5fe2c0 <= a' < 0x5fe2d0 -> in_ranges (aci AIu2) a'.
Proof. intros a' H. in_aci 0x5fe2c0 0x5fe2d0. Qed.

Definition zsh_c : opcomp.
Proof.
  refine (OpComp (fun _ m _ => ReadPre.TwinB.zsh_holds m) (fun _ => [(ReadPre.TwinB.ZSC_LO, ReadPre.TwinB.ZSC_HI)]) _).
  intros args m m' mo AG DM [HW HZ]. split.
  - intros a Ha. exact (wb_keep m m' a DM (HW a Ha)).
  - intros a Ha. rewrite <- (agree_one _ _ m m' a AG ltac:(unfold ReadPre.TwinB.ZSC_LO, ReadPre.TwinB.ZSC_HI, W64.two64 in *; lia) Ha). exact (HZ a Ha).
Defined.
Lemma zsh_pres : forall args m m' mo, oc_holds zsh_c args m mo -> agree_on (oc_fp zsh_c args) m m' -> wb_pres m m' -> oc_holds zsh_c args m' mo.
Proof.
  intros args m m' mo [HW HZ] AG WP. split.
  - intros a Ha. assert (R : 0 <= a < W64.two64) by (unfold ReadPre.TwinB.ZSH_LO, ReadPre.TwinB.ZSH_HI, W64.two64 in *; lia).
    apply (WP a R); [| exact (HW a Ha)]. right; left. exists (8 * (a - ASHOFF)). unfold ReadPre.TwinB.ZSH_LO, ReadPre.TwinB.ZSH_HI in Ha.
    split; [| apply unshad; unfold ASHOFF; lia]. unfold ASHOFF.
    destruct (Z_lt_ge_dec (8 * (a - 2147450880)) 0x5fe2d0) as [LT|GE]; [apply ACI_hull; lia| in_aci 0x5fe2d0 0x60ede8].
  - intros a Ha. rewrite <- (agree_one _ _ m m' a AG ltac:(unfold ReadPre.TwinB.ZSC_LO, ReadPre.TwinB.ZSC_HI, W64.two64 in *; lia) Ha). exact (HZ a Ha).
Qed.

Definition zarg_fp (args : list word) : list (Z * Z) :=
  match args with [az] => [(shad (Z.max (bv_unsigned az + 7) ATOP), Shadow.KHIGH)] | _ => [] end.
Definition zarg_holds_c (args : list word) (m : word -> option byte) : Prop :=
  match args with [az] => ATOP <= bv_unsigned az /\ StrReg.TwinB.zarg_holds az m | _ => False end.
Definition zarg_c : opcomp.
Proof.
  refine (OpComp (fun args m _ => zarg_holds_c args m) zarg_fp _).
  intros args m m' mo AG DM H. destruct args as [|az [|? ?]]; try exact H. cbn [zarg_fp] in AG. cbn [zarg_holds_c] in *.
  destruct H as [LO [B H]]. split; [exact LO|]. split; [exact B|]. intros s Hs. destruct (H s Hs) as [Z0 W0]. split; [| exact (wb_keep m m' s DM W0)].
  rewrite Z.max_l in AG by lia.
  assert (R : 0 <= s < W64.two64).
  { pose proof (bv_unsigned_in_range _ az). unfold shad, Shadow.KHIGH, W64.two64 in *. rewrite Z.shiftr_div_pow2 in Hs by lia. unfold ASHOFF in Hs. Z.div_mod_to_equations; lia. }
  unfold AM.wa in *. rewrite <- (agree_one _ _ m m' s AG R Hs). exact Z0.
Defined.
Lemma zarg_pres : forall args m m' mo, oc_holds zarg_c args m mo -> agree_on (oc_fp zarg_c args) m m' -> wb_pres m m' -> oc_holds zarg_c args m' mo.
Proof.
  intros args m m' mo H AG WP. destruct args as [|az [|? ?]]; try exact H. cbn [oc_holds zarg_c zarg_holds_c] in *. cbn [oc_fp zarg_c zarg_fp] in AG.
  destruct H as [LO [B H]]. split; [exact LO|]. split; [exact B|]. intros s Hs. destruct (H s Hs) as [Z0 W0].
  rewrite Z.max_l in AG by lia. pose proof atop_range as ATR.
  assert (SA : shad (bv_unsigned az + 7) = ASHOFF + (bv_unsigned az + 7) / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (R : 0 <= s < W64.two64) by (rewrite SA in Hs; unfold Shadow.KHIGH, W64.two64, ASHOFF in *; Z.div_mod_to_equations; lia).
  split; [unfold AM.wa in *; rewrite <- (agree_one _ _ m m' s AG R Hs); exact Z0|].
  apply (WP s R); [| exact W0]. right; right. exists (8 * (s - ASHOFF)). rewrite SA in Hs. unfold Shadow.KHIGH, ASHOFF in *.
  split; [Z.div_mod_to_equations; lia| apply unshad; unfold ASHOFF; lia].
Qed.

Variable file : list byte.
Definition rstv_c : opcomp.
Proof.
  refine (OpComp (fun args m _ => ReadPost.TwinB.rstage_holds_v file args m) (fun _ => [(ReadPre.TwinB.STAGE, ReadPre.TwinB.STAGE + 65536)]) _).
  intros args m m' mo AG _ H. destruct args as [|off [|n [|? ?]]]; try exact H. cbn [ReadPost.TwinB.rstage_holds_v] in *.
  destruct H as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite <- (H3 i Hi). unfold rb.
  rewrite <- (agree_one _ _ m m' (ReadPre.TwinB.STAGE + i) AG ltac:(unfold ReadPre.TwinB.STAGE, W64.two64; lia) ltac:(lia)). reflexivity.
Defined.
Lemma rstv_pres : forall args m m' mo, oc_holds rstv_c args m mo -> agree_on (oc_fp rstv_c args) m m' -> wb_pres m m' -> oc_holds rstv_c args m' mo.
Proof.
  intros args m m' mo H AG _. destruct args as [|off [|n [|? ?]]]; try exact H. cbn [oc_holds rstv_c ReadPost.TwinB.rstage_holds_v] in *.
  destruct H as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite <- (H3 i Hi). unfold rb.
  rewrite <- (agree_one _ _ m m' (ReadPre.TwinB.STAGE + i) AG ltac:(unfold ReadPre.TwinB.STAGE, W64.two64; lia) ltac:(lia)). reflexivity.
Qed.

Lemma zro_fp_class : forall args a, Exists (fun iv => fst iv <= a < snd iv) (oc_fp zro_c args) -> pres2 a.
Proof.
  intros args a H. apply Exists_exists in H as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold LowImg.TwinB.ZRO_LO, LowImg.TwinB.ZRO_HI in Ha.
  right. exists (8 * (a - ASHOFF)). split; [unfold ASHOFF; in_aci 0x10000 0x22d00| apply unshad; unfold ASHOFF; lia].
Qed.
Lemma zpb_fp_class : forall args a, Exists (fun iv => fst iv <= a < snd iv) (oc_fp zpb_c args) -> pres2 a.
Proof. intros args a H. cbn [oc_fp zpb_c] in H. right. exact (proj2 (zpbw_aci a (proj2 (zpbw_fp a) H))). Qed.
Lemma zsh_fp_class : forall args a, Exists (fun iv => fst iv <= a < snd iv) (oc_fp zsh_c args) -> pres2 a.
Proof.
  intros args a H. apply Exists_exists in H as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold ReadPre.TwinB.ZSC_LO, ReadPre.TwinB.ZSC_HI in Ha.
  right. exists (8 * (a - ASHOFF)). split; [unfold ASHOFF; in_aci 0x5fe2d0 0x60ede8| apply unshad; unfold ASHOFF; lia].
Qed.
Lemma rstv_fp_class : forall args a, Exists (fun iv => fst iv <= a < snd iv) (oc_fp rstv_c args) -> pres2 a.
Proof.
  intros args a H. apply Exists_exists in H as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold ReadPre.TwinB.STAGE in Ha.
  left. in_aci 0x5fe2d0 0x60ede8.
Qed.
Lemma zarg_fp_stk : forall args a, Exists (fun iv => fst iv <= a < snd iv) (oc_fp zarg_c args) -> exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a'.
Proof.
  intros args a H. destruct args as [|az [|? ?]]; cbn [oc_fp zarg_c zarg_fp] in H; try (apply Exists_nil in H; destruct H).
  apply Exists_exists in H as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. pose proof atop_range as ATR. pose proof ATOP_al16 as A16.
  set (b := Z.max (bv_unsigned az + 7) ATOP) in *. assert (Bb : ATOP <= b) by (unfold b; lia).
  assert (SA : shad b = ASHOFF + b / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  rewrite SA in Ha. exists (8 * (a - ASHOFF)). unfold Shadow.KHIGH, ASHOFF in *.
  split; [Z.div_mod_to_equations; lia| apply unshad; unfold ASHOFF; lia].
Qed.
Lemma zarg_fp_class : forall args a, Exists (fun iv => fst iv <= a < snd iv) (oc_fp zarg_c args) -> pres_set a.
Proof. intros args a H. right; right. exact (zarg_fp_stk args a H). Qed.

Lemma pres2_not_stk : forall a, pres2 a -> ~ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Proof.
  intros a P (a1 & R1 & E1). pose proof atop_range as ATR.
  assert (S1 : shad a1 = ASHOFF + a1 / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  destruct P as [(iv & Hi & R)|(a2 & (iv & Hi & R) & E2)]; pose proof (AI_aci_img AIu2 iv Hi) as HI; pose proof (AI_aci_lo AIu2 iv Hi) as LO; unfold AIMG_HI in HI.
  - rewrite E1, S1 in R. unfold ASHOFF in R. Z.div_mod_to_equations; lia.
  - assert (S2 : shad a2 = ASHOFF + a2 / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    rewrite E1, S1, S2 in E2. Z.div_mod_to_equations; lia.
Qed.

Lemma zarg_fp_zero : forall args m mo a, oc_holds zarg_c args m mo -> Exists (fun iv => fst iv <= a < snd iv) (oc_fp zarg_c args) -> m (AM.wa a) = Some (Z_to_bv 8 0).
Proof.
  intros args m mo a H E. destruct args as [|az [|? ?]]; try (exfalso; exact H). cbn [oc_holds zarg_c zarg_holds_c] in H. cbn [oc_fp zarg_c zarg_fp] in E.
  destruct H as [LO [_ H]]. rewrite Z.max_l in E by lia. apply Exists_exists in E as (iv & [<-|[]] & Ha). cbn [fst snd] in Ha. exact (proj1 (H a Ha)).
Qed.

Definition ext_asan (id : int) : opcomp :=
  if PrimInt63.eqb id 7%uint63 then pool_c
  else if PrimInt63.eqb id 10%uint63 then shmap_c
  else if PrimInt63.eqb id 11%uint63 then zsh_c
  else if PrimInt63.eqb id 12%uint63 then ssh_c
  else if PrimInt63.eqb id 13%uint63 then zro_c
  else if PrimInt63.eqb id 14%uint63 then zarg_c
  else if PrimInt63.eqb id 15%uint63 then rstv_c
  else if PrimInt63.eqb id 16%uint63 then zpb_c
  else if PrimInt63.eqb id 17%uint63 then gsh_c
  else oc_true.
End Comps.
End TwinB.
