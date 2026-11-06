(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlanSoundSums SegRun BigLinkBase BigLinkGlue BigModel BigFactsRun BigFactsDigits L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5ParseSpecsAB0 L5OpmodSpecsAB0 L5BCopyS L5BDetailG L5BFrameK L5DivSpecsAB0 L5UnwindSpecsAB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ATX.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition in_rngsb (W : list L5.range) (a : Z) : bool := existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) W.
Lemma in_rngsb_false W a : in_rngsb W a = false -> L5.outside W a.
Proof.
  unfold in_rngsb. intros E r Hr [X1 X2]. assert (T : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) W = true).
  { apply existsb_exists. exists r. split. exact Hr. apply andb_true_intro. split. apply Z.leb_le; exact X1. apply Z.ltb_lt; exact X2. }
  rewrite T in E. discriminate E.
Qed.
Definition rebase (W : list L5.range) (M Mc : word -> option byte) : word -> option byte :=
  fun w => if in_rngsb W (bv_unsigned w) then Mc w else M w.
Lemma rebase_at W M Mc a : 0 <= a < 2 ^ 64 -> rebase W M Mc (Z_to_bv 64 a) = if in_rngsb W a then Mc (Z_to_bv 64 a) else M (Z_to_bv 64 a).
Proof. intros Ha. unfold rebase. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by exact Ha. reflexivity. Qed.
Lemma rebase_out W M Mc a : 0 <= a < 2 ^ 64 -> (forall r, In r W -> ~ L5.in_rng r a) -> rebase W M Mc (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros Ha HO. rewrite rebase_at by exact Ha. destruct (in_rngsb W a) eqn:E. 2: reflexivity. exfalso.
  unfold in_rngsb in E. apply existsb_exists in E. destruct E as (r & Hr & X). apply andb_prop in X. destruct X as [X1 X2].
  apply (HO r Hr). split. apply Z.leb_le; exact X1. apply Z.ltb_lt; exact X2.
Qed.
Lemma rebase_in W M Mc a r : 0 <= a < 2 ^ 64 -> In r W -> L5.in_rng r a -> rebase W M Mc (Z_to_bv 64 a) = Mc (Z_to_bv 64 a).
Proof.
  intros Ha Hr X. rewrite rebase_at by exact Ha. replace (in_rngsb W a) with true. reflexivity. symmetry. unfold in_rngsb. apply existsb_exists. exists r. split. exact Hr.
  destruct X as [X1 X2]. apply andb_true_intro. split. apply Z.leb_le; exact X1. apply Z.ltb_lt; exact X2.
Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis Hdel : opdel_sized_spec L ar HI.

(* [comment removed for export] *)
Lemma ek_rebase LB FF sp scr W M Mc : ek L ar LB FF sp scr W M Mc -> ek L ar LB FF sp scr [] (rebase W M Mc) Mc.
Proof.
  intros E a (Ha & Hc & _). rewrite rebase_at by exact Ha. destruct (in_rngsb W a) eqn:X. reflexivity.
  apply E. split. exact Ha. split. exact Hc. apply in_rngsb_false. exact X.
Qed.
Lemma dk_rebase LB FF sp scr W M Mc : dk L ar LB FF sp scr M Mc -> dk L ar LB FF sp scr (rebase W M Mc) Mc.
Proof. intros D a Ha Hc. rewrite rebase_at by exact Ha. destruct (in_rngsb W a). intros X; exact X. apply D. exact Ha. exact Hc. Qed.
Lemma ahpres_rebase LB FF sp scr W1 W2 M Mc Mf :
  ahpres L ar LB FF sp scr W2 (rebase W1 M Mc) Mf -> dk L ar LB FF sp scr M Mc -> ahpres L ar LB FF sp scr (W2 ++ W1) M Mf.
Proof.
  intros (P & D & K) DK. split. 2: split. 2: exact D.
  - intros a (Ha & Hc & Ho). rewrite (P a). apply rebase_out. exact Ha. intros r Hr. apply Ho. apply in_or_app. right; exact Hr.
    split. exact Ha. split. exact Hc. intros r Hr. apply Ho. apply in_or_app. left; exact Hr.
  - intros a Ha Hc HM. apply K. exact Ha. exact Hc. rewrite rebase_at by exact Ha. destruct (in_rngsb W1 a). apply DK. exact Ha. exact Hc. exact HM. exact HM.
Qed.

Lemma ahpres_W LB FF sp scr W W' M Mf : ahpres L ar LB FF sp scr W M Mf -> (forall a, L5.outside W' a -> L5.outside W a) -> ahpres L ar LB FF sp scr W' M Mf.
Proof. intros (P & D & K) HW. split. 2: split. 2: exact D. 2: exact K. intros a (Ha & Hc & Ho). apply P. split. exact Ha. split. exact Hc. apply HW. exact Ho. Qed.
(* [comment removed for export] *)
Lemma stksh_rebase W M Mc lo : L5OMA.stksh ar M lo -> 0 <= lo -> Z.max (ar_sptop ar) (ar_stack_top ar) <= 2 ^ 47 -> (forall r, In r W -> fst r + snd r <= 2147450880) -> L5OMA.stksh ar (rebase W M Mc) lo.
Proof.
  intros H Hlo HT HW j Hj. unfold byte_at. rewrite rebase_out. apply H. exact Hj.
  - unfold HeapIfaceA.S, SB. pose proof (Z.div_pos lo 8 Hlo ltac:(lia)). assert ((Z.max (ar_sptop ar) (ar_stack_top ar) - lo) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with 17592186044416 in H1.
    assert (lo / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with 17592186044416 in H2. lia.
  - intros r Hr [X1 X2]. pose proof (HW r Hr). unfold HeapIfaceA.S, SB in X2. pose proof (Z.div_pos lo 8 Hlo ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rd1 (M : word -> option byte) (a : word) : seg_rom RSEGS a <> None -> exists b, (match M a with Some b => Some b | None => seg_rom RSEGS a end) = Some b.
Proof. intros H. destruct (M a) as [b|]. exists b; reflexivity. destruct (seg_rom RSEGS a) as [b|]. exists b; reflexivity. exfalso; apply H; reflexivity. Qed.
Lemma errno_readable (M : word -> option byte) : exists e, L5.u32_at RSEGS M L5USA.ERRNO e /\ 0 <= e < 2 ^ 64.
Proof.
  unfold L5USA.ERRNO, L5.u32_at. cbn [rdn].
  destruct (rd1 M (Z_to_bv 64 6363236) ltac:(vm_compute; discriminate)) as [b0 E0]. rewrite E0.
  destruct (rd1 M (Z_to_bv 64 6363236 + 1)%bv ltac:(vm_compute; discriminate)) as [b1 E1]. rewrite E1.
  destruct (rd1 M (Z_to_bv 64 6363236 + 1 + 1)%bv ltac:(vm_compute; discriminate)) as [b2 E2]. rewrite E2.
  destruct (rd1 M (Z_to_bv 64 6363236 + 1 + 1 + 1)%bv ltac:(vm_compute; discriminate)) as [b3 E3]. rewrite E3.
  exists (BvBase.bytes_le_to_Z [b0; b1; b2; b3]). split.
  - f_equal. symmetry. apply (APSX.word_to_le_bytes_of_bytes_n 4 [b0; b1; b2; b3]). reflexivity. Lia.lia.
  - pose proof (AX2S.bytes_le_to_Z_bound [b0; b1; b2; b3]) as X. cbn [length] in X. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in X. Lia.lia.
Qed.
(* [comment removed for export] *)
Definition xs_cell (a : Z) : Prop := (exists r, In r (L5USA.UNW_STATICS ++ L5USA.UNW_CONSTS) /\ fst r <= a < fst r + snd r) /\ ~ (6363236 <= a < 6363240).
Section XFER.
Variables (Ma Mb : word -> option byte) (EXC : Z -> Prop).
Hypothesis AGC : forall a, xs_cell a -> ~ EXC a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a).
Hypothesis AGT : forall a, ar_sptop ar <= a < 2 ^ 47 -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a).
Hypothesis AGI : L5.img_clear Ma 0x10000 0xd8000 -> L5.img_clear Mb 0x10000 0xd8000.
Lemma xfer_agr r a : In r (L5USA.UNW_STATICS ++ L5USA.UNW_CONSTS) -> fst r <= a < fst r + snd r -> ~ (6363236 <= a < 6363240) -> ~ EXC a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a).
Proof. intros Hr Ha NE NC. apply AGC. split. exists r. split. exact Hr. exact Ha. exact NE. exact NC. Qed.
Lemma xfer_u64 r a v : In r (L5USA.UNW_STATICS ++ L5USA.UNW_CONSTS) -> fst r <= a -> a + 8 <= fst r + snd r -> (a + 8 <= 6363236 \/ 6363240 <= a) -> (forall i, a <= i < a + 8 -> ~ EXC i) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  L5.u64_at RSEGS Ma a v -> L5.u64_at RSEGS Mb a v.
Proof. intros Hr H1 H2 H3 HX H4 H5 X. apply (L5C.u64_at_agree RSEGS Ma Mb a v). 2: exact H4. 2: exact H5. 2: exact X. intros i Hi. apply (xfer_agr r i Hr). clear - Hi H1 H2; lia. clear - Hi H3; lia. exact (HX i Hi). Qed.
Lemma xfer_u8 r a v : In r (L5USA.UNW_STATICS ++ L5USA.UNW_CONSTS) -> fst r <= a -> a + 1 <= fst r + snd r -> (a + 1 <= 6363236 \/ 6363240 <= a) -> ~ EXC a -> 0 <= a -> a + 1 <= 2 ^ 64 ->
  L5.u8_at RSEGS Ma a v -> L5.u8_at RSEGS Mb a v.
Proof. intros Hr H1 H2 H3 HX H4 H5 X. apply (L5C.u8_at_agree RSEGS Ma Mb a v). 2: exact H4. 2: exact H5. 2: exact X. intros i Hi. apply (xfer_agr r i Hr). clear - Hi H1 H2; lia. clear - Hi H3; lia. replace i with a by (clear - Hi; lia). exact HX. Qed.
Hypothesis EXCR : forall a, EXC a -> 6360520 <= a < 6360532.       (* [comment removed for export] *)
Lemma xfer_guard gd : L5USA.syscat_guard Ma gd -> L5USA.syscat_guard Mb gd.
Proof.
  intros (G0 & G1). unfold L5USA.syscat_guard, L5USA.SYSCAT_GUARD in *. split.
  - apply (xfer_u8 (6361072, 8) 6361072 _ ltac:(right; left; reflexivity)); cbn [fst snd]; try Lia.lia. intros X; apply EXCR in X; Lia.lia. exact G0.
  - apply (xfer_u8 (6361072, 8) (6361072 + 1) _ ltac:(right; left; reflexivity)); cbn [fst snd]; try Lia.lia. intros X; apply EXCR in X; Lia.lia. exact G1.
Qed.
Lemma xfer_flags fl : L5USA.uw_flags Ma fl -> L5USA.uw_flags Mb fl.
Proof.
  unfold L5USA.uw_flags, L5USA.UW_FLAGS. destruct fl.
  - intros (F0 & F1 & F2 & F3 & F4 & F5). repeat split; (eapply (xfer_u8 (6363185, 6) _ _ ltac:(right; right; left; reflexivity)); [| | | | | | eassumption]; cbn [fst snd]; try Lia.lia; intros X; apply EXCR in X; Lia.lia).
  - intros (F0 & F2 & F4). repeat split; (eapply (xfer_u8 (6363185, 6) _ _ ltac:(right; right; left; reflexivity)); [| | | | | | eassumption]; cbn [fst snd]; try Lia.lia; intros X; apply EXCR in X; Lia.lia).
Qed.
Lemma xfer_const av uid rnd canary hw : ar_sptop ar <= av -> L5USA.statics_const Ma av uid rnd canary hw -> L5USA.statics_const Mb av uid rnd canary hw.
Proof.
  intros AVS. unfold L5USA.statics_const, L5USA.TD_LOCALE, L5USA.GLOBAL_LOCALE, L5USA.LOCALE_MSGCAT, L5USA.CANARY, L5USA.AUXVP, L5USA.SYSCAT_OBJ.
  intros (TDL & MSG & _ & CAN & AUXP & AV8 & AVLO & AVHI & AUXV & UIDR & RNDR & CANR & HWR & I1 & I2 & I3).
  assert (NX : forall lo i, lo <= i -> 6360532 <= lo \/ i < 6360520 -> ~ EXC i) by (intros lo i H1 H2 X; apply EXCR in X; clear - H1 H2 X; Lia.lia).
  split. { apply (xfer_u64 (0x6118d8, 8) _ _ ltac:(apply in_or_app; right; right; right; left; reflexivity)); cbn [fst snd]; try Lia.lia. intros i Hi; apply (NX 0x6118d8); Lia.lia. exact TDL. }
  split. { apply (xfer_u64 (0x631bf8, 8) _ _ ltac:(apply in_or_app; right; right; right; right; left; reflexivity)); cbn [fst snd]; try Lia.lia. intros i Hi; apply (NX 0x631bf8); Lia.lia. exact MSG. }
  split. exact (errno_readable Mb).
  split. { apply (xfer_u64 (0x631948, 8) _ _ ltac:(apply in_or_app; right; do 4 right; left; reflexivity)); cbn [fst snd]; try Lia.lia. intros i Hi; apply (NX 0x631948); Lia.lia. exact CAN. }
  split. { apply (xfer_u64 (0x631ba0, 8) _ _ ltac:(apply in_or_app; right; do 5 right; left; reflexivity)); cbn [fst snd]; try Lia.lia. intros i Hi; apply (NX 0x631ba0); Lia.lia. exact AUXP. }
  split. exact AV8. split. exact AVLO. split. exact AVHI.
  split. { intros j Hj. apply (L5C.u64_at_agree RSEGS Ma Mb). 4: exact (AUXV j Hj). 2: clear - AVLO; lia. 2: clear - AVHI Hj; lia.
           intros i Hi. apply AGT. clear - Hi AVS AVHI Hj; lia. }
  split. exact UIDR. split. exact RNDR. split. exact CANR. split. exact HWR.
  split. exact (AGI I1).
  split. { intros i Hi. rewrite (xfer_agr (0xdab50, 32) i ltac:(apply in_or_app; right; left; reflexivity)). exact (I2 i Hi). cbn [fst snd]; clear - Hi; lia. clear - Hi; lia. apply (NX 0); clear - Hi; lia. }
  intros i Hi. rewrite (xfer_agr (0xdab80, 8) i ltac:(apply in_or_app; right; right; left; reflexivity)). exact (I3 i Hi). cbn [fst snd]; clear - Hi; lia. clear - Hi; lia. apply (NX 0); clear - Hi; lia.
Qed.
(* [comment removed for export] *)
Lemma statics_xfer gd av uid rnd canary hw :
  L5USA.statics_landed Ma gd av uid rnd canary hw -> ar_sptop ar <= av ->
  L5.u64_at RSEGS Mb L5USA.EH_CAUGHT 0 -> L5.u32_at RSEGS Mb L5USA.EH_UNCAUGHT 0 ->
  L5USA.xs_pre ar (L5USA.mkXS gd true av uid rnd canary hw) Mb.
Proof.
  intros SL AVS C0 U0. split. 2: exact AVS. cbn [L5USA.xs_gd L5USA.xs_fl L5USA.xs_av L5USA.xs_uid L5USA.xs_rnd L5USA.xs_canary L5USA.xs_hw].
  apply (L5USA.statics_after_catch Ma Mb gd av uid rnd canary hw SL C0 U0). apply xfer_guard. apply xfer_flags. apply xfer_const. exact AVS.
Qed.
End XFER.
(* [comment removed for export] *)
Lemma xs_pre_xfer (Ma Mb : word -> option byte) st :
  (forall a, xs_cell a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> (forall a, ar_sptop ar <= a < 2 ^ 47 -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
  (L5.img_clear Ma 0x10000 0xd8000 -> L5.img_clear Mb 0x10000 0xd8000) ->
  L5USA.xs_pre ar st Ma -> L5USA.xs_pre ar st Mb.
Proof.
  intros AGC AGT AGI ((EC0 & EU0 & GD & FLG & SCN) & AVS).
  assert (AGC' : forall a, xs_cell a -> ~ False -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) by (intros a Ha _; exact (AGC a Ha)).
  assert (AGE : forall i, 6360520 <= i < 6360532 -> Mb (Z_to_bv 64 i) = Ma (Z_to_bv 64 i)).
  { intros i Hi. apply AGC. split. exists (L5USA.EH_CAUGHT, 12). split. left; reflexivity. unfold L5USA.EH_CAUGHT; cbn [fst snd]; clear - Hi; lia. clear - Hi; lia. }
  split. 2: exact AVS. split.
  { apply (L5C.u64_at_agree RSEGS Ma Mb L5USA.EH_CAUGHT 0). 4: exact EC0. intros i Hi. apply AGE. unfold L5USA.EH_CAUGHT in Hi; clear - Hi; lia. unfold L5USA.EH_CAUGHT; clear; lia. unfold L5USA.EH_CAUGHT; clear; lia. }
  split.
  { unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS Ma Mb 4 L5USA.EH_UNCAUGHT). exact EU0. unfold L5USA.EH_UNCAUGHT; clear; lia. unfold L5USA.EH_UNCAUGHT; cbn; clear; lia.
    intros i Hi. apply AGE. unfold L5USA.EH_UNCAUGHT in Hi; cbn in Hi; clear - Hi; lia. }
  split. exact (xfer_guard Ma Mb (fun _ => False) AGC' (fun a X => False_ind _ X) _ GD).
  split. exact (xfer_flags Ma Mb (fun _ => False) AGC' (fun a X => False_ind _ X) _ FLG).
  exact (xfer_const Ma Mb (fun _ => False) AGC' AGT AGI (fun a X => False_ind _ X) _ _ _ _ _ AVS SCN).
Qed.
(* [comment removed for export] *)
Definition xs_dom (a : Z) : Prop := (0x10000 <= a < 0x634000 /\ ~ hl_rt_static L a) \/ ar_sptop ar <= a < 2 ^ 47.
Lemma xs_cell_dom a : L5USA.as0_unw_layout L -> xs_cell a -> xs_dom a.
Proof.
  intros (U1 & U2 & _) ((r & Hr & Ha) & _). left. split.
  - clear - Hr Ha. unfold L5USA.UNW_STATICS, L5USA.UNW_CONSTS, L5USA.EH_CAUGHT, L5USA.SYSCAT_GUARD, L5USA.UW_FLAGS, L5USA.ERRNO in Hr. cbn [app In] in Hr.
    repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in Ha; Lia.lia|]). destruct Hr.
  - apply in_app_or in Hr. destruct Hr as [Hr|Hr]. exact (proj1 (U1 r a Hr Ha)). exact (U2 r a Hr Ha).
Qed.
Lemma img_clear_dom (Ma Mb : word -> option byte) : (forall a, xs_dom a -> 0xd8000 <= a \/ a < 0x10000 \/ Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> L5.img_clear Ma 0x10000 0xd8000 -> L5.img_clear Mb 0x10000 0xd8000.
Proof.
  intros AG I1 i Hi. destruct (AG i) as [X|[X|X]]. left. split. clear - Hi; lia. intros Y. pose proof (aly_static_lo L C LY i Y). clear - Hi H; lia.
  clear - Hi X; lia. clear - Hi X; lia. rewrite X. exact (I1 i Hi).
Qed.
Lemma xs_pre_same (Ma Mb : word -> option byte) st :
  L5USA.as0_unw_layout L -> (forall a, xs_dom a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> L5USA.xs_pre ar st Ma -> L5USA.xs_pre ar st Mb.
Proof.
  intros UNWL AG. apply xs_pre_xfer.
  - intros a Ha. apply AG. exact (xs_cell_dom a UNWL Ha).
  - intros a Ha. apply AG. right. exact Ha.
  - apply img_clear_dom. intros a Ha. right; right. exact (AG a Ha).
Qed.


End WithIface.
End SCFG_1.
End L5ATX.
