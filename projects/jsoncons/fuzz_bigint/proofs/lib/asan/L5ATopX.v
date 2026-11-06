(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlanSoundSums SegRun BigLinkBase BigLinkGlue BigModel BigFactsRun BigFactsDigits L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ParseSpecsA L5OpmodSpecsA L5ACopyS L5ADetailH L5AFrameK L5AStrctor L5ATopP1 L5ATopP2 L5ATopP3 L5ATopH L5ATopD L5DivSpecsA L5UnwindSpecsA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ATX.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ATP1. Import L5ATP2. Import L5ATP3. Import L5ADH. Import L5ATH.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac al := match goal with
  | H : L5ATP2.aligned ?x ?y |- L5ATP3.aligned ?x ?y => exact H
  | H : L5ATP2.aligned ?x ?y |- L5ATP1.aligned ?x ?y => exact H
  | H : L5ATP1.aligned ?x ?y |- L5ATP2.aligned ?x ?y => exact H
  | H : L5ATP3.aligned ?x ?y |- L5ATP2.aligned ?x ?y => exact H end.
Local Ltac sc := first [ asm | al | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].

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
  destruct (rd1 M (Z_to_bv 64 6360164) ltac:(vm_compute; discriminate)) as [b0 E0]. rewrite E0.
  destruct (rd1 M (Z_to_bv 64 6360164 + 1)%bv ltac:(vm_compute; discriminate)) as [b1 E1]. rewrite E1.
  destruct (rd1 M (Z_to_bv 64 6360164 + 1 + 1)%bv ltac:(vm_compute; discriminate)) as [b2 E2]. rewrite E2.
  destruct (rd1 M (Z_to_bv 64 6360164 + 1 + 1 + 1)%bv ltac:(vm_compute; discriminate)) as [b3 E3]. rewrite E3.
  exists (BvBase.bytes_le_to_Z [b0; b1; b2; b3]). split.
  - f_equal. symmetry. apply (APSX.word_to_le_bytes_of_bytes_n 4 [b0; b1; b2; b3]). reflexivity. Lia.lia.
  - pose proof (AX2S.bytes_le_to_Z_bound [b0; b1; b2; b3]) as X. cbn [length] in X. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in X. Lia.lia.
Qed.
(* [comment removed for export] *)
Definition xs_cell (a : Z) : Prop := (exists r, In r (L5USA.UNW_STATICS ++ L5USA.UNW_CONSTS) /\ fst r <= a < fst r + snd r) /\ ~ (6360164 <= a < 6360168).
Section XFER.
Variables (Ma Mb : word -> option byte) (EXC : Z -> Prop).
Hypothesis AGC : forall a, xs_cell a -> ~ EXC a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a).
Hypothesis AGT : forall a, ar_sptop ar <= a < 2 ^ 47 -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a).
Hypothesis AGI : L5.img_clear Ma 0x10000 0xd7000 -> L5.img_clear Mb 0x10000 0xd7000.
Lemma xfer_agr r a : In r (L5USA.UNW_STATICS ++ L5USA.UNW_CONSTS) -> fst r <= a < fst r + snd r -> ~ (6360164 <= a < 6360168) -> ~ EXC a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a).
Proof. intros Hr Ha NE NC. apply AGC. split. exists r. split. exact Hr. exact Ha. exact NE. exact NC. Qed.
Lemma xfer_u64 r a v : In r (L5USA.UNW_STATICS ++ L5USA.UNW_CONSTS) -> fst r <= a -> a + 8 <= fst r + snd r -> (a + 8 <= 6360164 \/ 6360168 <= a) -> (forall i, a <= i < a + 8 -> ~ EXC i) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  L5.u64_at RSEGS Ma a v -> L5.u64_at RSEGS Mb a v.
Proof. intros Hr H1 H2 H3 HX H4 H5 X. apply (L5C.u64_at_agree RSEGS Ma Mb a v). 2: exact H4. 2: exact H5. 2: exact X. intros i Hi. apply (xfer_agr r i Hr). clear - Hi H1 H2; lia. clear - Hi H3; lia. exact (HX i Hi). Qed.
Lemma xfer_u8 r a v : In r (L5USA.UNW_STATICS ++ L5USA.UNW_CONSTS) -> fst r <= a -> a + 1 <= fst r + snd r -> (a + 1 <= 6360164 \/ 6360168 <= a) -> ~ EXC a -> 0 <= a -> a + 1 <= 2 ^ 64 ->
  L5.u8_at RSEGS Ma a v -> L5.u8_at RSEGS Mb a v.
Proof. intros Hr H1 H2 H3 HX H4 H5 X. apply (L5C.u8_at_agree RSEGS Ma Mb a v). 2: exact H4. 2: exact H5. 2: exact X. intros i Hi. apply (xfer_agr r i Hr). clear - Hi H1 H2; lia. clear - Hi H3; lia. replace i with a by (clear - Hi; lia). exact HX. Qed.
Hypothesis EXCR : forall a, EXC a -> 6357448 <= a < 6357460.       (* [comment removed for export] *)
Lemma xfer_guard gd : L5USA.syscat_guard Ma gd -> L5USA.syscat_guard Mb gd.
Proof.
  intros (G0 & G1). unfold L5USA.syscat_guard, L5USA.SYSCAT_GUARD in *. split.
  - apply (xfer_u8 (6358000, 8) 6358000 _ ltac:(right; left; reflexivity)); cbn [fst snd]; try Lia.lia. intros X; apply EXCR in X; Lia.lia. exact G0.
  - apply (xfer_u8 (6358000, 8) (6358000 + 1) _ ltac:(right; left; reflexivity)); cbn [fst snd]; try Lia.lia. intros X; apply EXCR in X; Lia.lia. exact G1.
Qed.
Lemma xfer_flags fl : L5USA.uw_flags Ma fl -> L5USA.uw_flags Mb fl.
Proof.
  unfold L5USA.uw_flags, L5USA.UW_FLAGS. destruct fl.
  - intros (F0 & F1 & F2 & F3 & F4 & F5). repeat split; (eapply (xfer_u8 (6360113, 6) _ _ ltac:(right; right; left; reflexivity)); [| | | | | | eassumption]; cbn [fst snd]; try Lia.lia; intros X; apply EXCR in X; Lia.lia).
  - intros (F0 & F2 & F4). repeat split; (eapply (xfer_u8 (6360113, 6) _ _ ltac:(right; right; left; reflexivity)); [| | | | | | eassumption]; cbn [fst snd]; try Lia.lia; intros X; apply EXCR in X; Lia.lia).
Qed.
Lemma xfer_const av uid rnd canary hw : ar_sptop ar <= av -> L5USA.statics_const Ma av uid rnd canary hw -> L5USA.statics_const Mb av uid rnd canary hw.
Proof.
  intros AVS. unfold L5USA.statics_const, L5USA.TD_LOCALE, L5USA.GLOBAL_LOCALE, L5USA.LOCALE_MSGCAT, L5USA.CANARY, L5USA.AUXVP, L5USA.SYSCAT_OBJ.
  intros (TDL & MSG & _ & CAN & AUXP & AV8 & AVLO & AVHI & AUXV & UIDR & RNDR & CANR & HWR & I1 & I2 & I3).
  assert (NX : forall lo i, lo <= i -> 6357460 <= lo \/ i < 6357448 -> ~ EXC i) by (intros lo i H1 H2 X; apply EXCR in X; clear - H1 H2 X; Lia.lia).
  split. { apply (xfer_u64 (0x610cd8, 8) _ _ ltac:(apply in_or_app; right; right; right; left; reflexivity)); cbn [fst snd]; try Lia.lia. intros i Hi; apply (NX 0x610cd8); Lia.lia. exact TDL. }
  split. { apply (xfer_u64 (0x630ff8, 8) _ _ ltac:(apply in_or_app; right; right; right; right; left; reflexivity)); cbn [fst snd]; try Lia.lia. intros i Hi; apply (NX 0x630ff8); Lia.lia. exact MSG. }
  split. exact (errno_readable Mb).
  split. { apply (xfer_u64 (0x630d48, 8) _ _ ltac:(apply in_or_app; right; do 4 right; left; reflexivity)); cbn [fst snd]; try Lia.lia. intros i Hi; apply (NX 0x630d48); Lia.lia. exact CAN. }
  split. { apply (xfer_u64 (0x630fa0, 8) _ _ ltac:(apply in_or_app; right; do 5 right; left; reflexivity)); cbn [fst snd]; try Lia.lia. intros i Hi; apply (NX 0x630fa0); Lia.lia. exact AUXP. }
  split. exact AV8. split. exact AVLO. split. exact AVHI.
  split. { intros j Hj. apply (L5C.u64_at_agree RSEGS Ma Mb). 4: exact (AUXV j Hj). 2: clear - AVLO; lia. 2: clear - AVHI Hj; lia.
           intros i Hi. apply AGT. clear - Hi AVS AVHI Hj; lia. }
  split. exact UIDR. split. exact RNDR. split. exact CANR. split. exact HWR.
  split. exact (AGI I1).
  split. { intros i Hi. rewrite (xfer_agr (0xd9f40, 32) i ltac:(apply in_or_app; right; left; reflexivity)). exact (I2 i Hi). cbn [fst snd]; clear - Hi; lia. clear - Hi; lia. apply (NX 0); clear - Hi; lia. }
  intros i Hi. rewrite (xfer_agr (0xd9f70, 8) i ltac:(apply in_or_app; right; right; left; reflexivity)). exact (I3 i Hi). cbn [fst snd]; clear - Hi; lia. clear - Hi; lia. apply (NX 0); clear - Hi; lia.
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
  (L5.img_clear Ma 0x10000 0xd7000 -> L5.img_clear Mb 0x10000 0xd7000) ->
  L5USA.xs_pre ar st Ma -> L5USA.xs_pre ar st Mb.
Proof.
  intros AGC AGT AGI ((EC0 & EU0 & GD & FLG & SCN) & AVS).
  assert (AGC' : forall a, xs_cell a -> ~ False -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) by (intros a Ha _; exact (AGC a Ha)).
  assert (AGE : forall i, 6357448 <= i < 6357460 -> Mb (Z_to_bv 64 i) = Ma (Z_to_bv 64 i)).
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
Definition xs_dom (a : Z) : Prop := (0x10000 <= a < 0x633000 /\ ~ hl_rt_static L a) \/ ar_sptop ar <= a < 2 ^ 47.
Lemma xs_cell_dom a : L5USA.as0_unw_layout L -> xs_cell a -> xs_dom a.
Proof.
  intros (U1 & U2 & _) ((r & Hr & Ha) & _). left. split.
  - clear - Hr Ha. unfold L5USA.UNW_STATICS, L5USA.UNW_CONSTS, L5USA.EH_CAUGHT, L5USA.SYSCAT_GUARD, L5USA.UW_FLAGS, L5USA.ERRNO in Hr. cbn [app In] in Hr.
    repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in Ha; Lia.lia|]). destruct Hr.
  - apply in_app_or in Hr. destruct Hr as [Hr|Hr]. exact (proj1 (U1 r a Hr Ha)). exact (U2 r a Hr Ha).
Qed.
Lemma img_clear_dom (Ma Mb : word -> option byte) : (forall a, xs_dom a -> 0xd7000 <= a \/ a < 0x10000 \/ Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> L5.img_clear Ma 0x10000 0xd7000 -> L5.img_clear Mb 0x10000 0xd7000.
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

Section BINV.
Variables (R : bvmap 5 word) (model : Model) (LB : list (Z * Z)) (FF : list fframe) (A : list (Z * Z)) (V2 cls SCRT F : Z).
Local Notation S := (V2 + cls).
Local Notation SPA := (V2 - 192).
Local Abbreviation binv M LK := (L5AFK.binv L ar HI M model LB FF LK A S SCRT SPA (town V2 cls F R) F 3).

Lemma binv_lk M LK LKb W BX Mc modelc LKc crc Ac : binv M LK W BX Mc modelc LKc crc Ac -> incl LK LKb -> binv M LKb W BX Mc modelc LKc crc Ac.
Proof.
  intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10) I. unfold L5AFK.binv.
  split. exact B1. split. exact B2. split. exact B3. split. exact B4. split. { intros x Hx. apply I. apply B5. exact Hx. }
  split. exact B6. split. exact B7. split. exact B8. split. exact B9. exact B10.
Qed.
Lemma binv_rebase M LK W BX Mc modelc LKc crc Ac : binv M LK W BX Mc modelc LKc crc Ac -> binv (rebase W M Mc) LK [] BX Mc modelc LKc crc Ac.
Proof.
  intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). unfold L5AFK.binv.
  split. exact B1. split. exact B2. split. exact B3. split. exact B4. split. exact B5. split. exact B6.
  split. apply ek_rebase. exact B7. split. apply dk_rebase. exact B8. split. exact B9. exact B10.
Qed.
End BINV.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u32_at_agree M M' a v : L5C.agree_on M M' a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof. intros AG Ha Hn H. unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M M' 4 a Ha ltac:(cbn; lia) AG). exact H. Qed.

Section PAD.
Variables (R : bvmap 5 word) (Mb : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LKb : list fframe) (A : list (Z * Z))
          (V2 cls r SCRT : Z) (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation S := (V2 + cls).
Local Notation SPA := (V2 - 192).
Hypothesis G : L5AFK.gctx L ar HI LB FF LKb A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2.
Hypothesis CLS : cls = 0 \/ cls = 16.
Hypothesis V2A : L5ATP2.aligned V2 32.
Hypothesis V2R : 140735332487424 <= V2 <= 140737488355328.
Hypothesis V2S : V2 + cls <= 140737488355328.
Hypothesis HK : K [].
Hypothesis RA : L5.ra_ok r.
Hypothesis UR1 : U R 1 = r.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
Hypothesis G4 : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis G3 : getr R (reg 3) = Z_to_bv 64 67584.
Hypothesis HSCR : 208 + 4096 <= SCRT.
Hypothesis HSCR8 : SCRT mod 8 = 0.
Hypothesis STKSHb : L5OMA.stksh ar Mb (V2 + cls - SCRT).
Hypothesis UNWL : L5USA.as0_unw_layout L.
Hypothesis HS_CATCH : 208 + L5USA.CATCH_SCR <= SCRT.
Variable crmin : credit.
Definition CWF : list L5.range := [(L5USA.EH_CAUGHT, 8); (L5USA.EH_UNCAUGHT, 4)].
Hypothesis KFb : forall (fxf : FPState) Rf Mf modelf LKf Af crf,
      regs_preserved R Rf -> getr Rf (reg 10) = Z_to_bv 64 0 ->
      ahpres L ar LB FF S SCRT CWF Mb Mf ->
      L5.u64_at RSEGS Mf L5USA.EH_CAUGHT 0 -> L5.u32_at RSEGS Mf L5USA.EH_UNCAUGHT 0 ->      (* [comment removed for export] *)
      model_rt model modelf -> incl A Af -> amodel_ok Af modelf -> incl LKf LKb -> credit_le crmin crf ->
      ri_inv HI LB FF LKf crf Af Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K.
Variables (dtor objsz refsz : Z).
Hypothesis Hcatch : L5USA.catchA_spec L ar HI dtor objsz refsz.
Hypothesis HSZ : 144 <= objsz /\ 20 <= refsz.

Local Abbreviation binv := (L5AFK.binv L ar HI Mb model LB FF LKb A S SCRT SPA (town V2 cls F R) F 3).
Local Abbreviation rinvT := (L5ATH.rinvT R V2 cls F).
Local Abbreviation rinv2 := (L5ATD.rinv2 R V2 cls F).
Local Abbreviation rinvY := (L5ATD.rinvY R V2 cls F).
Local Notation FF' := ((F, 3, V2 - 192 + 32) :: FF).
Local Abbreviation NUM := (L5ATD.NUM L ar HI R LB FF LKb A V2 cls SCRT F fl LK2 M2 model2 cr2 G V2R).
Local Abbreviation pf_of_binv := (L5ATD.pf_of_binv L ar C HI LY HIok R Mb model LB FF LKb A V2 cls SCRT F fl LK2 M2 model2 cr2 G CLS).
Local Abbreviation apure := (L5ADH.apure L ar C HI LY HIok).
Local Abbreviation dtor_stage := (L5ATD.dtor_stage L ar C HI LY HIok Hdel R Mb model K LB FF LKb A V2 cls SCRT F fl LK2 M2 model2 cr2 G CLS V2A V2R V2S HK G4 HSCR).

(* [comment removed for export] *)
Definition rinA (e sel : Z) (Rc : bvmap 5 word) : Prop := rinvY Rc /\ getr Rc (reg 10) = Z_to_bv 64 e /\ getr Rc (reg 11) = Z_to_bv 64 sel.
Definition rinB (e sel : Z) (Rc : bvmap 5 word) : Prop := rinvY Rc /\ getr Rc (reg 22) = Z_to_bv 64 e /\ getr Rc (reg 24) = Z_to_bv 64 sel.
Definition rinC (e sel : Z) (Rc : bvmap 5 word) : Prop := rinv2 Rc /\ getr Rc (reg 22) = Z_to_bv 64 e /\ getr Rc (reg 24) = Z_to_bv 64 sel.
Definition YIDX : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 27; 21; 23; 26]%nat.
Definition CIDX : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 27; 21; 23]%nat.
Lemma rinvY_keep Ra Rb : rinvY Ra -> (forall k, In k YIDX -> getr Rb (reg k) = getr Ra (reg k)) -> rinvY Rb.
Proof.
  intros (XT & X21 & X23 & X26) KS. unfold L5ATD.rinvY. rewrite !KS by inl.
  split. { apply (L5ATH.rinvT_keep R V2 cls F Ra Rb XT). intros k Hk. apply KS. revert Hk. apply (L5K.incl_b TIDX YIDX). vm_compute; reflexivity. }
  repeat split; assumption.
Qed.
Lemma rinv2_keep Ra Rb : rinv2 Ra -> (forall k, In k CIDX -> getr Rb (reg k) = getr Ra (reg k)) -> rinv2 Rb.
Proof.
  intros (XT & X21 & X23) KS. unfold L5ATD.rinv2. rewrite !KS by inl.
  split. { apply (L5ATH.rinvT_keep R V2 cls F Ra Rb XT). intros k Hk. apply KS. revert Hk. apply (L5K.incl_b TIDX CIDX). vm_compute; reflexivity. }
  repeat split; assumption.
Qed.
Lemma rinvY_pres Ra Rb : rinvY Ra -> regs_preserved Ra Rb -> rinvY Rb.
Proof. intros XY RP. apply (rinvY_keep Ra Rb XY). intros k Hk. apply (cs_of_preserved Ra Rb k RP). revert Hk. apply (L5K.incl_b YIDX cs_all). vm_compute; reflexivity. Qed.
Lemma rinv2_pres Ra Rb : rinv2 Ra -> regs_preserved Ra Rb -> rinv2 Rb.
Proof. intros XY RP. apply (rinv2_keep Ra Rb XY). intros k Hk. apply (cs_of_preserved Ra Rb k RP). revert Hk. apply (L5K.incl_b CIDX cs_all). vm_compute; reflexivity. Qed.
Lemma rinB_T e sel Rc : rinB e sel Rc -> rinvT Rc. Proof. intros ((X & _) & _). exact X. Qed.
Lemma rinC_T e sel Rc : rinC e sel Rc -> rinvT Rc. Proof. intros ((X & _) & _). exact X. Qed.
Lemma rinB_C e sel Rc : rinB e sel Rc -> rinC e sel Rc. Proof. intros ((X & Y & Z & _) & E1 & E2). split. split. exact X. split. exact Y. exact Z. split. exact E1. exact E2. Qed.
Lemma rinB_pres e sel Ra Rb : rinB e sel Ra -> regs_preserved Ra Rb -> rinB e sel Rb.
Proof.
  intros (XY & E1 & E2) RP. unfold rinB. rewrite !(cs_of_preserved Ra Rb _ RP) by inl. split. 2: split; assumption.
  apply (rinvY_keep Ra Rb XY). intros k Hk. apply (cs_of_preserved Ra Rb k RP). revert Hk. apply (L5K.incl_b YIDX cs_all). vm_compute; reflexivity.
Qed.
Lemma rinC_pres e sel Ra Rb : rinC e sel Ra -> regs_preserved Ra Rb -> rinC e sel Rb.
Proof.
  intros (XY & E1 & E2) RP. unfold rinC. rewrite !(cs_of_preserved Ra Rb _ RP) by inl. split. 2: split; assumption.
  apply (rinv2_keep Ra Rb XY). intros k Hk. apply (cs_of_preserved Ra Rb k RP). revert Hk. apply (L5K.incl_b CIDX cs_all). vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Local Ltac open_pf PF := destruct PF as (W192 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv);
  pose proof NUM as ((FRG & FLRG & V2RG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
Local Ltac vmap Rc fb q cap := constr:(fun j : nat => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fb | 61%nat => q | 62%nat => cap | _ => 0 end).
Local Ltac pre_inl := 
  match goal with |- L5ATD.inl_run _ _ _ _ _ _ _ _ => unfold L5ATD.inl_run end;
  let fx := fresh "fx" in let Rc := fresh "Rc" in let MV := fresh "MV" in let fb := fresh "fb" in
  intros fx Rc MV fb RI PF O0 FBR BT0; open_pf PF;
  assert (FBR' : 0 <= fb <= 255 /\ 0 <= fb < 2 ^ 64) by (clear - FBR; lia); destruct FBR' as [FBR' FBR''].
Local Ltac pre_dyn :=
  let fx := fresh "fx" in let Rc := fresh "Rc" in let MV := fresh "MV" in let fb := fresh "fb" in let q := fresh "q" in let cap := fresh "cap" in
  intros fx Rc MV fb q cap RI PF O0 FBR BT1 O24 QR O16 CAPR; open_pf PF;
  assert (FBR' : 0 <= fb <= 255 /\ 0 <= fb < 2 ^ 64) by (clear - FBR; lia); destruct FBR' as [FBR' FBR''];
  assert (QR' : 4096 <= q <= 140737488355328 /\ 0 <= q < 2 ^ 64) by (clear - QR; lia); destruct QR' as [QR' QR''];
  assert (CR' : 1 <= cap <= 134217728 /\ 0 <= cap < 2 ^ 64) by (clear - CAPR; lia); destruct CR' as [CR' CR''].

Lemma run_XAi e sel : L5ATD.inl_run V2 F fl (rinA e sel) (rinB e sel) 0x8e334 0x8e35c (F + 224).
Proof.
  pre_inl. pose proof RI as (((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21 & X23 & X26) & X10 & X11).
  pose proof (tpXAi_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fb | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & _ & pR22 & pR24)).
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
  exists fx1, R1. split. exact pMS. split. 2:{ rewrite pR22, pR24. split; assumption. }
  apply (rinvY_keep Rc R1 (proj1 RI)). intros k Hk. apply pKS. revert Hk. apply (L5K.incl_b YIDX KS_tpXAi). vm_compute; reflexivity.
Qed.
Lemma run_XAd e sel : L5ATD.dyn_run V2 F fl (rinA e sel) (rinB e sel) 0x8e334 0x8e35c (F + 224).
Proof.
  unfold L5ATD.dyn_run. replace (F + 224 + 24) with (F + 248) by (clear; lia). replace (F + 224 + 16) with (F + 240) by (clear; lia).
  pre_dyn. pose proof RI as (((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21 & X23 & X26) & X10 & X11).
  pose proof (tpXAd_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fb | 61%nat => q | 62%nat => cap | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & pR1 & pR10 & pR11 & pR22 & pR24)).
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
  exists fx1, R1. split. exact pMS. split. 2:{ split. exact pR1. split. exact pR10. exact pR11. }
  split. 2:{ rewrite pR22, pR24. split; assumption. }
  apply (rinvY_keep Rc R1 (proj1 RI)). intros k Hk. apply pKS. revert Hk. apply (L5K.incl_b YIDX KS_tpXAd). vm_compute; reflexivity.
Qed.
Lemma run_XBi e sel : L5ATD.inl_run V2 F fl (rinB e sel) (rinB e sel) 0x8e35c 0x8e37c (F + 160).
Proof.
  pre_inl. pose proof RI as (((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21 & X23 & X26) & X22 & X24).
  pose proof (tpXBi_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fb | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & _)).
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
  exists fx1, R1. split. exact pMS. split. 2:{ rewrite !pKS by inl. split; assumption. }
  apply (rinvY_keep Rc R1 (proj1 RI)). intros k Hk. apply pKS. revert Hk. apply (L5K.incl_b YIDX KS_tpXBi). vm_compute; reflexivity.
Qed.
Lemma run_XBd e sel : L5ATD.dyn_run V2 F fl (rinB e sel) (rinB e sel) 0x8e35c 0x8e37c (F + 160).
Proof.
  unfold L5ATD.dyn_run. replace (F + 160 + 24) with (F + 184) by (clear; lia). replace (F + 160 + 16) with (F + 176) by (clear; lia).
  pre_dyn. pose proof RI as (((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21 & X23 & X26) & X22 & X24).
  pose proof (tpXBd_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fb | 61%nat => q | 62%nat => cap | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & pR1 & pR10 & pR11)).
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
  exists fx1, R1. split. exact pMS. split. 2:{ split. exact pR1. split. exact pR10. exact pR11. }
  split. 2:{ rewrite !pKS by inl. split; assumption. }
  apply (rinvY_keep Rc R1 (proj1 RI)). intros k Hk. apply pKS. revert Hk. apply (L5K.incl_b YIDX KS_tpXBd). vm_compute; reflexivity.
Qed.
Lemma run_XCi e sel : L5ATD.inl_run V2 F fl (rinC e sel) (rinC e sel) 0x8e390 0x8e3b0 (F + 96).
Proof.
  pre_inl. pose proof RI as (((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21 & X23) & X22 & X24).
  pose proof (tpXCi_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fb | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & _)).
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
  exists fx1, R1. split. exact pMS. split. 2:{ rewrite !pKS by inl. split; assumption. }
  apply (rinv2_keep Rc R1 (proj1 RI)). intros k Hk. apply pKS. revert Hk. apply (L5K.incl_b CIDX KS_tpXCi). vm_compute; reflexivity.
Qed.
Lemma run_XCd e sel : L5ATD.dyn_run V2 F fl (rinC e sel) (rinC e sel) 0x8e390 0x8e3b0 (F + 96).
Proof.
  unfold L5ATD.dyn_run. replace (F + 96 + 24) with (F + 120) by (clear; lia). replace (F + 96 + 16) with (F + 112) by (clear; lia).
  pre_dyn. pose proof RI as (((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21 & X23) & X22 & X24).
  pose proof (tpXCd_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fb | 61%nat => q | 62%nat => cap | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & pR1 & pR10 & pR11)).
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
  exists fx1, R1. split. exact pMS. split. 2:{ split. exact pR1. split. exact pR10. exact pR11. }
  split. 2:{ rewrite !pKS by inl. split; assumption. }
  apply (rinv2_keep Rc R1 (proj1 RI)). intros k Hk. apply pKS. revert Hk. apply (L5K.incl_b CIDX KS_tpXCd). vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Definition xfacts (Mc : word -> option byte) (obj ref : Z) : Prop :=
  L5USA.exc_at Mc obj ref dtor /\ L5.u64_at RSEGS Mc L5USA.EH_CAUGHT 0 /\ L5.u32_at RSEGS Mc L5USA.EH_UNCAUGHT 1 /\
  L5.img_clear Mc 0x10000 0xd7000 /\ L5.img_clear Mc 0xd9f40 0xd9f60.
Definition xaddr (obj ref a : Z) : Prop :=
  obj - 128 <= a < obj - 128 + objsz \/ ref <= a < ref + refsz \/ 0x10000 <= a < 0xd7000 \/ 0xd9f40 <= a < 0xd9f60 \/ L5USA.EH_CAUGHT <= a < L5USA.EH_CAUGHT + 12.
Lemma xfacts_agree Mc M1 obj ref : xfacts Mc obj ref -> 4096 <= obj - 128 -> obj - 128 + objsz <= 2 ^ 47 -> 4096 <= ref -> ref + refsz <= 2 ^ 47 ->
  (forall a, xaddr obj ref a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) -> xfacts M1 obj ref.
Proof.
  intros ((E1 & E2 & E3 & E4 & E5 & E6 & E7) & C0 & U1 & I1 & I2) O1 O2 R1 R2 AG. destruct HSZ as [HZ1 HZ2]. unfold xfacts, L5USA.exc_at.
  assert (AO : forall a n, obj - 128 <= a -> a + n <= obj - 128 + objsz -> L5C.agree_on Mc M1 a n). { intros a n H1 H2 i Hi. apply AG. left. clear - H1 H2 Hi; lia. }
  assert (AR : forall a n, ref <= a -> a + n <= ref + refsz -> L5C.agree_on Mc M1 a n). { intros a n H1 H2 i Hi. apply AG. right; left. clear - H1 H2 Hi; lia. }
  split. { split. eapply L5C.u64_at_agree. 4: exact E1. apply AO; clear - HZ1; lia. clear - O1; lia. clear - O2 HZ1; lia.
    split. eapply u32_at_agree. 4: exact E2. apply AO; clear - HZ1; lia. clear - O1; lia. clear - O2 HZ1; lia.
    split. eapply L5C.u64_at_agree. 4: exact E3. apply AO; clear - HZ1; lia. clear - O1; lia. clear - O2 HZ1; lia.
    split. eapply L5C.u64_at_agree. 4: exact E4. apply AO; clear - HZ1; lia. clear - O1; lia. clear - O2 HZ1; lia.
    split. eapply L5C.u64_at_agree. 4: exact E5. apply AO; clear - HZ1; lia. clear - O1; lia. clear - O2 HZ1; lia.
    split. eapply L5C.u64_at_agree. 4: exact E6. apply AO; clear - HZ1; lia. clear - O1; lia. clear - O2 HZ1; lia.
    eapply u32_at_agree. 4: exact E7. apply AR; clear - HZ2; lia. clear - R1; lia. clear - R2 HZ2; lia. }
  split. { eapply L5C.u64_at_agree. 4: exact C0. intros i Hi. apply AG. right; right; right; right. unfold L5USA.EH_CAUGHT in *. clear - Hi; lia. unfold L5USA.EH_CAUGHT; clear; lia. unfold L5USA.EH_CAUGHT; clear; lia. }
  split. { eapply u32_at_agree. 4: exact U1. intros i Hi. apply AG. right; right; right; right. unfold L5USA.EH_CAUGHT, L5USA.EH_UNCAUGHT in *. clear - Hi; lia. unfold L5USA.EH_UNCAUGHT; clear; lia. unfold L5USA.EH_UNCAUGHT; clear; lia. }
  split. { intros i Hi. rewrite AG. apply I1. exact Hi. right; right; left. exact Hi. }
  intros i Hi. rewrite AG. apply I2. exact Hi. right; right; right; left. exact Hi.
Qed.
Lemma xaddr_client BXr obj ref scr a : xaddr obj ref a -> aclient L ar (((ref, refsz) :: (obj - 128, objsz) :: BXr) ++ LB) FF' SPA scr a.
Proof.
  intros [X|[X|[X|[X|X]]]].
  - apply (block_client L ar _ FF' SPA scr (obj - 128) objsz a). right; left; reflexivity. exact X.
  - apply (block_client L ar _ FF' SPA scr ref refsz a). left; reflexivity. exact X.
  - right; right; left. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY). split. clear - X; lia. intros ST. pose proof (aly_static_lo L C LY a ST). clear - X H; lia.
  - right; right; left. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY). split. clear - X; lia. apply (proj1 (proj2 UNWL) (0xd9f40, 32) a). left; reflexivity. cbn [fst snd]. clear - X; lia.
  - right; right; left. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY). split. unfold L5USA.EH_CAUGHT in X; clear - X; lia.
    apply (proj1 UNWL (L5USA.EH_CAUGHT, 12) a). left; reflexivity. cbn [fst snd]. exact X.
Qed.
(* [comment removed for export] *)
Lemma blk_rng W BX Mc modelc LKc crc Ac u n : binv W BX Mc modelc LKc crc Ac -> In (u, n) BX ->
  4096 <= u /\ u + n <= 2 ^ 47 /\ (u + n <= BIGSHADOW_LO \/ BIGSHADOW_HI <= u) /\ 0 < n.
Proof.
  intros (B1 & _) Hin. pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (WFB & _).
  destruct (WFB (u, n) ltac:(apply in_or_app; left; exact Hin)) as ((R1 & _ & _ & R4 & _ & (_ & R6 & R7)) & _). cbn [fst snd] in *.
  split. exact R1. split. exact R7. split. exact R6. exact R4.
Qed.
Lemma nd_head2 (a b : Z) (l : list Z) q : base.NoDup (a :: b :: l) -> In q l -> q <> a /\ q <> b.
Proof.
  intros ND Hq. inversion ND as [|x l' Na ND']; subst. inversion ND' as [|x l' Nb _]; subst.
  split; intros ->. apply Na. constructor. apply list_elem_of_In. exact Hq. apply Nb. apply list_elem_of_In. exact Hq.
Qed.

Local Abbreviation binv_piece := (L5AFK.binv_piece L ar HI Mb model LB FF LKb A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2 G).
Local Abbreviation binv_callee := (L5AFK.binv_callee L ar C HI HIok Mb model LB FF LKb A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2 G).
Local Abbreviation binv_model := (L5AFK.binv_model L ar HI Mb model LB FF LKb A S SCRT SPA (town V2 cls F R) F 3).
Local Abbreviation fsh_client := (L5ATD.fsh_client L ar HI R LB FF LKb A V2 cls SCRT F fl LK2 M2 model2 cr2 G).
Local Abbreviation fsh_off := (L5ATD.fsh_off L ar HI R LB FF LKb A V2 cls SCRT F fl LK2 M2 model2 cr2 G V2R).
Local Abbreviation tcl := (L5ATD.tcl L ar HI R LB FF LKb A V2 cls SCRT F fl LK2 M2 model2 cr2 G).
Local Abbreviation str_agree := (L5ATD.str_agree L ar HI R LB FF LKb A V2 cls SCRT F fl LK2 M2 model2 cr2 G V2R).
Local Abbreviation str_at := (L5ATD.str_at F).
Local Abbreviation ostr := L5ATD.ostr.
Local Notation XB obj ref := [(ref, refsz); (obj - 128, objsz)].

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma spa_facts : (V2 - 192) mod 32 = 0 /\ (V2 - 192) mod 16 = 0 /\ (V2 + 16 - SCRT) mod 8 = 0.
Proof. clear - V2A HSCR8. unfold L5ATP2.aligned in V2A. lia. Qed.
Lemma scr8_facts : (SCRT - 208) mod 8 = 0.
Proof. clear - HSCR8. lia. Qed.
(* [comment removed for export] *)
Lemma fsh_far a : F / 8 + SB <= a < F / 8 + SB + 64 -> 2147450880 <= a < 17594333495296.
Proof. intros Ha. pose proof NUM as (_ & FRP & _). unfold SB in *. clear - Ha FRP. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma ph_catch (fx : FPState) Rc Mc modelc LKc crc Ac sk obj ref :
  binv [] (XB obj ref ++ ostr sk) Mc modelc LKc crc Ac -> credit_le crmin crc -> rinvT Rc ->
  getr Rc (reg 10) = Z_to_bv 64 (obj - 32) -> xfacts Mc obj ref -> str_at Mc sk ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e3d4 Mc modelc) K.
Proof.
  intros BI CRL RI X10 (EXC & C0 & U1 & I1 & I2) ST.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4).
  pose proof spa_facts as (SPA32 & SPA16 & LO8).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  assert (STK1 : astk ar Mc SPA (SCRT - 208)).
  { replace SPA with (S - (192 + cls)) by (clear; lia). apply (astk_sub ar Mc Mc S SCRT (192 + cls) (SCRT - 208) B6 (mem_grows_refl _)).
    clear - CLS; lia. clear - HSCR; lia. clear - CLS; lia. replace (S - (192 + cls)) with SPA by (clear; lia). exact SPA16. }
  assert (SH1 : L5OMA.stksh ar Mc (SPA - (SCRT - 208))).
  { replace (SPA - (SCRT - 208)) with (V2 + 16 - SCRT) by (clear; lia).
    apply (L5ATD.stksh_now L ar C HI HIok R Mb model LB FF LKb A V2 cls SCRT F fl LK2 M2 model2 cr2 G CLS V2A V2R STKSHb HSCR8 _ Mc modelc LKc crc Ac (V2 + 16 - SCRT) BI). clear - CLS; lia. exact LO8. }
  apply (Hcatch fx Rc Mc modelc K (ostr sk ++ LB) FF' LKc crc Ac obj ref SPA (SCRT - 208)).
  - exact B1.
  - exact B2.
  - exact HK.
  - rewrite r10. exact X10.
  - rewrite r2. exact X2.
  - replace (3%bv : bv 5) with (reg 3) by (apply bv_eq; reflexivity). rewrite X3. exact G3.
  - rewrite r4, X4. exact G4.
  - replace (9%bv : bv 5) with (reg 9) by (apply bv_eq; reflexivity). exact X9.
  - exact SPA32.
  - destruct B6 as (_ & _ & T1 & T2 & _). clear - T1 T2 CLS; lia.
  - exact STK1.
  - clear - HS_CATCH; lia.
  - exact scr8_facts.
  - exact SH1.
  - exact EXC.
  - exact C0.
  - exact U1.
  - exact I1.
  - exact I2.
  - intros fx1 R1 M1 model1 A1 RP1 C01 U01 AH1 RT1 IA1 AM1 HH1.
    assert (BI1 : binv CWF (ostr sk) M1 model1 LKc crc A1).
    { apply (binv_callee [] CWF (XB obj ref ++ ostr sk) (ostr sk) (ostr sk) Mc modelc LKc crc Ac M1 model1 LKc crc A1 (SCRT - 208) CWF BI AH1 HH1 AM1 RT1 IA1 (incl_refl _)).
      - clear - HSCR; lia.
      - clear - CLS; lia.
      - intros rr a Hr Ha. assert (AR : 6357448 <= a < 6357460). { unfold CWF, L5USA.EH_CAUGHT, L5USA.EH_UNCAUGHT in Hr. destruct Hr as [<-|[<-|[]]]; unfold L5.in_rng in Ha; cbn [fst snd] in Ha; clear - Ha; lia. }
        split. intros OC. pose proof (OCR a OC) as X. clear - X AR SPC SLO SPT. lia.
        intros X. change (ff_bytes 3 / 8) with 64 in X. pose proof (fsh_far a X) as Y. clear - Y AR; lia.
      - intros a _ X. exact X.
      - intros a _ rr []. }
    (* [comment removed for export] *)
    pose proof (L5ATD.pf_of_binv L ar C HI LY HIok R (rebase CWF Mb M1) model LB FF LKb A V2 cls SCRT F fl LK2 M2 model2 cr2 G CLS _ _ _ _ _ _
                  (binv_rebase R model LB FF A V2 cls SCRT F Mb LKb CWF (ostr sk) M1 model1 LKc crc A1 BI1)) as PF.
    assert (RI1 : rinvT R1) by (apply (L5ATH.rinvT_pres R V2 cls F Rc R1 RI RP1)).
    pose proof BI1 as (D1 & D2 & _ & _ & _ & _ & _ & D8 & _).
    set (MV := mrestrict (ahid A1 model1) M1) in *.
    destruct PF as (W192 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
    pose proof NUM as ((FRG & FLRG & V2RG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
    pose proof RI1 as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y27 & Y3 & Y4).
    pose proof (tpXJ_conc fx1 R1 MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R1 1 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx2 & R2 & M2v & _ & pFR & _ & (pMS & pKS)).
    assert (E2 : M2v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M2v.
    apply (apure (ostr sk ++ LB) FF' LKc crc A1 M1 model1 fx1 fx2 R1 0x8e3dc R2 0x8e198 K D1 D2 pMS).
    intros model2' HH2' AM2' RT2' AH2'.
    pose proof (L5AFK.binv_model L ar HI Mb model LB FF LKb A S SCRT SPA (town V2 cls F R) F 3 CWF (ostr sk) M1 model1 LKc crc A1 model2' BI1 HH2' AM2' RT2') as BI2.
    pose proof (binv_rebase R model LB FF A V2 cls SCRT F Mb LKb CWF (ostr sk) M1 model2' LKc crc A1 BI2) as BI2r.
    assert (KF' : forall (fxf : FPState) Rf Mf modelf LKf Af crf, regs_preserved R Rf -> getr Rf (reg 10) = Z_to_bv 64 0 -> ahpres L ar LB FF S SCRT [] (rebase CWF Mb M1) Mf ->
               model_rt model modelf -> incl A Af -> amodel_ok Af modelf -> incl LKf LKb -> credit_le crmin crf -> ri_inv HI LB FF LKf crf Af Mf (vml_of modelf) ->
               srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K).
    { intros fxf Rf Mf modelf LKf Af crf RPf R10f AHf RTf IAf AMf LKIf CRLf HHf.
      assert (AGC : forall i, 6357448 <= i < 6357460 -> Mf (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)).
      { intros i Hi. rewrite (proj1 AHf i).
        - destruct (Z_lt_le_dec i 6357456) as [Y|Y].
          + apply (rebase_in CWF Mb M1 i (L5USA.EH_CAUGHT, 8)). clear - Hi; lia. left; reflexivity. unfold L5.in_rng, L5USA.EH_CAUGHT; cbn [fst snd]. clear - Hi Y; lia.
          + apply (rebase_in CWF Mb M1 i (L5USA.EH_UNCAUGHT, 4)). clear - Hi; lia. right; left; reflexivity. unfold L5.in_rng, L5USA.EH_UNCAUGHT; cbn [fst snd]. clear - Hi Y; lia.
        - split. clear - Hi; lia. split. 2:{ intros rr []. }
          right; right; left. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY). split. clear - Hi; lia.
          exact (proj1 (proj1 UNWL (L5USA.EH_CAUGHT, 12) i ltac:(left; reflexivity) ltac:(unfold L5USA.EH_CAUGHT; cbn [fst snd]; clear - Hi; lia))). }
      apply (KFb fxf Rf Mf modelf LKf Af crf RPf R10f). 4: exact RTf. 4: exact IAf. 4: exact AMf. 4: exact LKIf. 4: exact CRLf. 4: exact HHf.
      + pose proof (ahpres_rebase LB FF S SCRT CWF [] Mb M1 Mf AHf D8) as X. cbn [app] in X. exact X.
      + apply (L5C.u64_at_agree RSEGS M1 Mf L5USA.EH_CAUGHT 0). 4: exact C01. intros i Hi. apply AGC. unfold L5USA.EH_CAUGHT in Hi; clear - Hi; lia. unfold L5USA.EH_CAUGHT; clear; lia. unfold L5USA.EH_CAUGHT; clear; lia.
      + apply (u32_at_agree M1 Mf L5USA.EH_UNCAUGHT 0). 4: exact U01. intros i Hi. apply AGC. unfold L5USA.EH_UNCAUGHT in Hi; clear - Hi; lia. unfold L5USA.EH_UNCAUGHT; clear; lia. unfold L5USA.EH_UNCAUGHT; clear; lia. }
    assert (RI2 : rinvT R2). { apply (L5ATH.rinvT_ks R V2 cls F R1 R2 KS_tpXJ RI1 pKS). vm_compute; reflexivity. }
    assert (ST1 : str_at M1 sk).
    { apply (str_agree Mc M1 sk ST). intros i Hi. apply (proj1 AH1). split. clear - Hi FRP; lia.
      split. apply tcl. clear - HSCR; lia. left; clear - Hi; lia.
      intros rr Hr Ha. unfold CWF, L5USA.EH_CAUGHT, L5USA.EH_UNCAUGHT in Hr. destruct Hr as [<-|[<-|[]]]; unfold L5.in_rng in Ha; cbn [fst snd] in Ha; clear - Ha Hi FR; lia. }
    exact (L5ATD.ph_str L ar C HI LY HIok Hdel R (rebase CWF Mb M1) model K LB FF LKb A V2 cls r SCRT F fl LK2 M2 model2 cr2 G CLS V2A V2R V2S HK RA UR1 G2 G4 HSCR crmin KF'
             fx2 R2 M1 model2' LKc crc A1 sk BI2r CRL RI2 ST1).
Qed.

(* [comment removed for export] *)
Lemma xfacts_off BX Mc modelc LKc crc Ac M3 obj ref : binv [] (XB obj ref ++ BX) Mc modelc LKc crc Ac -> xfacts Mc obj ref ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (F / 8 + SB <= a < F / 8 + SB + 64) -> M3 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) -> xfacts M3 obj ref.
Proof.
  intros BI XF AG. destruct HSZ as [HZ1 HZ2].
  destruct (blk_rng [] _ Mc modelc LKc crc Ac (obj - 128) objsz BI ltac:(right; left; reflexivity)) as (O1 & O2 & O3 & _).
  destruct (blk_rng [] _ Mc modelc LKc crc Ac ref refsz BI ltac:(left; reflexivity)) as (R1 & R2 & R3 & _).
  apply (xfacts_agree Mc M3 obj ref XF O1 O2 R1 R2). intros a Xa. apply AG.
  - unfold xaddr, L5USA.EH_CAUGHT in Xa. clear - Xa O1 O2 R1 R2. lia.
  - intros Y. pose proof (fsh_far a Y) as Z. unfold xaddr, L5USA.EH_CAUGHT, BIGSHADOW_LO, BIGSHADOW_HI in *. clear - Xa Z O3 R3 HZ1 HZ2. destruct Xa as [X|[X|[X|[X|X]]]]; destruct O3 as [O3|O3]; destruct R3 as [R3|R3]; Lia.lia.
Qed.
Lemma xfacts_cl BX BXn Mc modelc LKc crc Ac M3 obj ref scr : binv [] (XB obj ref ++ BX) Mc modelc LKc crc Ac -> xfacts Mc obj ref ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar ((XB obj ref ++ BXn) ++ LB) FF' SPA scr a -> M3 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) -> xfacts M3 obj ref.
Proof.
  intros BI XF AG. destruct HSZ as [HZ1 HZ2].
  destruct (blk_rng [] _ Mc modelc LKc crc Ac (obj - 128) objsz BI ltac:(right; left; reflexivity)) as (O1 & O2 & O3 & _).
  destruct (blk_rng [] _ Mc modelc LKc crc Ac ref refsz BI ltac:(left; reflexivity)) as (R1 & R2 & R3 & _).
  apply (xfacts_agree Mc M3 obj ref XF O1 O2 R1 R2). intros a Xa. apply AG.
  - unfold xaddr, L5USA.EH_CAUGHT in Xa. clear - Xa O1 O2 R1 R2. lia.
  - apply (xaddr_client BXn obj ref scr a Xa).
Qed.

(* [comment removed for export] *)
Lemma ph_xe (fx : FPState) Rc Mc modelc LKc crc Ac sk obj ref :
  binv [] (XB obj ref ++ ostr sk) Mc modelc LKc crc Ac -> credit_le crmin crc -> rinC (obj - 32) 1 Rc -> xfacts Mc obj ref -> str_at Mc sk ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e3b0 Mc modelc) K.
Proof.
  intros BI CRL RI XF ST.
  pose proof (pf_of_binv _ _ _ _ _ _ BI) as PF. pose proof BI as (B1 & B2 & _).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  open_pf PF. pose proof RI as (((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21 & X23) & X22 & X24).
  pose proof (tpXE_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx2 & R2 & M2v & MG2 & oFR & oFZ & (oMS & oKS & oR10 & _)).
  set (W2 := fun a => F / 8 + SB + 12 <= a < F / 8 + SB + 16).
  apply (apiece L ar C HI LY HIok ((XB obj ref ++ ostr sk) ++ LB) FF' LKc crc Ac Mc modelc fx fx2 Rc 0x8e3b0 R2 0x8e3d4 M2v W2 K B1 B2 oMS MG2).
  { intros a Ha Hna. apply oFZ. exact Ha. clear - Hna; subst W2; cbn beta in Hna; unfold SB in *; lia. }
  { intros a Ha Wa. apply fsh_client. clear - Wa; subst W2; cbn beta in Wa; lia. }
  intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
  assert (BI3 : binv [] (XB obj ref ++ ostr sk) M3 model3 LKc crc Ac).
  { apply (binv_piece [] _ Mc modelc LKc crc Ac M3 model3 W2 BI HH3 AM3 RT3 MGM3 FRM3).
    intros a Wa. right; right. change (ff_bytes 3 / 8) with 64. clear - Wa; subst W2; cbn beta in Wa; lia. }
  assert (AG3 : forall a, 0 <= a < 2 ^ 64 -> ~ (F / 8 + SB <= a < F / 8 + SB + 64) -> M3 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha Hn. apply FRM3. exact Ha. intros X. apply Hn. clear - X; subst W2; cbn beta in X; lia. }
  apply (ph_catch fx2 R2 M3 model3 LKc crc Ac sk obj ref BI3 CRL).
  - apply (L5ATH.rinvT_ks R V2 cls F Rc R2 KS_tpXE (rinC_T _ _ _ RI) oKS). vm_compute; reflexivity.
  - rewrite oR10. exact X22.
  - apply (xfacts_off (ostr sk) Mc modelc LKc crc Ac M3 obj ref BI XF AG3).
  - apply (str_agree Mc M3 sk ST). intros i Hi. apply AG3. clear - Hi FRP; lia. apply fsh_off. left; clear - Hi; lia.
Qed.

Local Abbreviation obj_at := L5ATD.obj_at.
Local Abbreviation obj_keep := (L5ATD.obj_keep L ar HI R LB FF LKb A V2 cls SCRT F fl LK2 M2 model2 cr2 G V2R V2S).
Local Abbreviation str_keep := (L5ATD.str_keep L ar HI R LB FF LKb A V2 cls SCRT F fl LK2 M2 model2 cr2 G V2R).
Local Abbreviation tobj_rng := (L5ATD.tobj_rng L ar HI R LB FF LKb A V2 cls SCRT F fl LK2 M2 model2 cr2 G V2R V2S).

(* [comment removed for export] *)
Lemma ph_xc (fx : FPState) Rc Mc modelc LKc crc Ac sk obj ref ba :
  binv [] (XB obj ref ++ ostr sk) Mc modelc LKc crc Ac -> credit_le crmin crc -> rinC (obj - 32) 1 Rc -> xfacts Mc obj ref -> str_at Mc sk ->
  obj_at Mc (F + 96) ba None ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e390 Mc modelc) K.
Proof.
  intros BI CRL RI XF ST OA.
  apply (dtor_stage (rinC (obj - 32) 1) (rinC (obj - 32) 1) 0x8e390 0x8e3b0 (F + 96) (run_XCi _ _) (run_XCd _ _) (rinC_T _ _) (rinC_pres _ _)
           ltac:(split; [clear; lia | reflexivity]) ltac:(left; clear; lia) fx Rc Mc modelc (XB obj ref ++ ostr sk) (XB obj ref ++ ostr sk) LKc crc Ac ba None BI RI OA eq_refl).
  intros fx' R' M' model' A' BI' RI' IA' AG'.
  apply (ph_xe fx' R' M' model' LKc crc A' sk obj ref BI' CRL RI').
  - apply (xfacts_cl (ostr sk) (ostr sk) Mc modelc LKc crc Ac M' obj ref OPDEL_SCR BI XF AG').
  - apply (str_keep ((XB obj ref ++ ostr sk) ++ LB) OPDEL_SCR Mc M' sk ST). rewrite DEL_EQ; clear; lia. exact AG'.
Qed.

(* [comment removed for export] *)
Lemma ph_xp (fx : FPState) Rc Mc modelc LKc crc Ac sk obj ref ba :
  binv [] (XB obj ref ++ ostr sk) Mc modelc LKc crc Ac -> credit_le crmin crc -> rinC (obj - 32) 1 Rc -> xfacts Mc obj ref -> str_at Mc sk ->
  obj_at Mc (F + 96) ba None ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e37c Mc modelc) K.
Proof.
  intros BI CRL RI XF ST OA.
  pose proof (pf_of_binv _ _ _ _ _ _ BI) as PF. pose proof BI as (B1 & B2 & _).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  open_pf PF. pose proof RI as (((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21 & X23) & X22 & X24).
  pose proof (tpXP_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx2 & R2 & M2v & MG2 & oFR & oFZ & (oMS & oKS & _)).
  set (W2 := fun a => F / 8 + SB + 20 <= a < F / 8 + SB + 24).
  apply (apiece L ar C HI LY HIok ((XB obj ref ++ ostr sk) ++ LB) FF' LKc crc Ac Mc modelc fx fx2 Rc 0x8e37c R2 0x8e390 M2v W2 K B1 B2 oMS MG2).
  { intros a Ha Hna. apply oFZ. exact Ha. clear - Hna; subst W2; cbn beta in Hna; unfold SB in *; lia. }
  { intros a Ha Wa. apply fsh_client. clear - Wa; subst W2; cbn beta in Wa; lia. }
  intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
  assert (BI3 : binv [] (XB obj ref ++ ostr sk) M3 model3 LKc crc Ac).
  { apply (binv_piece [] _ Mc modelc LKc crc Ac M3 model3 W2 BI HH3 AM3 RT3 MGM3 FRM3).
    intros a Wa. right; right. change (ff_bytes 3 / 8) with 64. clear - Wa; subst W2; cbn beta in Wa; lia. }
  assert (AG3 : forall a, 0 <= a < 2 ^ 64 -> ~ (F / 8 + SB <= a < F / 8 + SB + 64) -> M3 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha Hn. apply FRM3. exact Ha. intros X. apply Hn. clear - X; subst W2; cbn beta in X; lia. }
  apply (ph_xc fx2 R2 M3 model3 LKc crc Ac sk obj ref ba BI3 CRL).
  - split. 2:{ rewrite !oKS by inl. split; assumption. }
    apply (rinv2_keep Rc R2 (proj1 RI)). intros k Hk. apply oKS. revert Hk. apply (L5K.incl_b CIDX KS_tpXP). vm_compute; reflexivity.
  - apply (xfacts_off (ostr sk) Mc modelc LKc crc Ac M3 obj ref BI XF AG3).
  - apply (str_agree Mc M3 sk ST). intros i Hi. apply AG3. clear - Hi FRP; lia. apply fsh_off. left; clear - Hi; lia.
  - assert (TA : L5ATD.tobj V2 cls F (F + 96)) by (left; clear; lia).
    apply (L5ATD.obj_at_agree Mc M3 _ _ _ OA). clear - FRP; lia. clear - FRP; lia. intros i Hi. destruct (tobj_rng _ i TA Hi) as [X Y]. apply AG3. exact Y. apply fsh_off. exact X.
Qed.

(* [comment removed for export] *)
Lemma ph_x1 (fx : FPState) Rc Mc modelc LKc crc Ac sk obj ref ba :
  binv [] (XB obj ref ++ ostr sk) Mc modelc LKc crc Ac -> credit_le crmin crc -> rinv2 Rc ->
  getr Rc (reg 10) = Z_to_bv 64 (obj - 32) -> getr Rc (reg 11) = Z_to_bv 64 1 -> xfacts Mc obj ref -> str_at Mc sk ->
  obj_at Mc (F + 96) ba None ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e2d8 Mc modelc) K.
Proof.
  intros BI CRL RI X10 X11 XF ST OA.
  pose proof (pf_of_binv _ _ _ _ _ _ BI) as PF. pose proof BI as (B1 & B2 & _).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  open_pf PF. pose proof RI as ((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21 & X23).
  pose proof (tpX1_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx2 & R2 & M2v & _ & pFR & _ & (pMS & pKS & pR22 & pR24)).
  assert (E2 : M2v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M2v.
  apply (apure ((XB obj ref ++ ostr sk) ++ LB) FF' LKc crc Ac Mc modelc fx fx2 Rc 0x8e2d8 R2 0x8e37c K B1 B2 pMS).
  intros model1 HH1 AM1 RT1 AH1.
  pose proof (binv_model [] _ Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
  apply (ph_xp fx2 R2 Mc model1 LKc crc Ac sk obj ref ba BI1 CRL). 2: exact XF. 2: exact ST. 2: exact OA.
  split. 2:{ rewrite pR22, pR24. split; assumption. }
  apply (rinv2_keep Rc R2 RI). intros k Hk. apply pKS. revert Hk. apply (L5K.incl_b CIDX KS_tpX1). vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma blk_third W obj ref (o : option (Z * Z)) (rest : list (Z * Z)) Mc modelc LKc crc Ac :
  binv W (XB obj ref ++ ostr o ++ rest) Mc modelc LKc crc Ac ->
  match o with None => XB obj ref ++ rest = XB obj ref ++ ostr o ++ rest
             | Some (q, n) => In (q, n) ((XB obj ref ++ ostr o ++ rest) ++ LB) /\ lb_remove q ((XB obj ref ++ ostr o ++ rest) ++ LB) = (XB obj ref ++ rest) ++ LB end.
Proof.
  intros (B1 & _). destruct o as [[q n]|]; cbn [L5ATD.ostr app] in *. 2: reflexivity.
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _). cbn [map fst] in ND.
  destruct (nd_head2 ref (obj - 128) (q :: map fst (rest ++ LB)) q ND (or_introl eq_refl)) as [N1 N2].
  split. right; right; left; reflexivity.
  change ((ref, refsz) :: (obj - 128, objsz) :: (q, n) :: rest ++ LB) with (XB obj ref ++ ((q, n) :: rest ++ LB)).
  rewrite L5ATD.lb_remove_app_skip. rewrite lb_remove_head. reflexivity.
  cbn [map fst]. intros [X|[X|[]]]. apply N1; symmetry; exact X. apply N2; symmetry; exact X.
Qed.

(* [comment removed for export] *)
Lemma ph_xb (fx : FPState) Rc Mc modelc LKc crc Ac sk ob obj ref bb ba :
  binv [] (XB obj ref ++ ostr ob ++ ostr sk) Mc modelc LKc crc Ac -> credit_le crmin crc -> rinB (obj - 32) 1 Rc -> xfacts Mc obj ref -> str_at Mc sk ->
  obj_at Mc (F + 160) bb ob -> obj_at Mc (F + 96) ba None ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e35c Mc modelc) K.
Proof.
  intros BI CRL RI XF ST OB OA.
  apply (dtor_stage (rinB (obj - 32) 1) (rinB (obj - 32) 1) 0x8e35c 0x8e37c (F + 160) (run_XBi _ _) (run_XBd _ _) (rinB_T _ _) (rinB_pres _ _)
           ltac:(split; [clear; lia | reflexivity]) ltac:(left; clear; lia) fx Rc Mc modelc (XB obj ref ++ ostr ob ++ ostr sk) (XB obj ref ++ ostr sk) LKc crc Ac bb ob BI RI OB).
  - pose proof (blk_third [] obj ref ob (ostr sk) Mc modelc LKc crc Ac BI) as X. destruct ob as [[q n]|]. exact X. exact X.
  - intros fx' R' M' model' A' BI' RI' IA' AG'.
    apply (ph_xp fx' R' M' model' LKc crc A' sk obj ref ba BI' CRL (rinB_C _ _ _ RI')).
    + apply (xfacts_cl (ostr ob ++ ostr sk) (ostr sk) Mc modelc LKc crc Ac M' obj ref OPDEL_SCR BI XF AG').
    + apply (str_keep ((XB obj ref ++ ostr sk) ++ LB) OPDEL_SCR Mc M' sk ST). rewrite DEL_EQ; clear; lia. exact AG'.
    + apply (obj_keep ((XB obj ref ++ ostr sk) ++ LB) OPDEL_SCR Mc M' _ _ _ OA). left; clear; lia. rewrite DEL_EQ; clear; lia. exact AG'.
Qed.

(* [comment removed for export] *)
Lemma ph_xa (fx : FPState) Rc Mc modelc LKc crc Ac sk ob ot obj ref bt bb ba :
  binv [] (XB obj ref ++ ostr ot ++ ostr ob ++ ostr sk) Mc modelc LKc crc Ac -> credit_le crmin crc -> rinA (obj - 32) 1 Rc -> xfacts Mc obj ref -> str_at Mc sk ->
  obj_at Mc (F + 224) bt ot -> obj_at Mc (F + 160) bb ob -> obj_at Mc (F + 96) ba None ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e334 Mc modelc) K.
Proof.
  intros BI CRL RI XF ST OT OB OA.
  apply (dtor_stage (rinA (obj - 32) 1) (rinB (obj - 32) 1) 0x8e334 0x8e35c (F + 224) (run_XAi _ _) (run_XAd _ _) (rinB_T _ _) (rinB_pres _ _)
           ltac:(split; [clear; lia | reflexivity]) ltac:(left; clear; lia) fx Rc Mc modelc (XB obj ref ++ ostr ot ++ ostr ob ++ ostr sk) (XB obj ref ++ ostr ob ++ ostr sk) LKc crc Ac bt ot BI RI OT).
  - pose proof (blk_third [] obj ref ot (ostr ob ++ ostr sk) Mc modelc LKc crc Ac BI) as X. destruct ot as [[q n]|]. exact X. exact X.
  - intros fx' R' M' model' A' BI' RI' IA' AG'.
    apply (ph_xb fx' R' M' model' LKc crc A' sk ob obj ref bb ba BI' CRL RI').
    + apply (xfacts_cl (ostr ot ++ ostr ob ++ ostr sk) (ostr ob ++ ostr sk) Mc modelc LKc crc Ac M' obj ref OPDEL_SCR BI XF AG').
    + apply (str_keep ((XB obj ref ++ ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' sk ST). rewrite DEL_EQ; clear; lia. exact AG'.
    + apply (obj_keep ((XB obj ref ++ ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' _ _ _ OB). left; clear; lia. rewrite DEL_EQ; clear; lia. exact AG'.
    + apply (obj_keep ((XB obj ref ++ ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' _ _ _ OA). left; clear; lia. rewrite DEL_EQ; clear; lia. exact AG'.
Qed.
End PAD.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section OBL.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z))
          (V2 cls r SCRT : Z) (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation S := (V2 + cls).
Local Notation SPA := (V2 - 192).
Hypothesis G : L5AFK.gctx L ar HI LB FF LK A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2.
Hypothesis CLS : cls = 0 \/ cls = 16.
Hypothesis V2A : L5ATP2.aligned V2 32.
Hypothesis V2R : 140735332487424 <= V2 <= 140737488355328.
Hypothesis V2S : V2 + cls <= 140737488355328.
Hypothesis HK : K [].
Hypothesis RA : L5.ra_ok r.
Hypothesis UR1 : U R 1 = r.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
Hypothesis G4 : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis G3 : getr R (reg 3) = Z_to_bv 64 67584.
Hypothesis HSCR : 208 + 4096 <= SCRT.
Hypothesis HSCR8 : SCRT mod 8 = 0.
Hypothesis STKSH : L5OMA.stksh ar M (V2 + cls - SCRT).
Hypothesis UNWL : L5USA.as0_unw_layout L.
Hypothesis HS_CATCH : 208 + L5USA.CATCH_SCR <= SCRT.
Local Notation FF' := ((F, 3, V2 - 192 + 32) :: FF).
Local Abbreviation binvL LKx := (L5AFK.binv L ar HI M model LB FF LKx A S SCRT SPA (town V2 cls F R) F 3).

(* [comment removed for export] *)
Lemma gctx_lk LX : L5AFK.gctx L ar HI LB FF (LX ++ LK) A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2.
Proof.
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  constructor; try assumption. intros x Hx. apply in_or_app. right. apply LKI2. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma binv_landed (LX : list fframe) (W1 : list L5.range) BXk BX' Mk modelk LKk crk Ak M' model' LK' cr' A' SCRc (Wc : list L5.range) :
  binvL LK [] BXk Mk modelk LKk crk Ak ->
  ahpres L ar (BXk ++ LB) FF' SPA SCRc Wc Mk M' ->
  ri_inv HI (BX' ++ LB) FF' LK' cr' A' M' (vml_of model') -> amodel_ok A' model' -> model_rt modelk model' -> incl Ak A' -> incl LK' (LX ++ LK) ->
  0 <= SCRc -> S - SCRT <= SPA - SCRc ->
  (forall rr a, In rr Wc -> L5.in_rng rr a -> ~ tocell V2 cls a /\ ~ (F / 8 + SB <= a < F / 8 + SB + 64)) ->
  (forall a, aclient L ar LB FF S SCRT a -> L5.outside W1 a -> L5.outside Wc a) ->
  binvL (LX ++ LK) W1 BX' M' model' LK' cr' A'.
Proof.
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10) AH HH1 AM1 RT1 IA1 ILK1 HS0 HS WAV WOUT.
  unfold L5AFK.binv. split. exact HH1. split. exact AM1. split. eapply L5LZ.model_rt_trans. exact B3. exact RT1.
  split. { intros x Hx. apply IA1. apply B4. exact Hx. } split. exact ILK1.
  split. { apply (astk_after2 L ar C HI HIok _ _ _ _ _ _ _ (BXk ++ LB) FF' Mk Mk M' S SCRT SPA SCRc Wc B1 B6 (mem_grows_refl Mk) AH).
           - exact HS.
           - clear - SPC; lia.
           - clear - SPC; lia. }
  split. { eapply ek_trans. { apply (ek_W L ar LB FF S SCRT W1 [] M Mk B7). intros a _ rr []. }
           apply (ek_callee L ar LB BXk FF [(F, 3, SPA + 32)] S SCRT SPA SCRc W1 Wc Mk M' AH).
           - exact HS.
           - clear - SPC; lia.
           - exact WOUT. }
  split. { eapply dk_trans. exact B8. apply (dk_callee L ar LB BXk FF [(F, 3, SPA + 32)] S SCRT SPA SCRc Wc Mk M' AH).
           - exact HS.
           - clear - SPC; lia. }
  split. { apply (OWNAG Mk M' B9). intros a Ha. pose proof (OCR a Ha) as OC. apply (proj1 AH). split. clear - OC SPC SLO; lia.
           split. apply stack_client. clear - OC SPC SLO SHI SPT; lia. clear - OC SPC HS0; lia.
           intros rr Hr X. exact (proj1 (WAV rr a Hr X) Ha). }
  intros i Hi. apply (proj2 (proj2 AH)).
  - change (ff_bytes 3 / 8) with 64 in Hi. clear - Hi FR F8. unfold SB. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)). change (2 ^ 47 / 8) with 17592186044416 in H0. lia.
  - apply (fframe_shadow_client L ar (BXk ++ LB) FF' SPA SCRc F 3 (SPA + 32)). left; reflexivity. unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). clear - Hi. lia.
  - apply B10. exact Hi.
Qed.

Variable crmin : credit.
Definition UNWW : list L5.range := CWF ++ L5USA.xs_foot1.
Hypothesis KFX : forall (fxf : FPState) Rf Mf modelf LKf Af crf,
      regs_preserved R Rf -> getr Rf (reg 10) = Z_to_bv 64 0 ->
      ahpres L ar LB FF S SCRT UNWW M Mf ->
      (exists st', L5USA.xs_pre ar st' Mf) ->                     (* [comment removed for export] *)
      model_rt model modelf -> incl A Af -> amodel_ok Af modelf -> L5USA.lk_bound LK LKf -> credit_le crmin crf ->
      ri_inv HI LB FF LKf crf Af Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K.
Hypothesis Hcatch1 : L5USA.catch1A_spec L ar HI.
Hypothesis Hcatch2 : L5USA.catch2A_spec L ar HI.
Hypothesis Hcatch3 : L5USA.catch3A_spec L ar HI.
Variables (SCRo K1 K2 : Z) (bytes1 bytes2 : Z -> Z).
Hypothesis HS_OM : 0 <= SCRo /\ 208 + SCRo <= SCRT.
Hypothesis HK1 : 0 <= K1 /\ forall c, 0 <= c -> 0 <= bytes1 c.
Hypothesis HK2 : 0 <= K2 /\ forall c, 0 <= c -> 0 <= bytes2 c.
Local Notation RESTB capb := (8 * capb + bytes2 capb + 8 * Z.max capb 8).
(* [comment removed for export] *)
Hypothesis HCR2 : forall c, 0 <= c -> L5USA.EXC23_SZ + L5USA.REF2_SZ <= bytes1 c + (64 + RESTB c).
Hypothesis HCR3 : forall c, 0 <= c -> L5USA.EXC23_SZ + L5USA.MSG3_SZ + L5USA.REF3_SZ <= 64 + RESTB c.

(* [comment removed for export] *)
Lemma kfb_of (LX : list fframe) (W1 : list L5.range) M' gd av uid rnd canary hw :
  (length LX <= 1)%nat -> Forall (fun f => ff_class f = 1) LX -> dk L ar LB FF S SCRT M M' ->
  (forall a, L5.outside UNWW a -> L5.outside (CWF ++ W1) a) ->
  ek L ar LB FF S SCRT W1 M M' -> L5USA.statics_landed M' gd av uid rnd canary hw -> ar_sptop ar <= av ->
  forall (fxf : FPState) Rf Mf modelf LKf Af crf,
      regs_preserved R Rf -> getr Rf (reg 10) = Z_to_bv 64 0 ->
      ahpres L ar LB FF S SCRT CWF (rebase W1 M M') Mf ->
      L5.u64_at RSEGS Mf L5USA.EH_CAUGHT 0 -> L5.u32_at RSEGS Mf L5USA.EH_UNCAUGHT 0 ->
      model_rt model modelf -> incl A Af -> amodel_ok Af modelf -> incl LKf (LX ++ LK) -> credit_le crmin crf ->
      ri_inv HI LB FF LKf crf Af Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K.
Proof.
  intros LXL LXC DK HW EKL STL AVS fxf Rf Mf modelf LKf Af crf RPf R10f AHf C0f U0f RTf IAf AMf LKIf CRLf HHf.
  apply (KFX fxf Rf Mf modelf LKf Af crf RPf R10f). 3: exact RTf. 3: exact IAf. 3: exact AMf. 4: exact CRLf. 4: exact HHf.
  - apply (ahpres_W LB FF S SCRT (CWF ++ W1) UNWW M Mf). apply (ahpres_rebase LB FF S SCRT W1 CWF M M' Mf AHf DK). exact HW.
  - exists (L5USA.mkXS gd true av uid rnd canary hw).
    destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
    assert (AGD : forall a, xs_dom a -> ~ (6357448 <= a < 6357460) -> Mf (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
    { intros a Hd NC.
      assert (Ha : 0 <= a < 2 ^ 64) by (destruct Hd as [(X & _)|X]; clear - X SPT; lia).
      assert (Hc : aclient L ar LB FF S SCRT a).
      { destruct Hd as [(X & NS)|X]. right; right; left. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY). split. exact X. exact NS.
        right; left. split. clear - X; lia. clear - X SHI HSCR; lia. }
      rewrite (proj1 AHf a).
      2:{ split. exact Ha. split. exact Hc. intros rr [<-|[<-|[]]] X; unfold L5.in_rng, L5USA.EH_CAUGHT, L5USA.EH_UNCAUGHT in X; cbn [fst snd] in X; clear - X NC; lia. }
      rewrite rebase_at by exact Ha. destruct (in_rngsb W1 a) eqn:E. reflexivity. symmetry. apply EKL. split. exact Ha. split. exact Hc. exact (in_rngsb_false W1 a E). }
    apply (statics_xfer M' Mf (fun a => 6357448 <= a < 6357460)). 5: exact STL. 5: exact AVS. 5: exact C0f. 5: exact U0f.
    + intros a Ha NC. apply AGD. exact (xs_cell_dom a UNWL Ha). exact NC.
    + intros a Ha. apply AGD. right; exact Ha. clear - Ha SPT; lia.
    + apply img_clear_dom. intros a Ha. destruct (Z_lt_le_dec a 0xd7000) as [Y|Y]. right; right. apply AGD. exact Ha. clear - Y; lia. left; exact Y.
    + intros a X; exact X.
  - exists LX. split. exact LKIf. split. exact LXL. exact LXC.
Qed.

Local Abbreviation NUM := (L5ATD.NUM L ar HI R LB FF LK A V2 cls SCRT F fl LK2 M2 model2 cr2 G V2R).
Local Abbreviation tcl := (L5ATD.tcl L ar HI R LB FF LK A V2 cls SCRT F fl LK2 M2 model2 cr2 G).
(* [comment removed for export] *)
Lemma wav_frame (W : list L5.range) (lo n : Z) : F + 32 <= lo -> lo + n <= F + 504 ->
  (forall r0, In r0 W -> 65536 <= fst r0 /\ fst r0 + snd r0 <= 6500352) ->
  forall rr a, In rr ((lo, n) :: W) -> L5.in_rng rr a -> ~ tocell V2 cls a /\ ~ (F / 8 + SB <= a < F / 8 + SB + 64).
Proof.
  intros H1 H2 HW rr a Hr Ha. pose proof NUM as (_ & FRP & _ & _ & FBIG & _ & _ & _ & _ & SFB & _).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA FLR FLBIG NCF NCS].
  assert (AR : (F + 32 <= a < F + 504) \/ (65536 <= a < 6500352)).
  { destruct Hr as [<-|Hr]. left. unfold L5.in_rng in Ha; cbn [fst snd] in Ha. clear - Ha H1 H2; lia. right. pose proof (HW rr Hr). unfold L5.in_rng in Ha. clear - Ha H; lia. }
  split.
  - intros OC. pose proof (OCR a OC) as X. clear - X AR SFB SPC SLO SPT. lia.
  - intros X. assert (Y : 2147450880 <= a < 17594333495296).
    { clear - X FRP. unfold SB in X. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    clear - Y AR FBIG. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma wout_frame (W : list L5.range) (lo n : Z) : F <= lo -> lo + n <= F + 512 ->
  forall a, aclient L ar LB FF S SCRT a -> L5.outside W a -> L5.outside ((lo, n) :: W) a.
Proof.
  intros H1 H2 a Hc Ho rr [<-|Hr]. 2: exact (Ho rr Hr).
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA FLR FLBIG NCF NCS].
  intros X. unfold L5.in_rng in X; cbn [fst snd] in X. apply (NCF a). left. change (ff_bytes 3) with 512. clear - X H1 H2; lia. exact Hc.
Qed.
Lemma xs_foot_img : forall rr, In rr L5USA.xs_foot -> 65536 <= fst rr /\ fst rr + snd rr <= 6500352.
Proof. intros rr [<-|[<-|[]]]; unfold L5USA.EH_UNCAUGHT, L5USA.UW_FLAGS; cbn [fst snd]; Lia.lia. Qed.
Lemma xs_foot_sh : forall rr, In rr L5USA.xs_foot -> fst rr + snd rr <= 2147450880.
Proof. intros rr [<-|[<-|[]]]; unfold L5USA.EH_UNCAUGHT, L5USA.UW_FLAGS; cbn [fst snd]; Lia.lia. Qed.
Lemma unww_foot : forall a, L5.outside UNWW a -> L5.outside (CWF ++ L5USA.xs_foot) a.
Proof.
  intros a Ho rr Hr. apply Ho. unfold UNWW. apply in_app_or in Hr. apply in_or_app. destruct Hr as [Hr|Hr]. left; exact Hr. right.
  unfold L5USA.xs_foot, L5USA.xs_foot1 in *. destruct Hr as [<-|[<-|[]]]. left; reflexivity. right; left; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma e2_obl : L5ATD.E2_obl L ar HI R M model K LB FF LK A V2 cls SCRT F crmin L5USA.XS (L5USA.xs_pre ar) L5USA.xs_foot (L5USA.e2_landed L) SCRo K1 K2 bytes1 bytes2.
Proof.
  unfold L5ATD.E2_obl.
  intros fx' Rk Mk modelk LKk crk Ak sk ob bb wb fba fbx st R' M' model' LB' cr' LK' A' OM1 RP XSk LANDED XA' BB' OL' AHP RT IA AM HH'.
  destruct OM1 as (BIk & RIk & XAk & XZk & OBJk & REDk & CAPk & YZk & AOKk & AZk & STk & CRLk).
  destruct LANDED as ((obj & ref & A0 & A1 & _ & ELB & EXC & SL) & CRE & LKI).
  pose proof SL as SL0. destruct SL as (C0 & U1 & _ & _ & SC). destruct SC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & I1 & I2 & _).
  pose proof NUM as ((FRG & FLRG & V2RG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  pose proof BIk as (_ & _ & _ & _ & LKIk & _).
  set (BX' := [(ref, L5USA.REF2_SZ); (obj - 128, L5USA.EXC23_SZ)] ++ L5ATD.ostr None ++ L5ATD.ostr ob ++ L5ATD.ostr sk).
  assert (HHb : ri_inv HI (BX' ++ LB) FF' LK' cr' A' M' (vml_of model')). { subst BX' LB'. cbn [app L5ATD.ostr]. exact HH'. }
  assert (BI' : binvL ([] ++ LK) L5USA.xs_foot BX' M' model' LK' cr' A').
  { apply (binv_landed [] L5USA.xs_foot (L5ATD.ostr ob ++ L5ATD.ostr sk) BX' Mk modelk LKk crk Ak M' model' LK' cr' A' SCRo ((F + 224, 32) :: L5USA.xs_foot) BIk AHP HHb AM RT IA).
    - cbn [app]. intros x Hx. apply LKIk. apply LKI. exact Hx.
    - exact (proj1 HS_OM).
    - clear - HS_OM CLS; lia.
    - apply wav_frame. clear; lia. clear; lia. exact xs_foot_img.
    - apply wout_frame. clear; lia. clear; lia. }
  pose proof BI' as (_ & _ & _ & _ & _ & _ & EK' & DK' & _).
  pose proof (binv_rebase R model LB FF A V2 cls SCRT F M ([] ++ LK) L5USA.xs_foot BX' M' model' LK' cr' A' BI') as BIb.
  assert (AGk : forall i, F + 32 <= i < F + 504 -> ~ (F + 224 <= i < F + 256) -> M' (Z_to_bv 64 i) = Mk (Z_to_bv 64 i)).
  { intros i Hi Hn. apply (proj1 AHP). split. clear - Hi FRP; lia. split. apply tcl. exact (proj1 HS_OM). left; exact Hi.
    intros rr [<-|Hr] X. apply Hn. unfold L5.in_rng in X; cbn [fst snd] in X. clear - X; lia.
    pose proof (xs_foot_img rr Hr) as Y. unfold L5.in_rng in X. clear - X Y Hi FR. lia. }
  assert (CAP0 : 0 <= L5.bo_cap bb). { unfold L5.bo_cap. destruct OBJk as (((_ & _ & _ & OST) & _) & _). destruct (L5.bo_st bb). clear; lia. destruct OST as (_ & _ & _ & _ & X & _). clear - X; lia. }
  assert (LO0 : 0 <= V2 + cls - SCRT) by (clear - SLO SPT; lia). assert (SPT47 : Z.max (ar_sptop ar) (ar_stack_top ar) <= 2 ^ 47).
  { pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (proj1 BI')) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP47 & _). clear - SPT TOP47; lia. }
  apply (ph_xa R (rebase L5USA.xs_foot M M') model K LB FF ([] ++ LK) A V2 cls r SCRT F fl LK2 M2 model2 cr2 (gctx_lk []) CLS V2A V2R V2S HK RA UR1 G2 G4 G3 HSCR HSCR8
           (stksh_rebase L5USA.xs_foot M M' (V2 + cls - SCRT) STKSH LO0 SPT47 xs_foot_sh) UNWL HS_CATCH crmin
           (kfb_of [] L5USA.xs_foot M' _ _ _ _ _ _ ltac:(cbn; lia) ltac:(constructor) DK' unww_foot EK' SL0 (proj2 XSk))
           L5USA.DTOR_RUNTIME_ERROR L5USA.EXC23_SZ L5USA.REF2_SZ Hcatch2 ltac:(unfold L5USA.EXC23_SZ, L5USA.REF2_SZ; clear; lia)
           fx' R' M' model' LK' cr' A' sk ob None obj ref (L5.BO fbx 2 (L5.BInl L5PSA.A0 L5PSA.A1)) bb (L5.BO fba 2 (L5.BInl L5PSA.A0 L5PSA.A1)) BIb).
  - eapply credit_le_trans. exact CRLk. eapply credit_le_trans. 2: exact CRE.
    apply (L5OMA.adebits_le L crk _ _ _ _ (as0_layout2_of L C LY)). clear - HK1 HK2; lia. apply HCR2. exact CAP0.
  - split. apply (rinvY_pres R V2 cls F Rk R' RIk RP). split. rewrite <- r10. exact A0. rewrite <- r11. exact A1.
  - split. exact EXC. split. exact C0. split. exact U1. split. exact I1. exact I2.
  - apply (L5ATD.str_agree L ar HI R LB FF LK A V2 cls SCRT F fl LK2 M2 model2 cr2 G V2R Mk M' sk STk). intros i Hi. apply AGk. clear - Hi; lia. clear - Hi; lia.
  - split. exact (proj1 XA'). reflexivity.
  - split. exact BB'. exact (proj2 (proj1 OBJk)).
  - split. 2: reflexivity. eapply L5C.big_at_agree. 4: exact (proj1 AOKk). intros i Hi. apply AGk. clear - Hi; lia. clear - Hi; lia. clear - FRP; lia. clear - FRP; lia.
Qed.

(* [comment removed for export] *)
Lemma e3_obl : L5ATD.E3_obl L ar HI R M model K LB FF LK A V2 cls SCRT F crmin L5USA.XS (L5USA.xs_pre ar) L5USA.xs_foot (L5USA.e3_landed L) SCRo K1 K2 bytes1 bytes2.
Proof.
  unfold L5ATD.E3_obl.
  intros fx' Rk Mk modelk LKk crk Ak sk ob bb wb fba fbx st R' M' model' LB' cr' LK' A' fbx' nx qx cr1 OM1 RP XSk XD' FRQ CRA LANDED BB' OL' AHP RT IA AM HH'.
  destruct OM1 as (BIk & RIk & XAk & XZk & OBJk & REDk & CAPk & YZk & AOKk & AZk & STk & CRLk).
  destruct LANDED as ((obj & ref & A0 & A1 & _ & ELB & EXC & SL) & CRE & (f & LKm & ELK & CF & ILK)).
  pose proof SL as SL0. destruct SL as (C0 & U1 & _ & _ & SC). destruct SC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & I1 & I2 & _).
  pose proof NUM as ((FRG & FLRG & V2RG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  pose proof BIk as (_ & _ & _ & _ & LKIk & _).
  set (BX' := [(ref, L5USA.REF3_SZ); (obj - 128, L5USA.EXC23_SZ)] ++ L5ATD.ostr (Some (qx, 64)) ++ L5ATD.ostr ob ++ L5ATD.ostr sk).
  assert (HHb : ri_inv HI (BX' ++ LB) FF' LK' cr' A' M' (vml_of model')). { subst BX' LB'. cbn [app L5ATD.ostr]. exact HH'. }
  assert (BI' : binvL ([f] ++ LK) L5USA.xs_foot BX' M' model' LK' cr' A').
  { apply (binv_landed [f] L5USA.xs_foot (L5ATD.ostr ob ++ L5ATD.ostr sk) BX' Mk modelk LKk crk Ak M' model' LK' cr' A' SCRo ((F + 224, 32) :: L5USA.xs_foot) BIk AHP HHb AM RT IA).
    - subst LK'. cbn [app]. intros x [<-|Hx]. left; reflexivity. right. apply LKIk. apply ILK. exact Hx.
    - exact (proj1 HS_OM).
    - clear - HS_OM CLS; lia.
    - apply wav_frame. clear; lia. clear; lia. exact xs_foot_img.
    - apply wout_frame. clear; lia. clear; lia. }
  pose proof BI' as (_ & _ & _ & _ & _ & _ & EK' & DK' & _).
  pose proof (binv_rebase R model LB FF A V2 cls SCRT F M ([f] ++ LK) L5USA.xs_foot BX' M' model' LK' cr' A' BI') as BIb.
  assert (AGk : forall i, F + 32 <= i < F + 504 -> ~ (F + 224 <= i < F + 256) -> M' (Z_to_bv 64 i) = Mk (Z_to_bv 64 i)).
  { intros i Hi Hn. apply (proj1 AHP). split. clear - Hi FRP; lia. split. apply tcl. exact (proj1 HS_OM). left; exact Hi.
    intros rr [<-|Hr] X. apply Hn. unfold L5.in_rng in X; cbn [fst snd] in X. clear - X; lia.
    pose proof (xs_foot_img rr Hr) as Y. unfold L5.in_rng in X. clear - X Y Hi FR. lia. }
  assert (CAP0 : 0 <= L5.bo_cap bb). { unfold L5.bo_cap. destruct OBJk as (((_ & _ & _ & OST) & _) & _). destruct (L5.bo_st bb). clear; lia. destruct OST as (_ & _ & _ & _ & X & _). clear - X; lia. }
  assert (LO0 : 0 <= V2 + cls - SCRT) by (clear - SLO SPT; lia). assert (SPT47 : Z.max (ar_sptop ar) (ar_stack_top ar) <= 2 ^ 47).
  { pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (proj1 BI')) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP47 & _). clear - SPT TOP47; lia. }
  assert (LXC : Forall (fun g => ff_class g = 1) [f]). { constructor. exact CF. constructor. }
  apply (ph_xa R (rebase L5USA.xs_foot M M') model K LB FF ([f] ++ LK) A V2 cls r SCRT F fl LK2 M2 model2 cr2 (gctx_lk [f]) CLS V2A V2R V2S HK RA UR1 G2 G4 G3 HSCR HSCR8
           (stksh_rebase L5USA.xs_foot M M' (V2 + cls - SCRT) STKSH LO0 SPT47 xs_foot_sh) UNWL HS_CATCH crmin
           (kfb_of [f] L5USA.xs_foot M' _ _ _ _ _ _ ltac:(cbn; lia) LXC DK' unww_foot EK' SL0 (proj2 XSk))
           L5USA.DTOR_RUNTIME_ERROR L5USA.EXC23_SZ L5USA.REF3_SZ Hcatch3 ltac:(unfold L5USA.EXC23_SZ, L5USA.REF3_SZ; clear; lia)
           fx' R' M' model' LK' cr' A' sk ob (Some (qx, 64)) obj ref (L5.BO fbx' nx (L5.BDyn 8 qx)) bb (L5.BO fba 2 (L5.BInl L5PSA.A0 L5PSA.A1)) BIb).
  - eapply credit_le_trans. exact CRLk. eapply credit_le_trans. 2: exact CRE.
    eapply credit_le_trans. 2:{ apply (L5OMA.adebits_mono L _ _ 3 _ CRA). } rewrite L5OMA.adebits_add.
    apply (L5OMA.adebits_le L crk _ _ _ _ (as0_layout2_of L C LY)). clear - HK1 HK2; lia. pose proof (HCR3 _ CAP0) as X. clear - X. lia.
  - split. apply (rinvY_pres R V2 cls F Rk R' RIk RP). split. rewrite <- r10. exact A0. rewrite <- r11. exact A1.
  - split. exact EXC. split. exact C0. split. exact U1. split. exact I1. exact I2.
  - apply (L5ATD.str_agree L ar HI R LB FF LK A V2 cls SCRT F fl LK2 M2 model2 cr2 G V2R Mk M' sk STk). intros i Hi. apply AGk. clear - Hi; lia. clear - Hi; lia.
  - split. exact XD'. reflexivity.
  - split. exact BB'. exact (proj2 (proj1 OBJk)).
  - split. 2: reflexivity. eapply L5C.big_at_agree. 4: exact (proj1 AOKk). intros i Hi. apply AGk. clear - Hi; lia. clear - Hi; lia. clear - FRP; lia. clear - FRP; lia.
Qed.

(* [comment removed for export] *)
Variables (IL : icpt_layout) (SCRs : Z) (st0 : L5USA.XS).
Hypothesis He1 : L5USA.e1_chainA_spec L ar HI IL.
Hypothesis HS_SC : 0 <= SCRs /\ 208 + SCRs <= SCRT.
Hypothesis HS_E1 : L5USA.CHAIN_SCR <= SCRs.
Hypothesis HSCs8 : SCRs mod 8 = 0.
Hypothesis XSPX : forall Mk, L5ATD.img_same L ar M Mk -> L5USA.xs_pre ar st0 Mk.
Local Notation REST capb := (bytes1 capb + (64 + RESTB capb)).

Lemma wav_img (W : list L5.range) : (forall r0, In r0 W -> 65536 <= fst r0 /\ fst r0 + snd r0 <= 6500352) ->
  forall rr a, In rr W -> L5.in_rng rr a -> ~ tocell V2 cls a /\ ~ (F / 8 + SB <= a < F / 8 + SB + 64).
Proof.
  intros HW rr a Hr Ha. pose proof NUM as (_ & FRP & _).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA FLR FLBIG NCF NCS].
  assert (AR : 65536 <= a < 6500352). { pose proof (HW rr Hr). unfold L5.in_rng in Ha. clear - Ha H; lia. }
  split.
  - intros OC. pose proof (OCR a OC) as X. clear - X AR SPC SLO SPT. lia.
  - intros X. assert (Y : 2147450880 <= a). { clear - X FRP. unfold SB in X. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    clear - Y AR. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma xs_foot1_img : forall rr, In rr L5USA.xs_foot1 -> 65536 <= fst rr /\ fst rr + snd rr <= 6500352.
Proof. intros rr [<-|[<-|[<-|[<-|[]]]]]; unfold L5USA.EH_UNCAUGHT, L5USA.UW_FLAGS, L5USA.SYSCAT_GUARD, L5USA.ERRNO; cbn [fst snd]; Lia.lia. Qed.
Lemma xs_foot1_sh : forall rr, In rr L5USA.xs_foot1 -> fst rr + snd rr <= 2147450880.
Proof. intros rr Hr. pose proof (xs_foot1_img rr Hr). Lia.lia. Qed.
Lemma unww_foot1 : forall a, L5.outside UNWW a -> L5.outside (CWF ++ L5USA.xs_foot1) a.
Proof. intros a Ho. exact Ho. Qed.
Lemma parse_debit_eq cr m : L5PSA.parse_debit L cr m = L5OMA.adebits L cr 2 (2 * L5PSA.vblk m).
Proof. unfold L5PSA.parse_debit, L5OMA.adebits, adebit. cbn [fst snd]. f_equal; ring. Qed.

Lemma e1_obl : L5ATD.E1_obl L ar HI R M model K LB FF LK A V2 cls SCRT F crmin K1 K2 bytes1 bytes2 SCRs.
Proof.
  unfold L5ATD.E1_obl.
  intros fx' Rk Mk modelk LKk crk Ak sk s fba fbo R' M' model' cr' LK' A' SCS TS RT IA AM LKI HH'.
  destruct SCS as (BIk & RIk & RA1 & AOKk & AZk & XZk & YZk & SFk & SZSk & BZk & CRLk & CRFk).
  destruct TS as (NP & T2 & T8 & T9 & T18 & TKS & C8 & C16 & C24 & C32 & OB & OBZ & CRT & ASTK & AHP1).
  pose proof NUM as ((FRG & FLRG & V2RG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  pose proof BIk as (_ & _ & _ & _ & LKIk & _).
  pose proof RIk as ((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21 & X23).
  set (m := length (snd (L5PSA.split_sign s))) in *. set (vb := L5PSA.vblk m) in *.
  assert (LY2 : as0_layout2 L) by (exact (as0_layout2_of L C LY)).
  assert (VB0 : 0 <= vb). { subst vb. unfold L5PSA.vblk. destruct (m <? 39)%nat. clear; lia. unfold round_up. pose proof (Z.div_pos (Z.of_nat (num_words_est m)) 8 ltac:(clear; lia) ltac:(clear; lia)) as X. clear - X; lia. }
  assert (RB0 : 201 <= REST 268). { pose proof (proj2 HK1 268 ltac:(clear; Lia.lia)). pose proof (proj2 HK2 268 ltac:(clear; Lia.lia)). clear - H H0. lia. }
  (* [comment removed for export] *)
  assert (BI1 : binvL ([] ++ LK) [] (L5ATD.ostr sk) M' model' LK' cr' A').
  { apply (binv_landed [] [] (L5ATD.ostr sk) (L5ATD.ostr sk) Mk modelk LKk crk Ak M' model' LK' cr' A' SCRs [(F + 160, 32)] BIk AHP1 HH' AM RT IA).
    - cbn [app]. intros x Hx. apply LKIk. apply LKI. exact Hx.
    - exact (proj1 HS_SC).
    - clear - HS_SC CLS; lia.
    - apply wav_frame. clear; lia. clear; lia. intros r0 [].
    - apply wout_frame. clear; lia. clear; lia. }
  cbn [app] in BI1.
  assert (AG1 : forall i, F + 32 <= i < F + 504 -> ~ (F + 160 <= i < F + 192) -> M' (Z_to_bv 64 i) = Mk (Z_to_bv 64 i)).
  { intros i Hi Hn. apply (proj1 AHP1). split. clear - Hi FRP; lia. split. apply tcl. exact (proj1 HS_SC). left; exact Hi.
    intros rr [<-|[]] X. apply Hn. unfold L5.in_rng in X; cbn [fst snd] in X. clear - X; lia. }
  (* [comment removed for export] *)
  assert (IS1 : L5ATD.img_same L ar M M').
  { pose proof (L5ATD.img_same_now L ar C HI LY R M model LB FF LK A V2 cls SCRT F fl LK2 M2 model2 cr2 G _ _ _ _ _ _ BI1) as X. exact X. }
  assert (SH1 : L5OMA.stksh ar M' (SPA - SCRs)).
  { apply (L5ATD.stksh_now L ar C HI HIok R M model LB FF LK A V2 cls SCRT F fl LK2 M2 model2 cr2 G CLS V2A V2R STKSH HSCR8 _ M' model' LK' cr' A' (SPA - SCRs) BI1).
    clear - HS_SC CLS; lia. clear - V2A HSCs8. unfold L5ATP2.aligned in V2A. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (CRF1 : L5OMA.acredit_for L cr' 2 (L5USA.EXC1_SZ + L5USA.REF1_SZ)).
  { apply (L5OMA.acredit_for_mono L (L5OMA.adebits L crk 2 (2 * vb)) cr'). 2:{ pose proof CRT as X. rewrite parse_debit_eq in X. exact X. }
    destruct (L5OMA.acredit_for_split L crk (2 + (K1 + K2 + 3)) (2 * vb + REST 268) 2 (2 * vb) LY2 CRFk ltac:(clear - HK1 HK2; lia) ltac:(clear - VB0 RB0; lia)) as [_ X].
    apply (L5OMA.acredit_for_le L _ _ _ _ _ LY2 X). clear - HK1 HK2; lia. unfold L5USA.EXC1_SZ, L5USA.REF1_SZ. clear - RB0; lia. }
  pose proof BI1 as (_ & AM1 & _).
  apply (He1 fx' R' M' model' K (L5ATD.ostr sk ++ LB) FF' LK' cr' A' SPA SCRs (U Rk 8) (U Rk 18) st0).
  - rewrite r2. exact T2.
  - replace (3%bv : bv 5) with (reg 3) by (apply bv_eq; reflexivity). rewrite (TKS 3%nat) by inl. rewrite X3. exact G3.
  - rewrite r4. rewrite (TKS 4%nat) by inl. rewrite X4. exact G4.
  - replace (9%bv : bv 5) with (reg 9) by (apply bv_eq; reflexivity). exact T9.
  - replace (18%bv : bv 5) with (reg 18) by (apply bv_eq; reflexivity). exact T18.
  - exact (proj1 (spa_facts V2 SCRT V2A HSCR8)).
  - rewrite RA1 in C8. rewrite L5.unsigned_lit in C8 by (clear; lia). exact C8.
  - exact C16.
  - rewrite X9 in C24. rewrite L5.unsigned_lit in C24 by (clear - V2R; lia). exact C24.
  - exact C32.
  - apply UR.
  - apply UR.
  - apply XSPX. exact IS1.
  - exact HH'.
  - exact AM.
  - exact HK.
  - exact ASTK.
  - exact HS_E1.
  - exact HSCs8.
  - exact SH1.
  - exact CRF1.
  - intros fx2 R2 M2' model2' LB2 cr2' LK2' A2 Y8 Y9 Y18 YKS LANDED AHP2 RT2 IA2 AM2 HH2'.
    destruct LANDED as ((obj & ref & A0 & A1 & A2' & ELB & EXC & SL) & CRE & LKI2').
    pose proof SL as SL0. destruct SL as (C0 & U1 & _ & _ & SC). destruct SC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & I1 & I2 & _).
    set (BX' := [(ref, L5USA.REF1_SZ); (obj - 128, L5USA.EXC1_SZ)] ++ L5ATD.ostr sk).
    assert (HHb : ri_inv HI (BX' ++ LB) FF' LK2' cr2' A2 M2' (vml_of model2')). { subst BX' LB2. cbn [app]. exact HH2'. }
    assert (BI2 : binvL ([] ++ LK) L5USA.xs_foot1 BX' M2' model2' LK2' cr2' A2).
    { apply (binv_landed [] L5USA.xs_foot1 (L5ATD.ostr sk) BX' M' model' LK' cr' A' M2' model2' LK2' cr2' A2 SCRs L5USA.xs_foot1 BI1 AHP2 HHb AM2 RT2 IA2).
      - cbn [app]. intros x Hx. apply LKIk. apply LKI. apply LKI2'. exact Hx.
      - exact (proj1 HS_SC).
      - clear - HS_SC CLS; lia.
      - apply wav_img. exact xs_foot1_img.
      - intros a _ X. exact X. }
    pose proof BI2 as (_ & _ & _ & _ & _ & _ & EK2 & DK2 & _).
    pose proof (binv_rebase R model LB FF A V2 cls SCRT F M ([] ++ LK) L5USA.xs_foot1 BX' M2' model2' LK2' cr2' A2 BI2) as BIb.
    assert (AG2 : forall i, F + 32 <= i < F + 504 -> M2' (Z_to_bv 64 i) = M' (Z_to_bv 64 i)).
    { intros i Hi. apply (proj1 AHP2). split. clear - Hi FRP; lia. split. apply tcl. exact (proj1 HS_SC). left; exact Hi.
      intros rr Hr X. pose proof (xs_foot1_img rr Hr) as Y. unfold L5.in_rng in X. clear - X Y Hi FR. lia. }
    assert (LO0 : 0 <= V2 + cls - SCRT) by (clear - SLO SPT; lia). assert (SPT47 : Z.max (ar_sptop ar) (ar_stack_top ar) <= 2 ^ 47).
  { pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (proj1 BI2)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP47 & _). clear - SPT TOP47; lia. }
    apply (ph_x1 R (rebase L5USA.xs_foot1 M M2') model K LB FF ([] ++ LK) A V2 cls r SCRT F fl LK2 M2 model2 cr2 (gctx_lk []) CLS V2A V2R V2S HK RA UR1 G2 G4 G3 HSCR HSCR8
             (stksh_rebase L5USA.xs_foot1 M M2' (V2 + cls - SCRT) STKSH LO0 SPT47 xs_foot1_sh) UNWL HS_CATCH crmin
             (kfb_of [] L5USA.xs_foot1 M2' _ _ _ _ _ _ ltac:(cbn; lia) ltac:(constructor) DK2 unww_foot1 EK2 SL0 (proj2 (XSPX M' IS1)))
             L5USA.DTOR_SYSTEM_ERROR L5USA.EXC1_SZ L5USA.REF1_SZ Hcatch1 ltac:(unfold L5USA.EXC1_SZ, L5USA.REF1_SZ; clear; lia)
             fx2 R2 M2' model2' LK2' cr2' A2 sk obj ref (L5.BO fba 2 (L5.BInl L5PSA.A0 L5PSA.A1)) BIb).
    + eapply credit_le_trans. exact CRLk. eapply credit_le_trans. 2: exact CRE.
      pose proof CRT as CRT'. rewrite parse_debit_eq in CRT'. eapply credit_le_trans. 2:{ apply (L5OMA.adebits_mono L _ _ 2 _ CRT'). } rewrite L5OMA.adebits_add.
      apply (L5OMA.adebits_le L crk _ _ _ _ LY2). clear - HK1 HK2; lia. unfold L5USA.EXC1_SZ, L5USA.REF1_SZ. fold m. fold vb. clear - RB0. lia.
    + apply (rinv2_keep R V2 cls F Rk R2 RIk). intros k Hk0. unfold CIDX in Hk0. cbn [In] in Hk0.
      destruct Hk0 as [<-|[<-|[<-|[<-|[<-|[<-|Hk0]]]]]].
      * rewrite <- r2. rewrite A2'. symmetry. exact X2.
      * rewrite (YKS 3%nat) by inl. apply (TKS 3%nat). inl.
      * rewrite (YKS 4%nat) by inl. apply (TKS 4%nat). inl.
      * replace (reg 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Y8. replace (8%bv : bv 5) with (reg 8) by (apply bv_eq; reflexivity). symmetry. apply U_to.
      * replace (reg 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Y9. replace (9%bv : bv 5) with (reg 9) by (apply bv_eq; reflexivity). symmetry. exact X9.
      * replace (reg 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Y18. replace (18%bv : bv 5) with (reg 18) by (apply bv_eq; reflexivity). symmetry. apply U_to.
      * repeat (destruct Hk0 as [<-|Hk0]; [rewrite (YKS _) by inl; apply (TKS _); inl|]). destruct Hk0.
    + rewrite <- r10. exact A0.
    + rewrite <- r11. exact A1.
    + split. exact EXC. split. exact C0. split. exact U1. split. exact I1. exact I2.
    + apply (L5ATD.str_agree L ar HI R LB FF LK A V2 cls SCRT F fl LK2 M2 model2 cr2 G V2R M' M2' sk). 2:{ intros i Hi. apply AG2. clear - Hi; lia. }
      apply (L5ATD.str_agree L ar HI R LB FF LK A V2 cls SCRT F fl LK2 M2 model2 cr2 G V2R Mk M' sk (L5ATD.str_full_at F Mk sk s SFk)). intros i Hi. apply AG1. clear - Hi; lia. clear - Hi; lia.
    + split. 2: reflexivity. eapply L5C.big_at_agree. 4:{ eapply L5C.big_at_agree. 4: exact (proj1 AOKk). intros i Hi. apply AG1. clear - Hi; lia. clear - Hi; lia. clear - FRP; lia. clear - FRP; lia. }
      intros i Hi. apply AG2. clear - Hi; lia. clear - FRP; lia. clear - FRP; lia.
Qed.

(* [comment removed for export] *)
Theorem pads_okX : L5ATD.pads_ok L ar HI R M model K LB FF LK A V2 cls SCRT F crmin L5USA.XS (L5USA.xs_pre ar) L5USA.xs_foot (L5USA.e2_landed L) (L5USA.e3_landed L) SCRo K1 K2 bytes1 bytes2 SCRs.
Proof. split. exact e1_obl. split. exact e2_obl. exact e3_obl. Qed.
End OBL.
End WithIface.
End SCFG_1.
End L5ATX.
