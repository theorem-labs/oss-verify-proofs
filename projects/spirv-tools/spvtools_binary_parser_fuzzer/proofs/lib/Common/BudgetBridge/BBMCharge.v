(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (mremap's charge over the cut source range, proved as text in place of the recorded proof). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mremap.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Common.BudgetBridge Require Import BBCut.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BBMCharge () := "C47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List6filterI47Corelib4Init9Datatypes4list00I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith4Znat5Nat2Z8inj_succI47Corelib4Init9Datatypes4bool00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State:map_removeC46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C4ELinuxProcessSemantics?LinuxProcessSem5State>vm_backed_mapsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm6MremapDmremap_source_lazy_bC4ELinuxProcessSemantics?LinuxProcessSem5State=lazy_interiorC4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem5State>move_page_baseC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem5StateBpage_outside_rangeC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm6MremapAmremap_word_rangeC4ELinuxProcessSemantics?LinuxProcessSem5StateAmaps_subtract_allC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm6MremapHmaps_subtract_all_withinI47Corelib4Init5Logic2ex00C4ELinuxProcessSemantics?LinuxProcessSem5State>region_free_InC4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6ltb_geK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K47Corelib4Init5Logic3and01C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib6Common<BudgetBridge5BBCut>cut_split_liveC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common<BudgetBridge9BBMCharge=filter_len_leC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesC47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflK46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib5Lists4List:length_mapC47Corelib4Init5Logic5proj2C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm6MremapHlive_bytes_subtract_freeC69OSSVerify5KrLib6Common<BudgetBridge5BBCut=ms_within_nilC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm6MremapAmaps_subtract_appC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm6MremapElazy_interior_alignedC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm6MremapOlive_bytes_maps_subtract_all_leK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm6Mremap>live_bytes_appC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm6MremapEmaps_subtract_all_appC46Stdlib5Lists4List:length_appC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm6MremapAmremap_model_nextC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm6MremapBmremap_move_chargeC56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC4ELinuxProcessSemantics?LinuxProcessSem5StateApage_in_half_openC56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic3and00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6mkapp2C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I47Corelib4Init5Logic5False00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma filter_len_le : forall {A} (f : A -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_BBMCharge ()) [] "p'0h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with61lh73IH0h84cstrh95cstr0h:1xh;1Ah<2IHh=1bi001bh>1fp;1p;3p;2p;4p;5p;<p;7p;8p200R0g0000R1p4p710p8P0g000RR2p4p710p8P0g0012R3p4p710p8g001Mj16TP3j33TP2j20Tg001mR2j21Tg002GR3j22Tg002cj27Tg003=j1ATg003]j1OTg004;j1LTg004Yj1ITg005Dj2DTg005gj2WTg006Ij2VTg0075j3UTg007Oj3TTg007nj4RTg008`j4;Tg009Kj3<Tg009kR4j1=Tg00:JR5j14Tg00:jj1PTg00;Hj25Tg00;ej4NTg00<Lj1?Tg00=1j2KTg00=Oj4JTg00=mj2>Tg00>Pj1HTg00?5j1MTg00?Wj3CTP1j5GTg00@:l<ETg00@_j4FTg00AJj7STg00Anl<YTg00BSj8XTg00C7R1g00CVR6P2P5P3g00D4R7g00DVR8g00E5R9f1R:P8P9f0R;M<Ep=QP6P:g00ESP;CFp=8P:g00F:R<g00FYR=P=g00G9R>P;g00GYFSp=9P1P1P6P6P4P5P5f3R4g00H9f2R?P:P;M<Yp=@P1P6P2P5P3P7f5R7f4R3P4P?P:P;M<Ep=:P4P<P=P=P>P?P:P;GXp=Bg00H]R<\;%6:P?%6?A34?;,04104;'1W611881299R81769R5/Q5g00I=R5#AR2%65R5%O6R1%L6R@%I6RA1D69RB/8B'91WA>R>P;P?g00IiRB,7<1V;?=U<BdAT69:CRRBb3b4b5P8P;b2C;%A?R893?:,0?10?8'1e%64A334;,03103;'1P3P?O1P<P<f7R8P<f8R<#6P;f6RC=384RD9<83PDn0100000020000'01084#='1P;A3C7?RE,0CRF#=RG10C?RH#=RI'1%4FRJg00JIRK#PRL'5RM%4HRN/5LRO'2PGPM15;LX:6RMPFPJ176JRGC@PIPOPMPHPN176NRMC@RPE:11FH12JNRQPFPJPGPHPNPME:P:CNRMPQ108DRD#?R8%4D,29RD10<3R<#?RN%4<,29R9P2P5P61K6?P:P1CJR1P@PA1>6KR<%HK,>6RK'8,9ARH%M=R=1D6LRR9C6<AC6KRRR'8,9ACBP>PBb3b4b5X06X1612;:RK15:L15?LRL'2[^06^16P;f:RS/0C#4f9=3SC,0S#4P4O3RSb2b9b8b7C;A<C4E,0C/1Ie11FIRC12JOPFPJPGPIPOPPE:PMPQP8PDPNP9P2P5P1P@PAPHP=18<R,9ACBP>PBb3b4b5X06X1612:L\K^06^16PSb2b9b8b7C;PCen0110000020101b=A<7?:R:9373,07107:'1eW<W6X:?P;DGW6W>X;0o"). Qed.

(* ---------------------------------------------------------------------
   PLAIN TEXT, not a replay.  At the revision [Mremap.mremap_maps_next] and
   [Mremap.mremap_move_charge] cut the source RANGE out of [vm_maps]
   ([maps_subtract]) where they used to remove the entry based at [old]
   ([map_remove]), so the serialised proof of [charge_dst_le] no longer
   replays; its two ledger premises are restated over the cut, as the
   model's own [Mremap.mremap_move_charge_at_fresh] states them.

   The proof needs one fact the model's equality does not (it assumes the
   lazy ledger misses the destination, [Hlazy] there): cutting a list that
   misses [D = [dlo, dhi)] by [KL] with [D] cut out of it removes the same
   bytes as cutting it by [KL] ([cut_restrict]).  [iv_subtract] can leave
   zero-length pieces, so the lists agree only after those are dropped
   ([nzf]); the byte count does not see them ([live_nzf]).
   --------------------------------------------------------------------- *)

Definition nzf (l : list (word * word)) : list (word * word) :=
  List.filter (fun e => negb (bv_unsigned (snd e) =? 0)%Z) l.

Lemma nzf_app : forall l1 l2, nzf (l1 ++ l2) = nzf l1 ++ nzf l2.
Proof. intros l1 l2. unfold nzf. apply filter_app. Qed.

Lemma live_nzf : forall l, live_bytes (nzf l) = live_bytes l.
Proof.
  induction l as [|[a s] l IH]; [reflexivity|].
  unfold nzf in *. cbn [List.filter snd].
  destruct (bv_unsigned s =? 0)%Z eqn:E; cbn [negb live_bytes].
  - apply Z.eqb_eq in E. rewrite IH, E. lia.
  - rewrite IH. reflexivity.
Qed.

Lemma nzf_idem : forall l, nzf (nzf l) = nzf l.
Proof.
  induction l as [|[a s] l IH]; [reflexivity|].
  unfold nzf in *. cbn [List.filter snd].
  destruct (bv_unsigned s =? 0)%Z eqn:E; cbn [negb List.filter snd]; [exact IH|].
  rewrite E. cbn [negb]. rewrite IH. reflexivity.
Qed.

Lemma nzf_cons : forall (a s : word) l,
  nzf ((a, s) :: l) = if (bv_unsigned s =? 0)%Z then nzf l else (a, s) :: nzf l.
Proof. intros a s l. unfold nzf. cbn [List.filter snd]. destruct (bv_unsigned s =? 0)%Z; reflexivity. Qed.

Lemma nzf_nil_of_live0 : forall l, (live_bytes l <= 0)%Z -> nzf l = [].
Proof.
  induction l as [|[a s] l IH]; intros H; [reflexivity|].
  cbn [live_bytes] in H. pose proof (mremap_word_range s). pose proof (live_bytes_nonneg l).
  rewrite nzf_cons. rewrite (proj2 (Z.eqb_eq (bv_unsigned s) 0) ltac:(lia)). apply IH. lia.
Qed.

Lemma iv_subtract_nzf_zero : forall (a sz : word) lo hi,
  (lo <= hi)%Z -> bv_unsigned sz = 0%Z -> nzf (iv_subtract a sz lo hi) = [].
Proof.
  intros a sz lo hi Hlh Hz. apply nzf_nil_of_live0.
  pose proof (live_bytes_iv_subtract_le a sz lo hi Hlh). lia.
Qed.

Lemma nzf_maps_subtract : forall l lo hi, (lo <= hi)%Z ->
  nzf (maps_subtract l lo hi) = nzf (maps_subtract (nzf l) lo hi).
Proof.
  induction l as [|[a s] l IH]; intros lo hi Hlh; [reflexivity|].
  cbn [maps_subtract]. rewrite nzf_app, (IH lo hi Hlh), nzf_cons.
  destruct (bv_unsigned s =? 0)%Z eqn:E.
  - apply Z.eqb_eq in E. rewrite (iv_subtract_nzf_zero a s lo hi Hlh E). reflexivity.
  - cbn [maps_subtract]. rewrite nzf_app. reflexivity.
Qed.

Lemma nzf_maps_subtract_all : forall C l,
  nzf (maps_subtract_all l C) = nzf (maps_subtract_all (nzf l) C).
Proof.
  induction C as [|[c cs] C IH]; intros l.
  - cbn [maps_subtract_all]. symmetry. apply nzf_idem.
  - cbn [maps_subtract_all].
    rewrite (IH (maps_subtract l (bv_unsigned c) (bv_unsigned c + bv_unsigned cs))).
    rewrite (IH (maps_subtract (nzf l) (bv_unsigned c) (bv_unsigned c + bv_unsigned cs))).
    pose proof (mremap_word_range cs).
    rewrite (nzf_maps_subtract l (bv_unsigned c) (bv_unsigned c + bv_unsigned cs)) by lia.
    reflexivity.
Qed.

Lemma msa_cuts_app : forall C1 C2 l,
  maps_subtract_all l (C1 ++ C2) = maps_subtract_all (maps_subtract_all l C1) C2.
Proof. induction C1 as [|[c cs] C1 IH]; intros C2 l; [reflexivity|]. cbn [app maps_subtract_all]. apply IH. Qed.

(* a list every entry of which misses [lo', hi'): the cut leaves it (its
   non-empty entries) as it is *)
Lemma nzf_ms_disjoint : forall X lo' hi', (lo' <= hi')%Z ->
  (forall b s, In (b, s) X -> (bv_unsigned b + bv_unsigned s <= lo' \/ hi' <= bv_unsigned b)%Z) ->
  nzf (maps_subtract X lo' hi') = nzf X.
Proof.
  induction X as [|[b s] X IH]; intros lo' hi' Hlh HX; [reflexivity|].
  cbn [maps_subtract]. rewrite nzf_app.
  rewrite (IH lo' hi' Hlh) by (intros b' s' H; apply HX; right; exact H).
  rewrite nzf_cons.
  destruct (Z.eq_dec (bv_unsigned s) 0) as [Hz|Hz].
  - rewrite (iv_subtract_nzf_zero b s lo' hi' Hlh Hz). rewrite (proj2 (Z.eqb_eq _ _) Hz). reflexivity.
  - pose proof (mremap_word_range s).
    rewrite (iv_subtract_disjoint b s lo' hi') by (try lia; apply HX; left; reflexivity).
    rewrite nzf_cons, (proj2 (Z.eqb_neq _ _) Hz). reflexivity.
Qed.

(* every entry inside [lo, hi): the cut leaves nothing *)
Lemma ms_inside_nil : forall l lo hi,
  (forall b s, In (b, s) l -> lo <= bv_unsigned b /\ bv_unsigned b + bv_unsigned s <= hi)%Z ->
  maps_subtract l lo hi = [].
Proof.
  induction l as [|[b s] l IH]; intros lo hi H; [reflexivity|].
  cbn [maps_subtract]. destruct (H b s (or_introl eq_refl)) as [H1 H2].
  rewrite IH by (intros b' s' Hin; apply H; right; exact Hin).
  unfold iv_subtract. cbv zeta.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned b) lo) H1), (proj2 (Z.ltb_ge hi (bv_unsigned b + bv_unsigned s)) H2).
  reflexivity.
Qed.

(* ONE entry that misses [D = [lo, hi)], ONE cut: the cut's pieces outside
   [D] remove from the entry what the whole cut removes *)
Lemma pe_cut : forall (b s c cs : word) lo hi,
  (0 <= lo)%Z -> (lo <= hi)%Z -> (hi < two_pow_64)%Z ->
  (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b)%Z ->
  nzf (maps_subtract_all [(b, s)] (iv_subtract c cs lo hi))
  = nzf (iv_subtract b s (bv_unsigned c) (bv_unsigned c + bv_unsigned cs)).
Proof.
  intros b s c cs lo hi H0 Hlh Hhi Hmiss.
  pose proof (mremap_word_range b) as Rb. pose proof (mremap_word_range s) as Rs.
  pose proof (mremap_word_range c) as Rc. pose proof (mremap_word_range cs) as Rcs.
  destruct (Z.eq_dec (bv_unsigned s) 0) as [Hz|Hnz].
  { assert (Hn : nzf [(b, s)] = []) by (rewrite nzf_cons, (proj2 (Z.eqb_eq _ _) Hz); reflexivity).
    rewrite nzf_maps_subtract_all, Hn, maps_subtract_all_nil.
    rewrite iv_subtract_nzf_zero by lia. reflexivity. }
  unfold iv_subtract at 1. cbv zeta. rewrite msa_cuts_app.
  destruct Hmiss as [HL | HR].
  - (* the entry is left of [D] *)
    assert (HX : maps_subtract_all [(b, s)]
                   (if (bv_unsigned c <? lo)%Z
                    then [(c, Z_to_bv 64 (Z.min (bv_unsigned cs) (lo - bv_unsigned c)))] else [])
                 = iv_subtract b s (bv_unsigned c) (bv_unsigned c + bv_unsigned cs)).
    { destruct (bv_unsigned c <? lo)%Z eqn:E1.
      - apply Z.ltb_lt in E1. cbn [maps_subtract_all maps_subtract]. rewrite app_nil_r.
        rewrite mremap_u64 by lia.
        destruct (Z.le_gt_cases (bv_unsigned cs) (lo - bv_unsigned c)) as [Hm|Hm].
        + rewrite Z.min_l by exact Hm. reflexivity.
        + rewrite Z.min_r by lia. unfold iv_subtract. cbv zeta.
          replace (bv_unsigned c + (lo - bv_unsigned c))%Z with lo by lia.
          rewrite (proj2 (Z.ltb_ge lo (bv_unsigned b + bv_unsigned s)) ltac:(lia)).
          rewrite (proj2 (Z.ltb_ge (bv_unsigned c + bv_unsigned cs) (bv_unsigned b + bv_unsigned s)) ltac:(lia)).
          reflexivity.
      - apply Z.ltb_ge in E1. cbn [maps_subtract_all].
        rewrite (iv_subtract_disjoint b s (bv_unsigned c) (bv_unsigned c + bv_unsigned cs)) by lia.
        reflexivity. }
    rewrite HX.
    destruct (hi <? bv_unsigned c + bv_unsigned cs)%Z eqn:E2; cbn [maps_subtract_all]; [| reflexivity].
    apply Z.ltb_lt in E2.
    rewrite !mremap_u64 by lia.
    apply nzf_ms_disjoint; [lia|].
    intros b' s' Hin. left.
    destruct (iv_subtract_within b s _ _ b' s' ltac:(lia) Hin) as [W1 W2]. lia.
  - (* the entry is right of [D] *)
    assert (HX : maps_subtract_all [(b, s)]
                   (if (bv_unsigned c <? lo)%Z
                    then [(c, Z_to_bv 64 (Z.min (bv_unsigned cs) (lo - bv_unsigned c)))] else [])
                 = [(b, s)]).
    { destruct (bv_unsigned c <? lo)%Z eqn:E1; cbn [maps_subtract_all]; [| reflexivity].
      apply Z.ltb_lt in E1. cbn [maps_subtract]. rewrite app_nil_r.
      rewrite mremap_u64 by lia.
      apply iv_subtract_disjoint; lia. }
    rewrite HX.
    destruct (hi <? bv_unsigned c + bv_unsigned cs)%Z eqn:E2; cbn [maps_subtract_all].
    + apply Z.ltb_lt in E2. cbn [maps_subtract]. rewrite app_nil_r.
      rewrite !mremap_u64 by lia.
      replace (Z.max (bv_unsigned c) hi + (bv_unsigned c + bv_unsigned cs - Z.max (bv_unsigned c) hi))%Z
        with (bv_unsigned c + bv_unsigned cs)%Z by lia.
      destruct (Z.le_gt_cases hi (bv_unsigned c)) as [Hc|Hc].
      * rewrite Z.max_l by exact Hc. reflexivity.
      * rewrite Z.max_r by lia. unfold iv_subtract. cbv zeta.
        rewrite (proj2 (Z.ltb_ge (bv_unsigned b) hi) ltac:(lia)).
        rewrite (proj2 (Z.ltb_ge (bv_unsigned b) (bv_unsigned c)) ltac:(lia)).
        reflexivity.
    + apply Z.ltb_ge in E2.
      rewrite (iv_subtract_disjoint b s (bv_unsigned c) (bv_unsigned c + bv_unsigned cs)) by lia.
      reflexivity.
Qed.

Lemma pc_cut : forall l (c cs : word) lo hi,
  (0 <= lo)%Z -> (lo <= hi)%Z -> (hi < two_pow_64)%Z ->
  (forall b s, In (b, s) l -> (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b)%Z) ->
  nzf (maps_subtract_all l (iv_subtract c cs lo hi))
  = nzf (maps_subtract l (bv_unsigned c) (bv_unsigned c + bv_unsigned cs)).
Proof.
  induction l as [|[b s] l IH]; intros c cs lo hi H0 Hlh Hhi Hm.
  - rewrite maps_subtract_all_nil. reflexivity.
  - change ((b, s) :: l) with ([(b, s)] ++ l).
    rewrite maps_subtract_all_app, maps_subtract_app, !nzf_app.
    rewrite (IH c cs lo hi H0 Hlh Hhi) by (intros b' s' H; apply Hm; right; exact H).
    f_equal. cbn [maps_subtract]. rewrite app_nil_r.
    apply pe_cut; [exact H0| exact Hlh| exact Hhi| apply Hm; left; reflexivity].
Qed.

Lemma cut_restrict : forall C l lo hi,
  (0 <= lo)%Z -> (lo <= hi)%Z -> (hi < two_pow_64)%Z ->
  (forall b s, In (b, s) l -> (bv_unsigned b + bv_unsigned s <= two_pow_64)%Z) ->
  (forall b s, In (b, s) l -> (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b)%Z) ->
  nzf (maps_subtract_all l (maps_subtract C lo hi)) = nzf (maps_subtract_all l C).
Proof.
  induction C as [|[c cs] C IH]; intros l lo hi H0 Hlh Hhi Hf Hm; [reflexivity|].
  cbn [maps_subtract maps_subtract_all]. rewrite msa_cuts_app.
  rewrite nzf_maps_subtract_all.
  rewrite (pc_cut l c cs lo hi H0 Hlh Hhi Hm).
  rewrite <- nzf_maps_subtract_all.
  apply IH; [exact H0| exact Hlh| exact Hhi| |].
  - apply maps_subtract_fits. exact Hf.
  - intros b' s' Hin.
    destruct (maps_subtract_In _ _ _ _ _ Hin) as [a [sz [Hin0 Hiv]]].
    destruct (iv_subtract_within a sz _ _ b' s' (Hf a sz Hin0) Hiv) as [W1 W2].
    destruct (Hm a sz Hin0); lia.
Qed.

Lemma charge_dst_le : forall m old old_n dst new_n,
  (bv_unsigned dst mod page_size = 0)%Z ->
  (bv_unsigned new_n mod page_size = 0)%Z ->
  (0 < bv_unsigned new_n)%Z ->
  (bv_unsigned dst + bv_unsigned new_n < two_pow_64)%Z ->
  (forall (a sz : word),
     In (a, sz) (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned old)
                   (bv_unsigned old + bv_unsigned old_n)) ->
     (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z) ->
  region_free (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned old)
                 (bv_unsigned old + bv_unsigned old_n)) dst new_n = true ->
  (vm_backing_used (mremap_model_next m old old_n dst new_n) <= mremap_move_charge m old old_n new_n)%Z.
Proof.
  intros m old old_n dst new_n Halign Hnalign Hpos Hend Hfit Hmaps.
  assert (P1 : forall L P m', m_vmmaps (with_vm_backing L P m') = m_vmmaps m') by reflexivity.
  assert (P2 : forall L P m', m_vm_lazy (with_vm_backing L P m') = L) by reflexivity.
  assert (P3 : forall L P m', m_vm_materialized (with_vm_backing L P m') = P) by reflexivity.
  assert (P4 : forall h m', m_vmmaps (with_vmmaps h m') = h) by reflexivity.
  assert (P5 : forall h m', m_vm_lazy (with_vmmaps h m') = m_vm_lazy m') by reflexivity.
  assert (P6 : forall h m', m_vm_materialized (with_vmmaps h m') = m_vm_materialized m') by reflexivity.
  unfold vm_backing_used, mremap_move_charge, mremap_model_next, vm_resize_backing, mremap_maps_next.
  cbv zeta.
  rewrite !P1, !P2, !P3, !P4, !P5, !P6.
  unfold vm_backed_maps. cbn [vm_maps vm_noaccess vm_limit].
  set (KL := maps_subtract (m_vm_lazy m) (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n)) in *.
  set (KP := List.filter (page_outside_range (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n))
               (m_vm_materialized m)) in *.
  set (R0 := maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n)) in *.
  set (NA := vm_noaccess (m_vmmaps m)) in *.
  pose proof (mremap_word_range dst) as Rd.
  (* what is left of the source mapping misses the destination *)
  assert (HR : forall (b s : word), In (b, s) (maps_subtract_all R0 NA) ->
            (bv_unsigned b + bv_unsigned s <= bv_unsigned dst
             \/ bv_unsigned dst + bv_unsigned new_n <= bv_unsigned b)%Z).
  { intros b s Hin.
    destruct (maps_subtract_all_within NA R0 b s Hfit Hin) as [a [sz [Hin0 Hw]]].
    pose proof (region_free_In R0 dst new_n a sz Hmaps Hin0) as Hov.
    unfold iv_overlap in Hov. apply andb_false_iff in Hov.
    destruct Hov as [Hov | Hov]; apply Z.ltb_ge in Hov; lia. }
  assert (HRfit : forall (b s : word), In (b, s) (maps_subtract_all R0 NA) ->
            (bv_unsigned b + bv_unsigned s <= two_pow_64)%Z).
  { intros b s Hin. destruct (maps_subtract_all_within NA R0 b s Hfit Hin) as [a [sz [Hin0 Hw]]].
    pose proof (Hfit a sz Hin0). lia. }
  (* the lazy ledger with the destination cut out of it cuts that the same *)
  assert (HKR : live_bytes (maps_subtract_all (maps_subtract_all R0 NA)
                              (maps_subtract KL (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n)))
                = live_bytes (maps_subtract_all (maps_subtract_all R0 NA) KL)).
  { rewrite <- (live_nzf (maps_subtract_all (maps_subtract_all R0 NA)
                            (maps_subtract KL (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n)))).
    rewrite <- (live_nzf (maps_subtract_all (maps_subtract_all R0 NA) KL)).
    f_equal. apply cut_restrict; [lia| lia| exact Hend| exact HRfit| exact HR]. }
  (* the re-created mapping, less [vm_noaccess], lies inside the destination *)
  assert (HDin : forall (b s : word), In (b, s) (maps_subtract_all [(dst, new_n)] NA) ->
            (bv_unsigned dst <= bv_unsigned b
             /\ bv_unsigned b + bv_unsigned s <= bv_unsigned dst + bv_unsigned new_n)%Z).
  { intros b s Hin.
    assert (Hf1 : forall (a sz : word), In (a, sz) [(dst, new_n)] ->
              (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z)
      by (intros a sz [E|[]]; injection E as <- <-; lia).
    destruct (maps_subtract_all_within NA [(dst, new_n)] b s Hf1 Hin) as [a [sz [[E|[]] Hw]]].
    injection E as <- <-. lia. }
  assert (HDle : (live_bytes (maps_subtract_all [(dst, new_n)] NA) <= bv_unsigned new_n)%Z).
  { pose proof (live_bytes_maps_subtract_all_le NA [(dst, new_n)]) as H. cbn [live_bytes] in H. lia. }
  change ((dst, new_n) :: R0) with ([(dst, new_n)] ++ R0).
  rewrite maps_subtract_all_app, maps_subtract_all_app, live_bytes_app.
  rewrite length_app.
  pose proof (filter_len_le (page_outside_range (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n)) KP) as HFL.
  destruct (mremap_source_lazy_b m old old_n) eqn:Hsrc.
  - (* lazy source: the re-created mapping is its own lazy interior *)
    rewrite (lazy_interior_aligned dst new_n Halign Hnalign Hpos).
    rewrite length_map.
    change ([(dst, new_n)] ++ maps_subtract KL (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n))
      with ((dst, new_n) :: maps_subtract KL (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n)).
    cbn [maps_subtract_all].
    rewrite (ms_inside_nil (maps_subtract_all [(dst, new_n)] NA) _ _ HDin), maps_subtract_all_nil.
    rewrite (live_bytes_subtract_free (maps_subtract KL (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n))
               (maps_subtract_all R0 NA) (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n) ltac:(lia) HR).
    rewrite HKR. cbn [live_bytes]. unfold page_size in *. lia.
  - (* eager source: the re-created mapping is charged whole *)
    pose proof (live_bytes_maps_subtract_all_le
                  (maps_subtract KL (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n))
                  (maps_subtract_all [(dst, new_n)] NA)) as HD2.
    rewrite HKR. cbn [length app]. unfold page_size in *. lia.
Qed.
