(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec StoreOk AgentLib AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanMainEntryKit () : Init.string Init.list := ["Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.lt"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "stdpp.bitvector.definitions.bv_add"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.option"; "stdpp.bitvector.definitions.bv"; "OSSVerify.KrLib.ABoot.PropExec.seg_rom"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "xfer_ok"; "OSSVerify.KrLib.ABoot.PropExec.rdn"; "OSSVerify.KrLib.ABoot.AsanAcct.mrestrict"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.kentry"; "cell"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.know_ok"; "Stdlib.Lists.List.In"; "kxfer_okb"; "Corelib.Init.Datatypes.true"; "kden"; "cell_ok"; "Stdlib.Lists.List.forallb"; "Corelib.Lists.ListDef.Forall"; "omap"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.atable"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.env"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.acs"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.img_hi"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.in_hull"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.hid"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.amap"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.no_fog"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.is_fog"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.uE"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.am_len"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.maps_match"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.snd"; "Corelib.Lists.ListDef.map"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.amap_den"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.seps"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.iv_disjoint"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.mkind"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.nlz_ok"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.zB"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.zE"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.am_kind"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.expr"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.cov_ok"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.K_NLZ"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.am_base"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.in_ivs"].


Inductive cell : Type :=
| CWord (a : word) (w : nat) (v : word)
| CZero (a : word) (n : word)
| CFill (a : word) (n : word) (c : Z)
| CUnk (a : word) (n : word)
| CWr (a : word) (n : word)
| CImg (lo hi : Z).

Definition cell_ok (segs : list Segment) (M : word -> option byte) (c : cell) : Prop :=
  match c with
  | CWord a w v => rdn segs M a w = Some (word_to_le_bytes w v)
  | CZero a n => bv_unsigned a + bv_unsigned n <= 2 ^ 64
               /\ forall i, 0 <= i < bv_unsigned n -> M (Z_to_bv 64 (bv_unsigned a + i)) = Some (Z_to_bv 8 0)
  | CFill a n c => bv_unsigned a + bv_unsigned n <= 2 ^ 64
               /\ forall i, 0 <= i < bv_unsigned n -> M (Z_to_bv 64 (bv_unsigned a + i)) = Some (Z_to_bv 8 c)
  | CUnk a n => bv_unsigned a + bv_unsigned n <= 2 ^ 64
               /\ forall i, 0 <= i < bv_unsigned n -> M (Z_to_bv 64 (bv_unsigned a + i)) <> None
  | CWr a n => bv_unsigned a + bv_unsigned n <= 2 ^ 64
               /\ forall d m, 0 <= d -> d + Z.of_nat m <= bv_unsigned n -> store_ok segs M (Z_to_bv 64 (bv_unsigned a + d)) m = true
  | CImg lo hi => forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None
  end.

(* [comment removed for export] *)
Definition sden (E : env) (a : saddr) : word :=
  match a with
  | SA (ELit 0) off => Z_to_bv 64 off
  | SA b off => v_addi (edenot E b) off
  end.

Lemma sden_adenot : forall E a, sden E a = adenot E a.
Proof.
  intros E [b off]. unfold sden, adenot, v_addi. destruct b as [z| | | | | | |]; try reflexivity.
  destruct z; reflexivity.
Qed.

(* [comment removed for export] *)
Definition kden (E : env) (K : kentry) : option cell :=
  match K with
  | KWord a w v => Some (CWord (sden E a) w (edenot E v))
  | KZero a n => Some (CZero (sden E a) (edenot E n))
  | KFill a n c => Some (CFill (sden E a) (edenot E n) c)
  | KUnk a n => Some (CUnk (sden E a) (edenot E n))
  | KWr a n => Some (CWr (sden E a) (edenot E n))
  | KImg lo hi => Some (CImg lo hi)
  | KBlob _ _ _ => None
  | KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ => None
  end.

Fixpoint omap {A B} (f : A -> option B) (l : list A) : list B :=
  match l with [] => [] | x :: r => match f x with Some y => y :: omap f r | None => omap f r end end.

(* [comment removed for export] *)
Definition xfer_ok (segs : list Segment) (H : word -> bool) (a : word) (n : nat) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryKit ()) "Pk,$0.P,(1.R1.O1.)(2.(3.$4.A1.O3.(5.&40.O2.(6.&40.(7.R2.)))$8.)(3.(9.(:.&8.))(;.O4.(5.&40.O2.(6.&40.(7.R2.))))(<.(:.&8.))))")
(* [comment removed for export] *).

Lemma woffk_S : forall (a : word) k, (a + 1 + Z_to_bv 64 (Z.of_nat k))%bv = (a + Z_to_bv 64 (Z.of_nat (S k)))%bv.
Proof.
  intros a k. apply bv_eq. rewrite !bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Nat2Z.inj_succ.
  change (bv_unsigned (1 : word)) with 1.
  rewrite Z.add_mod_idemp_l, !Z.add_mod_idemp_r by lia. f_equal. lia.
Qed.

Lemma xfer_ok_S : forall segs H a n, xfer_ok segs H a (S n) -> xfer_ok segs H (a + 1)%bv n.
Proof. intros segs H a n Hx k Hk. rewrite woffk_S. apply Hx. lia. Qed.

Lemma woff0 : forall a : word, (a + Z_to_bv 64 (Z.of_nat 0))%bv = a.
Proof.
  intros a. apply bv_eq. rewrite bv_add_unsigned, bv_wrap64_mod. change (bv_unsigned (Z_to_bv 64 (Z.of_nat 0))) with 0.
  rewrite Z.add_0_r. pose proof (u64_range a). apply Z.mod_small. lia.
Qed.

Lemma xfer_ok_0 : forall segs H a n, xfer_ok segs H a (S n) -> H a = false \/ seg_rom segs a = None.
Proof. intros segs H a n Hx. specialize (Hx O ltac:(lia)). rewrite woff0 in Hx. exact Hx. Qed.

Lemma rdn_mrestrict_xfer : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryKit ()) "Psegs,(=.$>.)PH,P,(:.&40.)$4.Pn,$0.PM,P,(:.&40.)(9.(:.&8.))Pa,(:.&40.)Pbs,(=.(:.&8.))P,(?.R6.R5.R2.R4.)P,(3.(9.(=.(:.&8.)))(10.R7.(11.R6.R4.)R3.R5.)(12.(=.(:.&8.))R2.))(3.(9.(=.(:.&8.)))(10.R8.R5.R4.R6.)(12.(=.(:.&8.))R3.))")
(* [comment removed for export] *).
Proof.
  intros segs H n. induction n as [|n IH]; intros M a bs Hx Hr; [exact Hr|].
  pose proof (xfer_ok_0 segs H a n Hx) as X0. pose proof (xfer_ok_S segs H a n Hx) as Hx'.
  cbn [rdn] in *. unfold mrestrict at 1 in Hr. fold (mrestrict H M) in Hr.
  destruct (H a) eqn:Ha.
  - destruct X0 as [X0|X0]; [congruence|]. rewrite X0 in Hr. discriminate.
  - destruct (M a) as [b|] eqn:HMa.
    + destruct (rdn segs (mrestrict H M) (a + 1)%bv n) as [rest|] eqn:Hrest; [|discriminate].
      rewrite (IH M (a + 1)%bv rest Hx' Hrest). exact Hr.
    + destruct (seg_rom segs a) as [b|]; [|discriminate].
      destruct (rdn segs (mrestrict H M) (a + 1)%bv n) as [rest|] eqn:Hrest; [|discriminate].
      rewrite (IH M (a + 1)%bv rest Hx' Hrest). exact Hr.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kxfer_okb (A : atable) (k : list kentry) (K : kentry) : bool :=
  match K with
  | KImg lo hi => ((img_lo A <=? lo) && (hi <=? img_hi A))%bool
  | _ => true
  end.

Lemma mrestrict_some : forall H M a b, mrestrict H M a = Some b -> M a = Some b.
Proof. intros H M a b. unfold mrestrict. destruct (H a); [discriminate | exact (fun x => x)]. Qed.

Lemma mrestrict_grows : forall H M, mem_grows (mrestrict H M) M.
Proof. intros H M x. unfold mrestrict. destruct (H x); [intros X; exfalso; exact (X eq_refl) | exact (fun x => x)]. Qed.

Lemma u_woffk : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryKit ()) "Pa,(:.&40.)Pk,$0.P,(13.(14.(15.&40.R2.)(7.R1.))(16.+2.+40.))(3.$17.(15.&40.(5.&40.R3.(6.&40.(7.R2.))))(14.(15.&40.R3.)(7.R2.)))")
(* [comment removed for export] *).
Proof.
  intros a k Hk. pose proof (u64_range a). rewrite bv_add_unsigned, Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small (Z.of_nat k)) by lia. apply Z.mod_small. lia.
Qed.

Section Bridge.
  Variable segs : list Segment.
  Variable A : atable.
  Variable E : env.
  Variable H : word -> bool.
  Variable M : word -> option byte.
  Hypothesis HULL : 0 <= img_lo A /\ img_hi A <= 2 ^ 64.
  Hypothesis H_hull : forall a, in_hull A (bv_unsigned a) = true -> H a = false.
  Hypothesis rom_hull : forall a, in_hull A (bv_unsigned a) = false -> seg_rom segs a = None.

  #[using="HULL H_hull rom_hull"] Lemma kden_sound : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryKit ()) "Pk,(=.$18.)PK,$18.Pc,$19.P,(1:.Vsegs,VE,(11.VH,VM,)R3.)P,(1;.$18.R3.R4.)P,(3.$4.(1<.VA,R5.R4.)$1=.)P,(3.(9.$19.)(1>.VE,R5.)(12.$19.R4.))(1?.Vsegs,VM,R5.)")
(* [comment removed for export] *).
  Proof.
    intros k K c Hk HIn Hx Hd.
    pose proof (proj1 (Forall_forall _ _) Hk K HIn) as HK.
    destruct K as [a w v | a n | a n kb | lo hi | e m | e lo hi | a n | a1 n1 a2 n2 | a n c8 | a n];
      cbn [kden] in Hd; try discriminate; injection Hd as <-; cbn [kentry_ok] in HK; unfold cell_ok; rewrite ?sden_adenot.
    - (* [comment removed for export] *)
      destruct HK as (Hw & Hfl & Hr).
      eapply rdn_mrestrict_xfer; [|exact Hr]. intros j Hj.
      destruct (in_hull A (bv_unsigned (adenot E a + Z_to_bv 64 (Z.of_nat j))%bv)) eqn:Hin;
        [left; exact (H_hull _ Hin) | right; exact (rom_hull _ Hin)].
    - (* [comment removed for export] *)
      destruct HK as [Hfl Hz]. pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
      unfold elenZ in *. rewrite Hu. split; [lia|]. intros i Hi. apply (mrestrict_some H). apply Hz. lia.
    - (* [comment removed for export] *)
      destruct HK as (L1 & L2 & Hn). cbn [kxfer_okb] in Hx. apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2.
      intros i Hi. specialize (Hn i Hi). unfold mrestrict in Hn.
      rewrite (H_hull (Z_to_bv 64 i)) in Hn; [exact Hn|]. rewrite u64_lit by lia.
      unfold in_hull. apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
    - (* [comment removed for export] *)
      destruct HK as [Hfl Hs]. pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
      unfold elenZ in *. rewrite Hu. split; [lia|]. intros d m Hd' Hm.
      eapply store_ok_mono; [apply mrestrict_grows | apply Hs; lia].
    - (* [comment removed for export] *)
      destruct HK as [Hfl Hz]. pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
      unfold elenZ in *. rewrite Hu. split; [lia|]. intros i Hi. apply (mrestrict_some H). apply Hz. lia.
    - (* [comment removed for export] *)
      destruct HK as [Hfl Hz]. pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
      unfold elenZ in *. rewrite Hu. split; [lia|]. intros i Hi X. apply (Hz i ltac:(lia)). unfold mrestrict. rewrite X. destruct (H _); reflexivity.
  Qed.

  #[using="HULL H_hull rom_hull"] Theorem know_cells_sound : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryKit ()) "Pk,(=.$18.)P,(1:.Vsegs,VE,(11.VH,VM,)R1.)P,(3.$4.(20.$18.(1<.VA,R2.)R2.)$1=.)(21.$19.(1?.Vsegs,VM,)(22.$18.$19.(1>.VE,)R3.))")
(* [comment removed for export] *).
  Proof.
    intros k Hk Hx.
    assert (G : forall l, (forall K, In K l -> In K k) -> Forall (cell_ok segs M) (omap (kden E) l)).
    { induction l as [|K l IH]; intros Hincl; cbn [omap]; [constructor|].
      assert (HIn : In K k) by (apply Hincl; left; reflexivity).
      pose proof (proj1 (forallb_forall _ _) Hx K HIn) as HxK.
      destruct (kden E K) as [c|] eqn:Hd.
      - constructor; [exact (kden_sound k K c Hk HIn HxK Hd) | apply IH; intros K' HK'; apply Hincl; right; exact HK'].
      - apply IH. intros K' HK'; apply Hincl; right; exact HK'. }
    apply G. exact (fun K HK => HK).
  Qed.
End Bridge.

(* [comment removed for export] *)
Fixpoint select {X} (g : nat) (route : list nat) (l : list X) : list X :=
  match route, l with
  | r :: route', c :: l' => if Nat.eqb r g then c :: select g route' l' else select g route' l'
  | _, _ => []
  end.
Lemma Forall_select {X} : forall (P : X -> Prop) g route l, Forall P l -> Forall P (select g route l).
Proof.
  intros P g route. induction route as [|r route IH]; intros l Hl; [destruct l; constructor|].
  destruct l as [|c l']; [constructor|]. inversion Hl; subst. cbn [select].
  destruct (Nat.eqb r g); [constructor; [assumption | apply IH; assumption] | apply IH; assumption].
Qed.

(* [comment removed for export] *)
Inductive cnst : Type :=
| CRange (lo : Z) (v : word) (hi : Z)      (* [comment removed for export] *)
| CDisj (a n b m : Z)                      (* [comment removed for export] *)
| CAlignm (v : word) (m : Z).               (* [comment removed for export] *)
Definition cnst_ok (c : cnst) : Prop :=
  match c with
  | CRange lo v hi => lo <= bv_unsigned v <= hi
  | CDisj a n b m => a + n <= b \/ b + m <= a
  | CAlignm v m => 0 < m /\ bv_unsigned v mod m = 0
  end.
(* [comment removed for export] *)
Definition zden (E : env) (a : saddr) : Z :=
  match a with SA (ELit 0) off => off | SA b off => bv_unsigned (edenot E b) + off end.
Lemma zden_estart : forall E a, zden E a = estart E a.
Proof. intros E [b off]. unfold zden, estart. cbn [a_base a_off]. destruct b as [z| | | | | | |]; try reflexivity. destruct z; reflexivity. Qed.
Definition kcn (E : env) (K : kentry) : option cnst :=
  match K with
  | KRange e lo hi => Some (CRange lo (edenot E e) hi)
  | KDisj a1 n1 a2 n2 => Some (CDisj (zden E a1) (bv_unsigned (edenot E n1)) (zden E a2) (bv_unsigned (edenot E n2)))
  | KAlign e m => Some (CAlignm (edenot E e) m)
  | _ => None
  end.
Lemma know_cnsts_sound : forall segs E M k, know_ok segs E M k -> Forall cnst_ok (omap (kcn E) k).
Proof.
  intros segs E M k Hk. induction k as [|K k IH]; cbn [omap]; [constructor|].
  inversion Hk as [|K' k' HK Hk']; subst.
  destruct K as [a w v | a n | a n kb | lo hi | e m | e lo hi | a n | a1 n1 a2 n2 | a n c8 | a n]; cbn [kcn]; try (apply IH; exact Hk').
  - constructor; [cbn [cnst_ok kentry_ok] in *; exact HK | apply IH; exact Hk'].
  - constructor; [cbn [cnst_ok kentry_ok] in *; exact HK | apply IH; exact Hk'].
  - constructor; [cbn [cnst_ok]; cbn [kentry_ok] in HK; rewrite !zden_estart; unfold elenZ in HK; exact HK | apply IH; exact Hk'].
Qed.

(* [comment removed for export] *)
Lemma hid_off_hull : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryKit ()) "PA,$23.PSP0,$17.PargH,Px,$24.Px0,(:.&40.)$4.PE,$24.Pcs,$25.Pmodel,$26.Pa,(:.&40.)P,PE,$24.Pa,(:.&40.)P,(3.$4.A2.R7.R2.R1.$1=.)(27.R9.(15.&40.R2.))P,(27.(28.R8.)R7.)P,(3.$4.(29.R9.(15.&40.R3.))$1=.)(3.$4.(2:.R:.R9.R8.R7.R6.R5.R4.)$8.)")
(* [comment removed for export] *).
Proof.
  intros A SP0 argH E cs model a AH Hhi Hin. unfold hid, vis. rewrite Hin. cbn [orb].
  destruct (argH E a) eqn:Ha; [|reflexivity]. exfalso. pose proof (AH E a Ha).
  unfold in_hull in Hin. apply andb_prop in Hin as [_ X]. apply Z.ltb_lt in X. lia.
Qed.

(* [comment removed for export] *)
Lemma maps_match_nofog : forall E ms l, no_fog ms = true -> maps_match E ms l -> l = map (amap_den E) ms.
Proof.
  intros E ms. induction ms as [|m ms IH]; intros l Hnf Hm; cbn [maps_match] in Hm; [exact Hm|].
  cbn [no_fog forallb] in Hnf. apply andb_prop in Hnf as [H1 H2]. destruct (is_fog m); [discriminate|].
  destruct Hm as (l' & -> & Hm'). cbn [map]. f_equal. exact (IH l' H2 Hm').
Qed.

Lemma maps_match_2fog : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryKit ()) "PE,$24.Pnew,(=.$2;.)Pf1,$2;.Pf2,$2;.Pold,(=.$2;.)Pl,(=.(2<.(:.&40.)(:.&40.)))PB,$17.P,(3.$4.(2=.R6.)$1=.)P,(3.$4.(2>.R6.)$1=.)P,(3.$4.(2>.R6.)$1=.)P,(3.$4.(2=.R6.)$1=.)P,(27.(2?.R;.(30.R9.))R5.)P,(27.(2?.R<.(30.R9.))R6.)P,(31.R=.(32.$2;.R<.(33.$2;.R;.(33.$2;.R:.R9.)))R8.)(34.(=.(2<.(:.&40.)(:.&40.)))Lfog,(=.(2<.(:.&40.)(:.&40.)))(35.(36.(37.(2<.(:.&40.)(:.&40.))R1.)#2.)(35.(21.(2<.(:.&40.)(:.&40.))Liv,(2<.(:.&40.)(:.&40.))(27.(15.&40.(38.(:.&40.)(:.&40.)R1.))R:.)R1.)(3.(=.(2<.(:.&40.)(:.&40.)))R:.(32.(2<.(:.&40.)(:.&40.))(39.$2;.(2<.(:.&40.)(:.&40.))(3:.R?.)R>.)(32.(2<.(:.&40.)(:.&40.))R1.(39.$2;.(2<.(:.&40.)(:.&40.))(3:.R?.)R;.)))))))")
(* [comment removed for export] *).
Proof.
  intros E new. induction new as [|m new IH]; intros f1 f2 old l B Hn H1 H2 Ho B1 B2 Hm.
  - cbn [app map] in *. cbn [maps_match] in Hm. rewrite H1 in Hm. fold (maps_match E (f2 :: old)) in Hm.
    assert (STEP2 : forall l2, maps_match E (f2 :: old) l2 ->
              exists fog, (length fog <= 1)%nat /\ Forall (fun iv => bv_unsigned (snd iv) <= B) fog /\ l2 = fog ++ map (amap_den E) old).
    { intros l2 Hm2. cbn [maps_match] in Hm2. rewrite H2 in Hm2. fold (maps_match E old) in Hm2.
      destruct Hm2 as [Hm2 | (iv & l' & -> & Hsz & Hm2)].
      - exists []. split; [cbn; lia|]. split; [constructor|]. cbn [app]. exact (maps_match_nofog E old l2 Ho Hm2).
      - exists [iv]. split; [cbn; lia|]. split; [constructor; [lia|constructor]|]. cbn [app]. f_equal. exact (maps_match_nofog E old l' Ho Hm2). }
    destruct Hm as [Hm | (iv & l' & -> & Hsz & Hm)].
    + destruct (STEP2 l Hm) as (fog & L & F & ->). exists fog. split; [lia|]. split; [exact F | reflexivity].
    + destruct (STEP2 l' Hm) as (fog & L & F & ->). exists (iv :: fog). split; [cbn; lia|]. split; [constructor; [lia | exact F] | reflexivity].
  - cbn [no_fog forallb] in Hn. apply andb_prop in Hn as [Hn1 Hn2].
    cbn [app maps_match] in Hm. destruct (is_fog m); [discriminate|].
    destruct Hm as (l' & -> & Hm).
    destruct (IH f1 f2 old l' B Hn2 H1 H2 Ho B1 B2 Hm) as (fog & L & F & ->).
    exists fog. split; [exact L|]. split; [exact F|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma seps_cons_inv' : forall p l, seps (p :: l) -> Forall (iv_disjoint p) l /\ seps l.
Proof. intros p l H. inversion H; subst; auto. Qed.
Lemma seps_In_disjoint' : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryKit ()) "Pl,(=.(2<.(:.&40.)(:.&40.)))Pp,(2<.(:.&40.)(:.&40.))Pq,(2<.(:.&40.)(:.&40.))P,(3;.R3.)P,Piv,(2<.(:.&40.)(:.&40.))P,(1;.(2<.(:.&40.)(:.&40.))R1.R5.)(13.=(15.&40.(38.(:.&40.)(:.&40.)R2.)))P,(1;.(2<.(:.&40.)(:.&40.))R4.R5.)P,(1;.(2<.(:.&40.)(:.&40.))R4.R6.)P,(3<.(3.(2<.(:.&40.)(:.&40.))R6.R5.))(3=.R7.R6.)")
(* [comment removed for export] *).
Proof.
  induction l as [|h t IH]; intros p q Hs Hpos Hp Hq Hne; [destruct Hp|].
  apply seps_cons_inv' in Hs as [Hf Ht].
  destruct Hp as [<-|Hp]; destruct Hq as [<-|Hq].
  - exfalso. exact (Hne eq_refl).
  - exact (proj1 (Forall_forall _ _) Hf q Hq).
  - pose proof (proj1 (Forall_forall _ _) Hf p Hp) as D. unfold iv_disjoint in *. lia.
  - apply IH; auto. intros iv Hiv. apply Hpos. right. exact Hiv.
Qed.

(* [comment removed for export] *)
Lemma nlz_cov : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryKit ()) "PE,$24.Pms,(=.$2;.)Pks,(=.$3>.)PM,(=.(2<.(:.&40.)(:.&40.)))PX,(=.(2<.(:.&40.)(:.&40.)))P,(3?.R5.R4.R3.R2.R1.)Pe,(2<.(:.&40.)(:.&40.))P,(1;.(2<.(:.&40.)(:.&40.))R1.R3.)(35.(13.=(15.&40.(38.(:.&40.)(:.&40.)R2.)))(34.(2<.(:.&40.)(:.&40.))Liv,(2<.(:.&40.)(:.&40.))(35.(1;.(2<.(:.&40.)(:.&40.))R1.R6.)(35.(27.(40.R1.)(40.R3.))(27.(41.R3.)(41.R1.))))))")
(* [comment removed for export] *).
Proof. intros E ms ks M X H e He. destruct (H e He) as (P & iv & Hiv & B1 & B2 & _). split; [exact P|]. exists iv. auto. Qed.

(* [comment removed for export] *)
Lemma ledger_clear : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryKit ()) "PE,$24.Pms,(=.$2;.)Pks,(=.$3>.)PM,(=.(2<.(:.&40.)(:.&40.)))PX,(=.(2<.(:.&40.)(:.&40.)))Pm,$2;.P,(31.R6.R5.R3.)P,(3;.R4.)P,Piv,(2<.(:.&40.)(:.&40.))P,(1;.(2<.(:.&40.)(:.&40.))R1.R6.)(13.=(15.&40.(38.(:.&40.)(:.&40.)R2.)))P,(3?.R9.R8.R7.R6.R5.)P,(1;.$2;.R5.R9.)P,(3.$4.(2>.R6.)$8.)P,(1;.$3>.(42.R7.)R:.)Pe,(2<.(:.&40.)(:.&40.))P,(1;.(2<.(:.&40.)(:.&40.))R1.R:.)(2.(27.(41.R2.)(40.(3:.R?.R:.)))(27.(41.(3:.R?.R:.))(40.R2.)))")
(* [comment removed for export] *).
Proof.
  intros E ms ks M X m HM HS HP H Hin Hf Hk e He.
  destruct (H e He) as (P & iv & Hiv & B1 & B2 & NB).
  pose proof (maps_match_In E ms M m HM Hin Hf) as Hden.
  assert (Hne : iv <> amap_den E m) by (intros ->; apply NB; exists m; auto).
  pose proof (seps_In_disjoint' M iv (amap_den E m) HS HP Hiv Hden Hne) as D. unfold iv_disjoint, zB, zE in *. lia.
Qed.

(* [comment removed for export] *)
Lemma bounds_pos : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryKit ()) "PP,P,(2<.(:.&40.)(:.&40.))SpPM,(=.(2<.(:.&40.)(:.&40.)))P,(21.(2<.(:.&40.)(:.&40.))Liv,(2<.(:.&40.)(:.&40.))(35.(13.=(15.&40.(38.(:.&40.)(:.&40.)R1.)))A1.R3.R1.)R1.)Piv,(2<.(:.&40.)(:.&40.))P,(1;.(2<.(:.&40.)(:.&40.))R1.R3.)(13.=(15.&40.(38.(:.&40.)(:.&40.)R2.)))")
(* [comment removed for export] *).
Proof. intros P M H iv Hiv. exact (proj1 (proj1 (Forall_forall _ _) H iv Hiv)). Qed.

(* [comment removed for export] *)
Lemma cov_tok1 : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryKit ()) "PE,$24.PN,(=.(2<.(:.&40.)(:.&40.)))Ptb,$43.Ptl,$43.Pms,(=.$2;.)Pm,$2;.P,(21.$2;.(44.R6.R5.(33.(2<.$43.$43.)(45.$43.$43.R4.R3.)(46.(2<.$43.$43.))))R2.)P,(1;.$2;.R2.R3.)P,(1;.$3>.(42.R3.)$47.)Pz,$17.P,(35.(27.(2?.R:.(48.R5.))R1.)(13.R1.(14.(2?.R:.(48.R5.))(2?.R:.(30.R5.)))))(2.(3.$4.(49.R2.R:.)$1=.)(35.(27.(2?.R;.R9.)R2.)(13.R2.(14.(2?.R;.R9.)(2?.R;.R8.)))))")
(* [comment removed for export] *).
Proof.
  intros E N tb tl ms m HF Hm Hk z Hz.
  destruct (proj1 (Forall_forall _ _) HF m Hm Hk z Hz) as [H|(t & Ht & Hzt)]; [left; exact H | right].
  destruct Ht as [<-|[]]. unfold in_tok in Hzt. cbn [fst snd] in Hzt. exact Hzt.
Qed.
