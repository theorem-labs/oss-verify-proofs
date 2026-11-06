(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Arr SysStep CellsX TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim STree Malloc MallocCtrl Monad Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

Record srep := mkS { sb : list byte ;            (* [comment removed for export] *)
                     sown : option block }.      (* [comment removed for export] *)

Definition slen (S : srep) : Z := zlength (sb S).
Definition scap (S : srep) : Z := match sown S with None => 22 | Some (_, _, alloc) => alloc - 1 end.
Definition sdata (a : Z) (S : srep) : Z := match sown S with None => a + 1 | Some (_, A, _) => A end.   (* [comment removed for export] *)
Definition blocks_S (S : srep) : list block := match sown S with None => [] | Some b => [b] end.
Definition StrEmpty : srep := mkS [] None.
Definition is_long (S : srep) : bool := match sown S with None => false | Some _ => true end.

(* [comment removed for export] *)
Definition str_alloc (n : Z) : Z := if Z.lor n 7 =? 23 then 26 else Z.lor n 7 + 1.

(* [comment removed for export] *)
Definition short_cells (bs junk : list byte) : list cell :=
  [C1 (b8 (2 * zlength bs)); CB (length bs) bs; C1 (b8 0); CB (22 - length bs)%nat junk].
(* [comment removed for export] *)
Definition long_hdr (alloc size A : Z) : list cell := [C8 (wz (alloc + 1)); C8 (wz size); C8 (wz A)].
Definition long_buf (bs junk : list byte) (alloc : Z) : list cell :=
  [CB (length bs) bs; C1 (b8 0); CB (Z.to_nat alloc - length bs - 1)%nat junk].

Definition StrObj (LB : list block) (m : mem) (a : Z) (S : srep) : Prop :=
  match sown S with
  | None =>
      slen S <= 22 /\ exists junk, rw_cells rsegs m a (short_cells (sb S) junk)
  | Some (p, A, alloc) =>
      slen S <= alloc - 1 /\ In (p, A, alloc) LB /\ rblock_range A alloc /\ alloc mod 2 = 0 /\ 24 <= alloc /\ alloc < 2^63 /\
      (a + 24 <= A \/ A + alloc <= a) /\
      rw_cells rsegs m a (long_hdr alloc (slen S) A) /\
      exists junk, rw_cells rsegs m A (long_buf (sb S) junk alloc)
  end.

Lemma StrObj_len_cap : forall LB m a S, StrObj LB m a S -> 0 <= slen S <= scap S.
Proof.
  intros LB m a [bs [[[p A] alloc]|]] H; cbn in *; unfold slen, zlength in *; cbn in *; [|lia].
  destruct H as (H & _). lia.
Qed.

Lemma StrObj_short_intro : forall LB m a bs junk,
  zlength bs <= 22 -> rw_cells rsegs m a (short_cells bs junk) -> StrObj LB m a (mkS bs None).
Proof. intros LB m a bs junk Hl H. cbn. split; [exact Hl| exists junk; exact H]. Qed.

Lemma StrObj_long_intro : forall LB m a bs junk p A alloc,
  zlength bs <= alloc - 1 -> In (p, A, alloc) LB -> rblock_range A alloc -> alloc mod 2 = 0 -> 24 <= alloc -> alloc < 2^63 ->
  (a + 24 <= A \/ A + alloc <= a) ->
  rw_cells rsegs m a (long_hdr alloc (zlength bs) A) ->
  rw_cells rsegs m A (long_buf bs junk alloc) ->
  StrObj LB m a (mkS bs (Some (p, A, alloc))).
Proof. intros. cbn. unfold slen; cbn. repeat (split; [assumption|]). exists junk; assumption. Qed.

Lemma StrObj_short_elim : forall LB m a bs,
  StrObj LB m a (mkS bs None) -> zlength bs <= 22 /\ exists junk, rw_cells rsegs m a (short_cells bs junk).
Proof. intros LB m a bs H. exact H. Qed.

Lemma StrObj_long_elim : forall LB m a bs p A alloc,
  StrObj LB m a (mkS bs (Some (p, A, alloc))) ->
  zlength bs <= alloc - 1 /\ In (p, A, alloc) LB /\ rblock_range A alloc /\ alloc mod 2 = 0 /\ 24 <= alloc /\ alloc < 2^63 /\
  (a + 24 <= A \/ A + alloc <= a) /\
  rw_cells rsegs m a (long_hdr alloc (zlength bs) A) /\ exists junk, rw_cells rsegs m A (long_buf bs junk alloc).
Proof. intros LB m a bs p A alloc H. exact H. Qed.

(* [comment removed for export] *)
Lemma StrObj_zero24 : forall LB m a, rw_cells rsegs m a [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> StrObj LB m a StrEmpty.
Proof.
  intros LB m a H. apply (StrObj_short_intro LB m a [] (repeat (b8 0) 22)). { unfold zlength; cbn; lia. }
  destruct H as [[WF B] W]. split; [split|].
  - cbn. repeat split; reflexivity.
  - replace (cells_bytes (short_cells [] (repeat (b8 0) 22))) with (cells_bytes [C8 (wz 0); C8 (wz 0); C8 (wz 0)]); [exact B|].
    vm_compute. reflexivity.
  - exact W.
Qed.

(* [comment removed for export] *)
Lemma StrObj_sdata_range : forall LB m a S, StrObj LB m a S ->
  0 < sdata a S /\ sdata a S + slen S + 1 <= 2^64.
Proof.
  intros LB m a [bs [[[p A] alloc]|]] H; cbn in *.
  - destruct H as (Hl & _ & (R1 & _ & R3 & R4 & _) & _ & _ & _ & _ & _ & _). hcb. unfold slen in *; cbn in *. lia.
  - destruct H as (Hl & junk & H). pose proof (rw_cells_bound _ _ _ _ H) as B.
    unfold short_cells in B. cbn [cells_size csize] in B. unfold slen in *; cbn in *. unfold zlength in *. lia.
Qed.

Lemma StrObj_LB_mono : forall LB LB' m a S, StrObj LB m a S -> (forall b, In b LB -> In b LB') -> StrObj LB' m a S.
Proof.
  intros LB LB' m a [bs [[[p A] alloc]|]] H HL; cbn in *; [|exact H].
  destruct H as (H1 & H2 & H3). split; [exact H1|]. split; [apply HL; exact H2| exact H3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint rin_ivs (X : list (Z * Z)) (a : Z) : Prop :=
  match X with [] => False | iv :: X' => (fst iv <= a < snd iv) \/ rin_ivs X' a end.

Definition xclient (LB : list block) (SP : Z) (X : list (Z * Z)) (a : Z) : Prop :=
  rclient_addr LB SP a /\ ~ rin_ivs X a.

Definition xpres (LB : list block) (SP : Z) (X : list (Z * Z)) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> xclient LB SP X a ->
    m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None).

Lemma xpres_refl : forall LB SP X m, xpres LB SP X m m.
Proof. intros LB SP X m a _ _. auto. Qed.

Lemma xpres_trans : forall LB SP X m1 m2 m3, xpres LB SP X m1 m2 -> xpres LB SP X m2 m3 -> xpres LB SP X m1 m3.
Proof.
  intros LB SP X m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma xpres_weaken : forall LB LB' SP SP' X X' m m',
  xpres LB SP X m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> (forall a, rin_ivs X a -> rin_ivs X' a) ->
  xpres LB' SP' X' m m'.
Proof.
  intros LB LB' SP SP' X X' m m' H HS HL HX a Ha [Hc Hx]. apply H; [exact Ha|]. split; [| intros K; apply Hx, HX, K].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

Lemma xpres_of_heap_pres : forall LB SP X m m', rheap_pres LB SP m m' -> xpres LB SP X m m'.
Proof. intros LB SP X m m' H a Ha [Hc _]. apply H; assumption. Qed.

Lemma rin_ivs_app : forall X1 X2 a, rin_ivs (X1 ++ X2) a <-> rin_ivs X1 a \/ rin_ivs X2 a.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.iff); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.CXXRep.HCW.rin_ivs); constr:(@Corelib.Init.Datatypes.app); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.or_intror); constr:(@Corelib.Init.Logic.or_ind); constr:(@Corelib.Init.Logic.False_ind); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.iff_Transitive); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Init.Datatypes.fst); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Classes.Morphisms.Reflexive_partial_app_morphism); constr:(@Corelib.Classes.Morphisms.respectful); constr:(@Corelib.Classes.Morphisms_Prop.or_iff_morphism); constr:(@Corelib.Classes.Morphisms.reflexive_proper_proxy); constr:(@Corelib.Classes.Morphisms.reflexive_reflexive_proxy); constr:(@Corelib.Classes.RelationClasses.iff_Reflexive); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@Corelib.Init.Datatypes.prod_ind); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Logic.and_ind); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Datatypes.cons)|] [|@a; @X2; @X1; @H; @H0; @B; @lemma; @iv; @H1; @b; @a0; @IH|] "#%'#.#P#3###$#%#'#&#(#.#5#)#*#:#8#O#+#2#1#=#>#G#J#K#I#F#H#L#?#@#,#-#M#Q#4#6#C#B#E#D#A#;#N#7#<#P#91#/%#D%#E&#F%#G&#H%#I%#J&#K'#L&#+%#M)#N&#O'VRCCUS##,$FE$#D$FD$ED#$#-&#k#$C#k#%*#j#&+#$FE#N#k##*##N+k###&*N'Dj#'.#$HFVS$#Dj#(N#j#(,D.N--$#Dj#'+#0-+)#US%;,<#E$#D$%D##:-%#m#)#j#$C#j#%B#,s#$HE$#D$HD##B-%#%CCI&#E'CCI(E#)%#,s#.GF$#E#%#$GE##s#'#(#k#)JJXS&JJKKWS'JKS(XS)JK#,_S*J&K%OS+-#+(D#.*##s#/VS,J#]S-JKS..+&$$#j#*7#VFED%CCD&#E'CCD(E#)%###4#$6##s#;-%#j#+s#H#+CCED%CC#&#F'CC%(F#)%#$IF##s#>#%#+CCFE%CC#&#H'CC%(H#)%#$LH#$#$GH#$#k##-##10##s#L#)'#+#k##%#+CCHF%CC#&#G'CC%(G#)%#$MG#$#$IG#$#+CCGH'CC#(I#+CCIG%CC#&#L'CC%(L#)%#$S/L#$#$ML0)'ED/'&#/&%#j#,/#j#':#YP;94#Dj#(s#)#%CC5&#I)#5$QI#$#$LI*&%D/%$#j#'A#*'&Dj#'A#.s#$BA%#Dj#(s#.#.s#7s#/s#30#Dj#'s#>##s#(s#&#s#*##0.#2#+CCLI%CC#&#M'CC%(M#)%#$S0M$QM#$#0)'ED/'$#j#,s#,#j#(@#YPAs#30#Dj#'s#;#/A?D*s##4#j#'s#=#.s#?s#>7&#Dj#(s#N#*s#@s#>D*s#B;#j#(s#P#.s#Rs#Qs#K&#Dj#'s#N#0s#Qs#L@#j#-C#j#.C#YS1CCs#h#GVs#ts#s#WS2s$TGH,s$U#E$#D$%D##s$S-%#m#)#j#$C#j#%s$[#j#/s$T#j#&s$]#j#+s$_#YS3s$`s$Vs$?#Dj#&s$`##"). Qed.

(* [comment removed for export] *)
Lemma xpres_of_munch : forall LB SP X W m m',
  munch W m m' -> wmono rsegs m m' ->
  Forall (fun iv : Z * Z => (hceil <= fst iv /\ snd iv <= SP) \/ (forall a, fst iv <= a < snd iv -> rin_ivs X a)) W ->
  (forall b, In b LB -> blk_addr b + blk_size b <= hceil) ->
  xpres LB SP X m m'.
Proof.
  intros LB SP X W m m' MU WM FW HB a Ha [Hc Hx].
  assert (OUT : outside W a).
  { clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
    pose proof (Forall_inv FW) as H1. cbn in H1.
    split; [| apply IH; apply (Forall_inv_tail FW)].
    destruct H1 as [[H1 H2]|H1].
    - destruct Hc as [Hc|[[Hc _]|(b & Hb & Hr)]]; [lia| hcb; lia|]. pose proof (HB b Hb). lia.
    - intros R. apply Hx. apply H1. exact R. }
  split.
  - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
  - intros Hw. apply WM. exact Hw.
Qed.

(* [comment removed for export] *)
Definition xclient_range (LB : list block) (SP : Z) (X : list (Z * Z)) (A n : Z) : Prop :=
  rclient_range LB SP A n /\ Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) X.

Lemma xclient_range_addr : forall LB SP X A n a, xclient_range LB SP X A n -> A <= a < A + n -> xclient LB SP X a.
Proof.
  intros LB SP X A n a [HR HX] Ha. split; [eapply rclient_range_addr; eauto|].
  induction X as [|iv X IH]; cbn; [tauto|]. pose proof (Forall_inv HX) as H1. cbn in H1. pose proof (Forall_inv_tail HX) as H2.
  intros [K|K]; [lia| exact (IH H2 K)].
Qed.

Lemma xpres_bytes_at : forall LB SP X m m' A bs,
  xpres LB SP X m m' -> bytes_at rsegs m A bs -> xclient_range LB SP X A (Z.of_nat (length bs)) -> bytes_at rsegs m' A bs.
Proof.
  intros LB SP X m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply xclient_range_addr; [exact HR|lia])) as [E _].
  rewrite E. reflexivity.
Qed.

Lemma xpres_wr_at : forall LB SP X m m' A n,
  xpres LB SP X m m' -> wr_at rsegs m A n -> xclient_range LB SP X A n -> wr_at rsegs m' A n.
Proof.
  intros LB SP X m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply xclient_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

Lemma xpres_rw_cells : forall LB SP X m m' A cs,
  xpres LB SP X m m' -> rw_cells rsegs m A cs -> xclient_range LB SP X A (Z.of_nat (cells_size cs)) -> rw_cells rsegs m' A cs.
Proof.
  intros LB SP X m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply xpres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply xpres_wr_at; eauto.
Qed.

Lemma xpres_stk : forall LB SP X m m' lo hi,
  xpres LB SP X m m' -> stk rsegs m lo hi -> SP <= lo -> Forall (fun iv : Z * Z => hi <= fst iv \/ snd iv <= lo) X ->
  stk rsegs m' lo hi.
Proof.
  intros LB SP X m m' lo hi HP ST HS HX. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi.
  assert (XC : xclient LB SP X i).
  { split; [left; lia|]. clear HP HW. induction X as [|iv X IH]; cbn; [tauto|].
    pose proof (Forall_inv HX) as K1. cbn in K1. pose proof (Forall_inv_tail HX) as K2. intros [K|K]; [lia| exact (IH K2 K)]. }
  destruct (HP i ltac:(lia) XC) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
Definition StrObj_foot (a : Z) (S : srep) : list (Z * Z) :=
  (a, a + 24) :: match sown S with None => [] | Some (_, A, alloc) => [(A, A + alloc)] end.
Scheme kc__1 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.Ref.CXXRep.HCW.srep Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Datatypes.option Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Datatypes.prod Sort Prop.
Scheme kc__4 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__5 := Elimination for Corelib.Init.Logic.ex Sort Prop.

Lemma xpres_StrObj : forall LB SP X m m' a S,
  xpres LB SP X m m' -> StrObj LB m a S ->
  xclient_range LB SP X a 24 ->
  (forall p A alloc, sown S = Some (p, A, alloc) -> Forall (fun iv : Z * Z => A + alloc <= fst iv \/ snd iv <= A) X) ->
  StrObj LB m' a S.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.block); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.mem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.CXXRep.HCW.srep); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.CXXRep.HCW.xpres); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.CXXRep.HCW.StrObj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.CXXRep.HCW.xclient_range); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Prog.bptr); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.CXXRep.HCW.sown); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.CXXRep.HCW.mkS); constr:(@kc__3); constr:(@kc__4); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.CXXRep.HCW.slen); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.Lists.List.In); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.rblock_range); constr:(HCEIL); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RSegs.rsegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.CXXRep.HCW.long_hdr); constr:(@Corelib.Init.Logic.ex); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.CXXRep.HCW.long_buf); constr:(@kc__5); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.CXXRep.HCW.xpres_rw_cells); constr:(@Corelib.Init.Logic.ex_intro); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells_bound); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.rclient_range); constr:(@Corelib.Init.Nat.add); constr:(@Corelib.Init.Datatypes.length); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Nat.sub); constr:(@Stdlib.ZArith.BinInt.Z.to_nat); constr:(@Corelib.Init.Logic.or_intror); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.RLIBC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.RCTX); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.RERRNO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.RSSP_GUARD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.RGOT_SSP); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.RVMLOCK); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.blk_addr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.blk_size); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Corelib.Init.Datatypes.nat); constr:(@Stdlib.Arith.PeanoNat.Nat.add); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_add); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_succ); constr:(@Stdlib.Arith.PeanoNat.Nat.sub); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_sub_max); constr:(@Stdlib.micromega.ZifyInst.of_nat_to_nat_eq); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.micromega.ZifyClasses.eq_iff); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.Tauto.X); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.Lists.List.Forall_impl); constr:(@Stdlib.micromega.ZifyClasses.or_morph); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.LiaTuning.zify_done); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.CB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.b8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.CXXRep.HCW.short_cells); constr:(@Corelib.Init.Logic.eq_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Prelim.zlength); constr:(@kc__2 (@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.block)); constr:(@kc__3 ((@Corelib.Init.Datatypes.prod) (@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Prog.bptr) (@Corelib.Numbers.BinNums.Z)) (@Corelib.Numbers.BinNums.Z)); constr:(@kc__3 (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z)); constr:(@kc__3 (@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Prog.bptr) (@Corelib.Numbers.BinNums.Z)); constr:(@kc__5 ((@Corelib.Init.Datatypes.list) ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH))))))))|] [|@iv; @alloc; @A; @p; @s; @o; @z; @junk; @b; @x; @y; @m; @n; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__x6; @__p1; @__p2; @__p3; @__arith; @__sat71; @__sat69; @__sat67; @__sat68; @__sat70; @z66; @H66; @z65; @H65; @z64; @H64; @cstr; @BB0; @a; @__x7; @__x8; @__p4; @zh; @H0; @H4; @H3; @H2; @H1; @H; @K; @hi; @lo; @a0; @BB; @BUF; @HDR; @DJ; @A63; @A24; @EV; @BR; @Hin; @Hl; @HB; @HA; @HP; @p0; @z0; @sown0; @bs; @sown; @sb; @S; @m'; @X; @SP; @LB|] "#:t#y%P#~%6$G##$T$K$p%7%5#$#}$.#M#)#0#(#+#,%@#*#%#/#4#-#.#8#L#7#9#3#<#@$7#2#6#;#y#D#N#'#1#5#A#E#:#?#H#K#S$E#=#>#I$Z%D#B#O$q$r#C#J%A#&#F#T#R%&#P#G#^$t$u$6%-#\#_#`%X#W#Z$\$'$1#X$z$|%0$-#Q#U#V#[$U$j#|$8$9#]#a$i$Y%<%=%Y$##Y$Q$s$h$y$f$R#b#d#f$>$%$I$`$a$b$c$d$e$v$x$w${$}$~%*%.%C%H%I$]%Q%P#c#m%[%Z$O$/$$$0$;$:$S$V$^$_$m$n%$%#%,%+%1%2%4%F%J%K%G#g%M%N%O%R%S%T%U%W%V#e#x#n#p%L%]%^$<$&$B$J$3$5$+$=$M$H$2$A$@$N%;%:$L$k$F$W$g$l%($X$C$D%%%9%3$($[$,$*$)$P$o%E%)%'%/%?%8$?%\$4%>%BU%#%#k%#C%%$'%%'$V&%&%%'$%(%%)%%*%%+%%,%%-$%.&%/'%0*#'$%1&%25$+$%3%%4%%5%%6%%7&%8%%9&%:&%;&%<*%=+%>'%?%%@$%A$%B(%C'%D/%E&%F%%G%%H'%I%%J*%K(%L%%M&%N&%O)USqMVS{CCUSq#YSdS&PRS:SQCS#RSQLESj*#*#*#F#GS$S#S&S:#UTHMUSePVS{NCVS{#C'NCS'L'%C#F.%#()(#%SQS'WSrCCF$$#WSsCCF$#SQ)%#j#$:#R;#S(k##+#k#%C#k#&C#k#'N#CS+S&PS:k##$#k##9#k##@#k##B#j#(T+#*Sj*#*#UTI#UTJ#USq#YSdS+S*S$S#S&+SQLCS(S$S&#GQS(S+S#s#'+S#PUSe#(s#(#BRs#3;S0k##$#k#%C#k#&C#k#'N#+PS:CS4S+S*#k##%#k##.#k##0#k##3#j#)s#4#YSdQS(S+S*S$.ML+R#CS;S+S$#GS4S;QS*s#;.MP+S*#USe#(s#=#s#7Rs#Hs#0S<k##$#k#%C#k#&C#k#'N#.MS:+S##CS)QS(#k##&#k##0#k##2#k##6#j#'s#G#YSdS)S0S4S;Q's#JCS'L.M#+S$#CS<S4Q#GS5S<S)S;s#R's#OCS&P.M#+S;#USe#(s#U#s#ORs#`s#HS/k##$#k#%C#k#&C#k#'N#'s#YCRS:.M#+S(#CS,S)S0#k##'#k##2#k##4#k##9#k#*C#j#'s#b#YSdS.S5S<S)S0'NCSQS''s#eC#L.M#+S(#CS,S<S0#GS/S,S.S)s#m'NCS#S&'s#kC#P.M#+S)#USe#(s#q#s#kRs#|s#dS1k##$#k#%C#k#&C#k#'N#'NCPR's#vC#S:.M#+S4#0#FSj/S:#$%#>s#|)S6?SDRS:Fs#g8S:#(C#E$s$*S:Es$/E#E#E#F#VT,+#-S:#%S5s$2$#R%RS:$#S5)%#5S:8R&HS,S5#1S0FR&HS/P#j#+s#v#,s#w##'##*##0##8##:##>##@##B#'NCS&P's$BC#R.M#+S0#0#/Rs#*$$#>s$G(S1?SDPR8Rs#)(C#E$s$PR-Rs##%S.s$R$#P%PR$#S.)%#5R0P&HS,S.#1S)FP&HS/S&#j#+s$:#,s$;##'##*##0##2##4##7##9##;#j##s###&HS/S.1&HS?S&0j#+s$G#,s$H##&##7##=##?##A##s#$##s#&#0s#^/Ps#R$$#'NCS$S#'s$qC#S&>s$q#SF?SDS#S&8S&s#S(C#E$s$zS&-S&s#M%S/s$|$#S#%S#S&$#S/)%#.M.+S<#0#5S&#S#&HS6S/#1S5FS#&HS1S$#j#+s$g#,s$h##'##-##3##5##7##:##<#'NCS*S$'s%2C#S#>s%2#S@?SDS$S#8S#s#p(C#E$s%;S#-S#s#j%S?s%=$#S$%S$S#$#S?)%#.M.+S5#0#5S##S$&HS1S?#1S.FS$&HSES*#j#+s%(#,s%)##'##-##3##5##7##:##<#'NCS+S*'s%OC#S$.M#+S.#0#/S$s$7$$#>s%T(S2?SDS*S$8S$s$6(C#E$s%]S$-S$s$0%S6s%_$#S*%S*S$$#S6)%#5S$0S*&HS1S6#1S,FS*&HSES+#j#+s%G#,s%H##'##*##0##2##4##7##9##;#j##s###&HSES61&HSFS+0j#+s%T#,s%U##&##7##=##?##A##s#$#'NCS(S+'s%zC#S*>s%z#S=?SDS(S+8S+s$\(C#E$s&'S+-S+s$V%SEs&)$#S(%S(S+$#SE)%#'NCQS('s&+C#S+.M#+S/#0#5S+#S(&HS@SE#1S?FS(&HS2Q#j#+s%r#,s%s##'##/##5##7##9##<#?SDQS(8S(s$w(C#E$s&BS(-S(s$q%SFs&D$#Q%QS($#SF)%#'NCS;Q's&FC#S(.M#+S?#0#5S(#Q&HS2SF#1S6FQ&HS=S;#j#+s&1#,s&2##'##/##5##7##9##<#'NCS4S;'s&WC#Q.M#+S6#0#/Qs%?$$#>s&\(S8?SDS;Q8Qs%>(C#E$s&eQ-Qs%8%S@s&g$#S;%S;Q$#S@)%#5Q0S;&HS2S@#1S1FS;&HS=S4#j#+s&O#,s&P##'##*##0##2##4##7##9##;#j##s###&HS=S@1&HSJS40j#+s&\#,s&]##&##7##=##?##A#?SDS4S;8S4s%`(C#E$s'+S4-S4s%Z%S=s'-$#S0%S0S4$#S=)%#'NCS)S0's'/C#S4.M#+SE#0#5S4#S0&HSNS=#1SFFS0&HS8S)#j#+s&v#,s&w##'##/##5##7##9#8S0s%y(C#E$s'DS0-S0s%s%SJs'F$#S)%S)S0$#SJ)%#'NCS<S)'s'HC#S0.M#+SF#0#5S0#S)&HS8SJ#1S@FS)&HS>S<#j#+s'3#,s'4##'##/##5##7##9#'NCS5S<'s'XC#S).M#+S@#0#/S)s&@$$#>s'](SA?SDS<S)8S)s&?(C#E$s'fS)-S)s&9%SNs'h$#S<%S<S)$#SN)%#5S)0S<&HS8SN#1S2FS<&HS>S5#j#+s'P#,s'Q##'##*##0##2##4##7##9##;#j##s###&HS>SN1&HSRS50j#+s']#,s'^##&##7##=##?#8S<s&_(C#E$s(*S5-S5s&Y%S>s(,$#S.%S.S5$#S>)%#'NCS,S.'s(.C#S5.M#+S=#0#5S5#S.&HSWS>#1SJFS.&HSAS,#j#+s'u#,s'v##'##/##5##7#$s(@S.-S.s&o%SRs(B$#S,%S,S.$#SR)%#'NCS/S,'s(DC#S..M#+SJ#0#5S.#S,&HSASR#1SNFS,&HSGS/#j#+s(/#,s(0##'##/##5##7#'NCS?S/'s(SC#S,.M#+SN#0#/S,s';$$#>s(X(S-?SDS/S,8S,s':(C#E$s(aS,-S,s'4%SWs(c$#S/%S/S,$#SW)%#5S,0S/&HSASW#1S8FS/&HSGS?#j#+s(K#,s(L##'##*##0##2##4##7##9##;#j##s###&HSGSW1&HSOS?0j#+s(X#,s(Y##&##7##=#$s(~S/-S?s'Q%SGs)$$#S6%S6S?$#SG)%#'NCS1S6's)&C#S?.M#+S>#0#5S?#S6&HSBSG#1SRFS6&HS-S1#j#+s(m#,s(n##'##/##5#-S6s'e%SOs)8$#S1%S1S6$#SO)%#'NCSES1's):C#S6.M#+SR#0#5S6#S1&HS-SO#1SWFS1&HOSE#j#+s)%#,s)&##'##/##5#'NCSFSE's)HC#S1.M#+SW#0#/S1s(0$$#>s)M(SV?SDSES18S1s(/(C#E$s)VS1-S1s()%SBs)X$#SE%SES1$#SB)%#5S10SE&HS-SB#1SAFSE&HOSF#j#+s)@#,s)A##'##*##0##2##4##7##9##;#j##s###&HOSB1&HS9SF0j#+s)M#,s)N##&##7#-SEs(D%Os)s$#S@%S@SF$#O)%#'NCS2S@'s)uC#SF.M#+SG#0#5SF#S@&HSKO#1SOFS@&HSVS2#j#+s)`#,s)a##'##/#%S9s*)$#S2%S2S@$#S9)%#'NCS=S2's*+C#S@.M#+SO#0#5S@#S2&HSVS9#1SBFS2&HSkS=#j#+s)r#,s)s##'##/#'NCSJS='s*8C#S2.M#+SB#0#/S2s(|$$#>s*=(SS?SDS=S28S2s({(C#E$s*FS2-S2s(u%SKs*H$#S=%S=S2$#SK)%#5S20S=&HSVSK#1S-FS=&HSkSJ#j#+s*0#,s*1##'##*##0##2##4##7##9##;#j##s###&HSkSK1&HSTSJ0j#+s*=#,s*>##&#%SVs*a$#SJ%SJS=$#SV)%#'NCS8SN's*cC#SJ.M#+O#0#5SJ#SN&HSCSk#1S9FSN&HSSS8#j#+s*N#,s*O##'#'NCS>S8's*oC#SN.M#+S9#0#5SN#S8&HSSST#1SKFS8&HSlS>#j#+s*Z#,s*[##'#'NCSRS>'s*{C#S8.M#+SK#0#/S8s)c$$#>s+$(Sf?SDS>S88S8s)b(C#E$s+-S8-S8s)\%SCs+/$#S>%S>S8$#SC)%#5S80S>&HSSSC#1SVFS>&HSlSR#j#+s*s#,s*t##'##*##0##2##4##7##9##;#j##s###&HSmSR/j#+s+##,s+$#'NCSWSR's+CC#S>.M#+SV#0#5S>#SR&HSmSS#1STFSW&HSfSA#j#+s+.#,s+/#1SCFSA&HS|SG#j#+s+2#,s+3#'NCSOSG's+RC#SA.M#+SC#0#/SAs*:$$#>s+W(S]?SDSGSA8SAs*9(C#E$s+`SA-SAs*3%Sas+b$#SG%SGSA$#Sa)%#5SA0SG&HSfSa#1SSFSG&HS|SO#j#+s+J#,s+K##'##*##0##2##4##7##9##;#j##s###&HSbSO/j#+s+V#U#F1SlFSO&HSnSB#'NCOS-'s+xC#SB.M#+Sm#0#/SBs*`$$#>s+}(S^?SDS-SB8SBs*_(C#E$s,*SB-SBs*Y%Sbs,,$#S-%S-SB$#Sb)%#5SB0S-&HSnSb#1SaFS-&HS]O#j#+s+p#,s+q##'##*##0##2##4##7##9#^S}S^SXStS]SnSb/SORSA1SmLSBYTKHS]S-#F$ES-USo%4#%S-#*s,'*#*#F#VT,s+$#$(##,#=s,,Sa7SHUScS-D#%D#%9#SH9'#9)#4#XTLS_S^O#=s,6SfUScOD#$D#.9#SH90#9(#4#%S9#$#s,T$s,SS9)$#j#$s,j#Rs,k#SX$S^O*s+;E#*#*#*#*#*#*#*#*#*#*#*#*#*#F#ESjE#E#*#E#*#*#*#*#*#*#*#*#*#*#*#*#*#F#*SjE#E#*#E#*#*#*#*#*#*#*#*#*#*#*#*#*#*#F#$7O%Os#KEs-%*#E#*#*#*#*#*#*#*#*#*#*#*#*#*#*#F#$57$6TM*s,-E#*#*#*#*#*#F#%TN#$#O)-#$BT-Fs-E%T-#$#O)&#$s#'T.Fs-I%T.#$#O)&#$s#,T/%T/'$#O)%#$s#0T0%T00$#O)%##'##,##2##8##s#%##s#:#>MFSuUT1F$#S9UT2F%%#$s#~##&##)#j#,M#,M#)-#'NCS9O's.%C#S->M#S_$OO7s$99s$?#4#%O#%OS-$$##)#4s$E:ES-/#$:E#/#s,s:E#%#E%#s,v%*#%O#$#/#5#USv6j#-CF$LFUSv#j#.C#j#-C#%LFXTOCCTP#;C#j#/C#j#0C#;CO4F;C#j#-I#;C=%Fs-/j#-C#/LF:E#j#/C#j#0C#:EFj#-C#;CS-ICICCSc:G$T3S-S-#6IIICCCSYGGG'SZs$is#'#s$ks#(-;Cs-:6IIICCCSYGGG)SZs$js#'$s$ls-;#;CE6IIICCCSLGGGS3SMs$ks#'$SHE#IIICCSwGG0S~s$ks#'#6IIICCCSLGGGS3SMs$qs#.3s#5s#'#IICCCGGBB5s#5s#'#6CCCCCCS3s##s##s##S3:OO9s#5s#(#;Cs#4`SpCCS[s#%S[As#6s#)$s#5s#5#ZT#s#;s#5s#;s#)s#'#$EO$s$'s${#$#%s-Hs#1%s#8#%O#$#s%$#)#U9S-V<#s#=V=#s-O%#E%s-Q#%s#A#Us#5#%O#$#s%.;S73(S744m#$#WT466#6IIICCCSYGGGs#(SZs%./s#$s%0s#Is#.6IIICCCSYGGGs#)SZs%./#s%0s-[s##6IIICCCSLGGGS3SMs%./#SHEB6IIICCCSLGGGS3SMs%2s-]s#%s%./#6IIICCCSLGGGS3SMs%4s#Ms#2s%./#IICCCGGs#As#As#4s%./#6CCCCCCS3s#Bs#Bs#BS3s#9OOs#8s%./#;Cs%:(Cs%;s%;m#$#`SpCCS[s#FS[s#Bs$E2&s%=s%=#ZT#BAB2.#XT5A<#FUT$s%34s%4$E#VSgES9-ES9:ES9(C#S9#%#$S9E(C&E#$#)&#:ESK=s.tSn4#/F#VSgE#-E$:E%(C#&#%#$(E(C&E#$#)&#=s/$S]4#/L#:E#/Fs.(VSgE#-E$:E%(C#&#%#$(E(C&E#$#)&#/Ls.2:E#VT6s./s.'-Es.0$Es.)-Es.)k##$#k##&#$Es.5WT7s.6s..Lj##Sh#j#1%#$Es.0k##Sh#k#1(#VT6s.<s%w$Es%x-Es%xk##$#k##2#WT7s.As%|Lj##Sh#j#10#$Es%~k##Sh#k#13#VT8Sfs.G$ESf8Sbs.I$E#k##8#k##&#VTQEs.M;TR#m##AUS'#UR$7s&,7#7#7#KC#UTSSjVTTC#KC(WT9C$#KCs&5<C$#<C)#L#S\7,KC#KCSH<C+#<C/#<C&#L#S\KC4<C#'<C*#L#S\UT:SU@SU$#@SU)#@SU1#USqSUVSiCS:VSiCRMC$S'#UTUCVSiCPMC$SQ#MC&L#UTVCUTWCVSxCENCs.uVSxCs/#SC$#2C&Sy#3(KDDJ#S%NCs0K2C#SP&3+KDDJ#S%A,KDDJ&#T-KDDJS#2C'SP-3/KDDJ#S%A0KDDJ%#O1KDDJ'#UT;DNCs0TNCs06SC$#2C5Sy#37KDDJ#S%2C6SP%39KDDJ#S%A:KDDJ%#2C(SI:3<KDDJ#S%2C;SP<3>KDDJ#S%A?KDDJ%#O@KDDJ(#TAKDDJS$NCs0C2C2SP#3s#$KDDJ#S%As#%KDDJ&#2C&SIs#%3s#'KDDJ#S%Ts#(KDDJS*As#)KDDJ$#Os#*KDDJ'#VSxCs0i2C#SI,3s#-KDDJ#S%SC.s#+2C=SI#3s#0KDDJ#S%NCSj2C#SI#3s#3KDDJ#S%JCs#-s#3JC#s#2JCs#$#JC(#JC)82C$SI#3s#:KDDJ#S%As#;KDDJ*#Bs#<KDDJ.s#,#Bs#=KDDJ2s#-#Bs#>KDDJ6s#.#Bs#?KDDJAs#/#Bs#@KDDJs#1s#0#VTXs#AJ;T<T=VTYFS'(T<#T=m$%#WTZCELXT[FS'$#l#2*)#l#3s#Ks#J#l#4s#Ts#S#j#5C#j#6C#j#7C#j#8C#j#9C#j#:C#j#;S7#j#<S7#j#=S7#-Es/J(CS's/K#$#(CS'E#P#)%#/RS'-E#(CP$#$#$&E(CPE#$#)&#(CPR#S$#$RE##S*)%#$s1IP/S&s0*$R#$RR%S&E%#s0.%P#%R#%RS#$$##)#k##+#k##.#k##0#k##6#k##?#k#5C#k#6C#k#7C#k#8C#k#9C#k#:C#k#;S7#k#<S7#k#=S7#(CS(E-ES]/S*s0D$#E=s1FT\4#bF('%S*S(S]S##StS$S+QS>Sll#>s#6*#l#?s$Rs$p#l#@s$Ts$e#l#As$^s$Y#l#Bs$cs$`#l#@s$ks$g#l#Cs$ps$m#l#?s$zs$u#l#Ds$|C#l#Es%+s%##l#Fs%.C#l#Gs%;s%3#l#Hs%@C#l#Is%Js%B#l#Js%Ns%L#l#Ks%Ps%j#XT%s&Is&=s%s#Hs&Rs&JS=#UT1s&T$#OUT2s&V%%#$s'@##&##s&Y#m#*#XT&Ms&`s&\#WT>s&js&`#WT>s(#s&`#%S9O$#s1|)#s(*j#$s25#%SKS9$#s2$$s2#SK)$#=s1nSbUScSKD#$D#s(F9#SH7#9(#4#%SV#WSrCCL$$#WSsCCL$#SV)%#k##1#j#'s2I#%STSk'CCLFWSrCC#$%#WSsCC%$#ST)%#=s2)StUScSTD#$D#s(]9#SH7#9(#4#%SC#$#S'$LSC)$#4.:EST/#$:E#/#s19:E#%#E%#s1<%*#%SC#$#S')#/;CSC;C/;CSTICICCScs'&Gs&lT3STST#6IIICCCSYGGGs&oSZ=1#>2%6IIICCCSYGGGs&pSZ=0#s(ws1Fs&j6IIICCCSLGGGS3SM=/#SHEs&iIIICCSwGGs&vS~=/#6IIICCCSLGGGS3SMB6)=/#IICCCGGs',s',s&{=/#6CCCCCCS3s'-s'-s'-S3s'$SCSC,=0#;CS'`SpCCS[s'/S[s'+>1$S'S'#USv=ZT]?>2>$#$ESC$Bs)*#$#$7s),#&#Us&}STVs'$#s##Vs'%#s1W%#EUs'+#%s#'#Us'=#%SC#$#s)6;S70(S711m#$#WT433#6IIICCCSYGGGs'0SZs#:/@s#;s#/B6IIICCCSYGGGs'1SZs#:/#s)8s1cs'+6IIICCCSLGGGS3SMs#:/#SHEs'*IIICCSwGGs'7S~s#:/#6IIICCCSLGGGS3SMs#?s#3s#&s#:/#IICCCGGs'Is'Is'<s#:/#6CCCCCCS3s'Js'Js'JS3s'ASCSCs#)s#:/#`SpCCS[s'KS[s'Gs#:/#s)Bs)Bs&dZT#<;</+#XT5;9#P=s2lSXUT$#4$$E#VSgESS-ESS:ESS(C#SS#%#$SSE(C&E#$#)&#:ESl=s2zSu4#/F#VSgE#-E$:E%(C#&#%#$(E(C&E#$#)&#=s3*T'4#/L#:E#VT8SXs2)$ESX8S_s2+$E#k##s&V#k##&#VT^S^s2/(Cs20EUT_#VT?S_s22VT@s23#%#+(CS_#k##'#VT`S_s278Sus28$E#-$s2:#$#k##s&j#VTaSus2=-s2>E8T's2?-s2@#$$E#$#k##'#VTbT's2DVT?TAs2E(C#Ek##9#VTcTAs2H8T(s2I(C#T(k##=#VTdT(s2Lm#Te#US:s&]8Tfs2O$E#-$s2Q#$#VS*FLj#Ls&}#k#Ls&~s&oUS+s&eVS4FLj#Ls'%#k#Ls'&s&~US0s&i7s&ZKC#KCs&i<C#s&a<Cs&W#<C&#L#S\7)KC#<C#'L#S\<Cs&^s&i<Cs&o#<Cs&f#<C(#L#S\@SU#s&_@SU)#@SU.#VSiCS#MC#Ps&[MCs&_S'#VSiCS&MC#Rs&^MC#SQs&_MC&L#Es3~*#NC#SC#s&\2Cs&_Sy#3s&aKDDJ#S%2Cs&[SP%3s&cKDDJ#S%As&dKDDJ%#As&eKDDJs&?s&XOs&fKDDJ$#NCs)eSC#s&V2Cs&hSy#3s&jKDDJ#S%2C/SP%3s&lKDDJ#S%As&mKDDJ%#Ts&nKDDJS+2C3SPs&n3s&pKDDJ#S%As&qKDDJ%#Os&rKDDJ'#Ts&sKDDJS(2C/SPs&c3s&uKDDJ#S%As&vKDDJ%#2Cs&fSIs&v3s&xKDDJ#S%Ts&yKDDJQAs&zKDDJ$#Os&{KDDJ'#JCs&Ms&k2C#SIs&]3s&~KDDJ#S%NCs#%2C#SIs&Q3s'%KDDJ#S%Os'&KDDJ&#2Cs&ZSIs&r3s'(KDDJ#S%SCs&ts'&2Cs&tSI#3s'+KDDJ#S%2Cs&SSIs&h3s'-KDDJ#S%Os'.KDDJ#+Bs'/KDDJ&s&{#Bs'0KDDJ*s&|#Bs'1KDDJ-s&}#Bs'2KDDJ5s&~#Bs'3KDDJ?s'##Bs'4KDDJs#,s'$#l#2#s&Rs&Ll#3s#9s'7#l#4s#As'@#j#5C#j#6C#j#7C#j#8C#j#9C#j#:C#j#MC#j#NC#j#;S7#j#<S7#j#=S7#j#OS7#-Es&:(CS's&;#$##S#s&N)$#/S&S'-E#(CS#$#$#(CS#E#S*#)%#(CS#S&#S(#$S&E##Q)%#%SQS#$#P$S&SQ)$#$Ps&5%S#E%#s3y%S&#%P#$#S$$S*P)$#k##*#k##s2E#k##-#k##2#k##8#k##@#k#5C#k#6C#k#7C#k#8C#k#9C#k#:C#k#MC#k#NC#k#;S7#k#<S7#k#=S7#k#OS7#(CS?E-ETB=s57Tg4#/S?#$#E$s/^EfF)($#S,S?TBS@S2S5&ThS.S/S6SFSmT)l#>s#:+#l#?s$=s(d#l#Cs$@s$?#l#PS:Sh#l#@s$Ds([#l#Bs$Gs$F#l#PLSh#l#Qs$Os$K#=s5ETi4#%S+E%#s4H%%#%T)#$#S,$S.T))$#m#,#l#Rs$[s$\#l#Ss$as$^#l#Ts$fs$c#l#Us$ns$h#l#Qs$us$p#l#Vs$~s$w#l#As%)s%$#l#Bs(ls(i#l#@s(ts(p#l#Cs(ys(v#l#?s)'s(~#l#Ds))C#l#Es)4s),#l#Fs%1C#l#Gs%>s%6#l#Hs%CC#l#Is%Ms%E#l#Js%Qs%O#l#Ks%Ts%k#XT%s&0s&$s%q#'CCS'LWSrCC#$s&6#WSsCC%$#SC)%#m#)#j#Ws&D#j#XC#j#YC#V#LFj#*C#j#*C#YT*CCs&Q#Fj#Zs6=#j#$s6>s&cU#F=s5tS|UScS9D#$D#s,L9#SH9s,N#9(#4#%SK#$#s&d$s&cSK)$#k##/#k#Ls6M#m#3#.Ms*|;s6F#XSAS9OS-#ZTjs6Rs&{s,F&SX#Hs,Ts,Fs'$#VSzs,^SaUTCEUTD#VSzs,]S'UT:S`@S`$#@S`&#@S`)#USo#4#GS_S^SXO#m#.#1SaS'S-USo#4#GS_S^SXO#m#'#l#[s,{s,p#^S}S^SXStS]SnS-s,}SOF#XT&s6>s-,L#Hs-0s-,s-$#Hs-3s-,S$#Hs-9s-,Q#Hs-;s-,S)#Hs-=s-,S,#Hs-@s-,S1#Hs-Bs-,S2#Hs-Ds-,S8#j#\s-L#j#+s6H#V#LFj##s-Q#j#-s6K#YTEs6Ls-xs-V#Fj#Vs-|#j#]s.%#V#LFj##s..#j##s.X#Ps.Ys.Us.3#Fj#Vs.a#j#^s.n#V#LFj##s.u#j##s/M#Ps/Ns/Bs.|#Fj#Vs/T#j#_s/g#V#LFj##s/j#j##s0I#Ps0Js08s/r#Fj#Vs0L#j#`s0a#V#LFj##s0d#j##s1F#Ps1Gs13s0m#Fj#Vs1I#j#as1`#V#LFj##s1d#j##s2I#Ps2Js24s1n#Fj#Vs2M#j#bs2g#V#LFj##s2j#j##s3S#Ps3Ts3;s2u#Fj#Vs3V#j#cs3r#V#LFj##s3w#j##s4a#Ps4bs4Is4'#Fj#Vs4f#j#ds5(#V#LFj##s5-#j##s5z#Ps5{s5\s5:#S'CS6S.S5s6$m#$#j#es6*#j#fs66#j#Vs68#j#gs6>#j#%C#j#&C#j#'N#V#LFj#*C#j#,N#YT*NCs6F#Fj#hs7K#V#LFj#*C#j#'s7N#YT*s7OCs6e#Fj#,M#U#Fj#,M#YSdS*S$S#S&PUT;M+S'#CS+S#P#GS(S+S*S&s7[+S&&USe#(s7\#s7VRs7gs7OS4k##$#k#%C#k#&C#k#'N#+R.0#Es&**#F#$&#QPF&HS(S*#j#+s7K#,s7L##'#+P90#$#+QS&F&HS(S+#j#+s7S#,s7T##'#j##+#&HQS+(j#+s7X#,s7Y#0A$#6QS$F&HS4Q#j#+s7^#,s7_#QS*F&HS0S;#j#+s7b#,s7c#+S*s#/0#$#AQS+F&HS0S4#j#+s7i#,s7j##'#j##+#&HS)S4(j#+s7n#U#FQS(F&HS<S0#+Qs#=0#$#s#/QS;F&HS5S<#j#+s7w#,s7x#QQL=s7{Q7s&s7#7#7#7#7#7#7#7#7#7#7#7#7#D#19#SH9s.a#94#9s.c#4#(Cs8T#48/s#L#:E#%#E%s79#%'#%s7;#(Cs8\#UTFC(CLFUSv#j#.C#j#-C#;Cs8b;C0;Cs#Z6IIICCCSYGGGs,oSZ:s#[#s#(2$6IIICCCSLGGGS3SM:1#SHEs,h6IIICCCSLGGGS3SMs.xs7Gs,k:1#6IIICCCSLGGGS3SMs#+5':1#6IIICCCSLGGGS3SMs.zs7Is,m:1#IICCCGGs-,s-,s,{:1#`SpCC0s--0,s8ks8k+:2#UT$s#/$E:=s8NS;4#/s#f#VSgE#-E$:E%(C#&#%#$(E(C&E#$#)&#=s8ZS44#/s#r#:E#WT9Cs+_s'Z<C#s+W<Cs+`#L#S\<Cs+`s+Z<Cs'_#L#S\L(S\@SU#s+U@SU%#@SU)#VSiCS'MC#Ls+QTs+MKDDJS:VSxCs$&SC#s*|2Cs+>SP#3s+QKDDJ#S%As+RKDDJ'#2C&SIs+R3s+TKDDJ#S%2Cs+CSPs+T3s+VKDDJ#S%As+WKDDJ%#Os+XKDDJ(#2Cs+*SI-3s+ZKDDJ#S%JCs+Is+ZJCs+Y#JCs+.#JCs+[#2Cs+6SP#3s+`KDDJ#S%Bs+aKDDJ)s+Q#Bs+bKDDJ,s+R#l#2#s+$s*zl#3:s+e#l#4=s+n#j#5C#j#6C#j#;S7#/s$AF(CL##S'#$%E(CLE#$#)&#$Ls$H%SQE%s84#%S'#%s86#(Cs9W#k##(#k##*#k#5C#k#6C#k#;S7#=s9=S)4#/s$U#-E#YF#L%S'S$l#>:(#l#is#DC#l#Qs#Qs#I#l#Js#Ws#V#XT%s#ps#hs#Y#GS6S?S/S5Fj#*C#Ds#zs#Y9#SH9s/|#9s#\#9s/~#4#ZTkCs9o)S*#Fl#Q,s#z#VTls9QQVT@s8M#UTC#UTD#VSzs$8QVSzs$*L@S`#s&)@S`s&,#@S`&#@S`(#USo#4#GS/S,S.S)#m#0#USos$C4#GS/S,S.S)#m#&#^S}S/S,S.S5S<S)s$GS+F#XT&s9cs$JL#Hs$Ns$JR#j#Vs$R#j#+s9f#V#LFj##s$W#j#-s9i#YTEs9js$fs$\#Fj#Qs$j#j#ds$o#V#LFj##s$s#j##s%)#Ps%*s%&s$x#S'CS;S*S$s%0m#$#j#es%3#j#fs%<#j#Vs%>#j#gs%B#YTmMs9ds%D#Fj#js:;#j#ks9y#V#LFj#ls:>#j#ms9|#WTns:'#Fj#nT+#j#LC#j#oTG#j#/TG#j#ps:N#j#qC#j#rs:R##"). Qed.

Lemma disjoint_from_mono : forall W a n n', disjoint_from W a n -> n' <= n -> disjoint_from W a n'.
Proof. induction W as [|[lo hi] W IH]; cbn; intros a n n' H Hn; [exact I|]. destruct H as [H1 H2]. split; [lia| eauto]. Qed.

(* [comment removed for export] *)
Lemma StrObj_transport : forall LB W m m' a S,
  StrObj LB m a S -> munch W m m' -> wmono rsegs m m' ->
  disjoint_from W a 24 ->
  (forall p A alloc, sown S = Some (p, A, alloc) -> disjoint_from W A alloc) ->
  StrObj LB m' a S.
Proof.
  intros LB W m m' a [bs [[[p A] alloc]|]] H MU WM DA DB; cbn in *.
  - destruct H as (Hl & Hin & BR & EV & A24 & A63 & DJ & HDR & junk & BUF).
    repeat (split; [assumption|]). split.
    + eapply rw_cells_transport; [exact HDR| exact MU| exact WM|]. exact DA.
    + exists junk. eapply rw_cells_transport; [exact BUF| exact MU| exact WM|].
      unfold long_buf. cbn [cells_size csize]. unfold slen, zlength in Hl; cbn in Hl.
      eapply disjoint_from_mono; [exact (DB p A alloc eq_refl)| lia].
  - destruct H as (Hl & junk & H). split; [exact Hl|]. exists junk.
    eapply rw_cells_transport; [exact H| exact MU| exact WM|]. unfold short_cells. cbn [cells_size csize].
    unfold slen, zlength in Hl; cbn in Hl. replace (Z.of_nat _) with 24 by lia. exact DA.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive sres : Type := SShort | SLong (p : bptr) | SFail.

(* [comment removed for export] *)
Definition str_new_M (n : Z) : M PState sres :=
  if n <? 23 then mret SShort
  else mbind (raw_malloc (str_alloc n)) (fun r => mret (match r with Some p => SLong p | None => SFail end)).

(* [comment removed for export] *)
Definition str_grow_M (old : option bptr) (newalloc : Z) : M PState sres :=
  mbind (raw_malloc newalloc) (fun r =>
    match r with
    | None => mret SFail
    | Some p' => mbind (match old with Some p => raw_free p | None => mret tt end) (fun _ => mret (SLong p'))
    end).

Lemma str_alloc_bounds : forall n, 23 <= n -> n + 1 <= str_alloc n <= n + 8 /\ str_alloc n mod 2 = 0 /\ 24 <= str_alloc n.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.ZArith.Zbitwise.Z.sub_lor_land); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.lor); constr:(@Stdlib.ZArith.BinInt.Z.land); constr:(@Stdlib.ZArith.BinInt.Z.lxor); constr:(@Stdlib.ZArith.Zbitwise.Z.add_lxor_2land); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.ZArith.BinInt.Z.ones); constr:(@Stdlib.ZArith.BinInt.Z.land_ones); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.eqb_spec); constr:(@Corelib.Init.Datatypes.reflect); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Corelib.Init.Logic.not); constr:(@Corelib.Init.Logic.eq_sym); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Corelib.Init.Logic.False); constr:(@Stdlib.ZArith.Zdiv.Zplus_mod_idemp_l); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.CXXRep.HCW.str_alloc)|] [|@z; @__ff; @__varmap; @__wit; @__arith; @__x1; @__x2; @__x3; @__x4; @__sat2; @B1; @A1; @C; @__sat0; @__p1; @e; @__x5; @H1; @H6; @r0; @q0; @H9; @H8; @H7; @H5; @r; @q; @H4; @H3; @H2; @H0; @n0; @b; @n; @H; @L; @Hn|] "#*%#=$6#@#]#^#\#a###$#c#%#&#b#(#'#+#|#)#*#V#,#E#f#3#r$&#=$%#-#.#0#7#g#O#q$)$/$1$2#/$3#1#4#5#6$5$4$6$7$8#F#L#Q#S#U#W#X#Y#[#d#h#i#e#T#u#t#}$($,#2#8#<$.$9$:#A#G#P#M#H$##_#Z#x$'#n#`#y#B#N#D#v#C#J#K#o#z#~$+$0#I#R#j#p#l#m#w$*#k#s#{$$$-I#l%#m&#n%#o%#p%#q%#r'#s*#t+#u%#v&#w%#x&#y$#z%#{$#|'#}$#~%$#%$$%$%%$&&$'*$(%$)%$*%$+)$,$$-&$.%$/%$0'$1%$2&$3&$4%$5$2S&4#4#4#0###H4S&4#0#VSCI#<I$5I%'$#6I'$C$#VSDK)6K*035K,1$#&&#&K/$C$#03VSE)#%L#2<2#0#%O#$CH#j#$C#%L&=C#USF-5L#USGS$USHS$USICUSJCUSKC.CG.C5)C$M#*&FDDE#JVSL'E=S'S1VSMHK$S'#S1m$%#WSNCGIXSOHK$#l#%*)#l#&10#l#'43##GBl#($#HWSPLs#$#ZS2Cs##=;9#5Ls#5$C#>5Os#7<Ns#8'#H6Ns#:$C$#j#$C#>C(#Ks#(H<Os#>'#s#*6Os#@$C$#5Ns#B6Rs#C1s#;H&$#&Rs#F$C$#j#$C#%Ns#5>C*$K#I1s#B$&4#&Ns#M$C$#DRs#;#GR#Gs#=%Ps#>#G#k##%#k##'#?S3?#?#7C#7C%7CS3-C$#-C&#A#S)USQS&VSRC#EC#*EC$*-C#*-C%#A#S)@S$#s#J@S$+#BCO3C#Ks#KBCL3C$I#8Cs#Z.Cs#d8Cs#pFC$#/C&#8Cs#y.Cs#r/C$#)C&Q#*s#UFDDE#JUSSD8CS&9C#,)C#Q/*s#ZFDDE#J.Cs$#)C#M-*s#]FDDE#J9C-2)C*Q#*s#`FDDE#J+s#aFDDE&-#+s#bFDDE*.#+s#cFDDE0/#l#%#s#_s#Yl#&<s#f#l#'As#i#j#)C#j#*C#j#+C#j#,C#1s$&K&L#&Is$1$C$#'IL$C#O#s$9L&Os$6'#N$CL#k##&#k##(#k##+#k#)C#k#*C#k#+C#k#,C#6Ps$@<Ps$A[H$s#NP#KLS#l#(7&#l#-s#Ss#M#l#.s#Ys#U#l#/s#gs#c#l#0s#qs#o#l#.s$As$:#l#/s$Hs$C#%Is$6'<#$Cs$J#%Ks$9's$A#0S&&L#GHs$U2s$T4#2#0#&H)nS'#$##C(#%#$###*#&Ls$E#%#(%#%'s$S$C#G2.2#0###,('#(*#j#$C#DKs$Q#GK#Gs$Rk##s#u#k##%#.Cs$V)Cs$JS*#*s$LFDDE#Jl#%#s$Hs$Bl#&s$Ps$O#l#'s$Ss$R#,Gs$\l#($#Hl#1/+#WS,Ks$_##Gs#),s#*s$a($#&Ls$w'#s$`VST#s$}$C$s$~G%s%#VS4$#'s#Is$hG#s%&'s$4s$8$C#s%(&S#s#4&S#s%&%S#s$o'$#&#s#8nS'#$##CI#%#s#3###(#&S#s$t#%#(%#%'s%&$C#G#s#/)($#('#%Rs$|'s$M#$C#s%:#4s#@#s#A.($#%s#Cs%1$C#G#s#:s#E($#DS#s%*#GS#%S%s%,#G#k##s$O#k##&#@S$s$Ds%(BCK3Cs%(I#/Cs$.s$39C#s$8)C#Qs$,*s%*FDDE#JZSUs%+FDDEO)Cs$<S*s#@*s%-FDDE#J:s%.FDDE%#)Cs$2Ms$6*s%0FDDE#J.Cs#`/Cs$9#.Cs#\)C$M#*s%5FDDE#J/Cs$=s#J)C&M#*s%8FDDE#J:s%9FDDE&#+s%:FDDE,s$B#+s%;FDDE/s$C#+s%<FDDE4s$D#l#%#s%8s%2l#&:s%?#l#'=s%B#j#)C#j#*C#j#2S+#&Hs%c'#I$C#s%i,Ks%R(L##s%lK#s#ws#r#s#ss#o($#k##&#k##(#k##+#k#)C#k#*C#k#2S+#ZHs#3s#4S%KRPl#(3$#l#1s#8s#3#=CG.Cs#t)C#Ms#&*s%XFDDE#Jl#%#s%Ts%Nl#&s%\s%[#l#'s%_s%^#l#(#s#BHl#1s#As#<#Cs#Es#D+#Cs#Hs#D-#j#3s#L#U#HHs#N#s#`s#\#s#]s#Z($#%s#_s%}$C#G#s$*s#a($#3Cs#GIs%l)Cs%jMs$x*s%lFDDE#J)Cs$zS*s$%*s%nFDDE#J:s%oFDDE%#9Cs#Ks$}/C#s#B)Cs#BM#*s%sFDDE#J)C%Ms#@*s%uFDDE#J:s%vFDDE%#+s%wFDDE*s%##l#%#s%ss%ml#&1s%z#l#'s%~s%}#j#)C#j#*C##GI,Is&.($#&Is$S's$rK&#s$U#%#&Is&4#%#(%#k##*#k#)C#k#*C#WHs#lS%Rl#(1$#l#1s#ps#k#9Cs%8s%>/C#s$F)C#Q@*s&4FDDE#Jl#%#s&0s&*l#&s#*s&7#l#'s&;s&:#j#)C#j#*C#'HI&#s&G&s#Vs$k$C$#k#)C#k#*C#VHs#~S%l#(*$#l#1s$&s#}#'S#s$>&#s&P$C#s$>'Ps%r&#s&S%Hs&_$C#Gj#$C#%'s&b&#s&X%#s&d$CHGj#$C#VS5,s&g$Cs&hGH#'S%s$5;#s&k1s&l#%%s&m&$#$C'#k##)#VS,)s&q,Gs&r%S-s&h'S-#%#s&u#G#,$s&w($#k##)#VS6(s&z,s&{G%S.s&q'S.#%#s&~,s'###$G($#k##)#VS7(s''%S8s&y'S8#;#s'*$C#Gk##B#VS9&s'-%S/s'#'S/#%#s'0$C#$k##s#(#;&s'3%S:s')'S:#%#s'6VS5SVs',$Cs'-GH#;S(s'/1s'0#%S(s'1&$#$CS(#k##(#VS,S(s'5%S;s'6#G#,$s'8($#k##s%<#VS6S;s';,s'<G%S<s'=,s'>##$G($#k##'#VS7S<s'B;S=s'C$C#Gk##:#VS9S=s'F%S0s'G$C#S0k##>#;S0s'J%SWs'KVS>Gs'L=S?#m##s%PUN##GH,Hs'Q($#VS>Gs'^=S?#m##s#LUS/##GP,Ps'c($#?s&t7C#ECs&n#7Cs&y-Cs&v#-C%#?(7C#-Cs&r'-C$#-C)s&{A#S)VS@%#VS@*#@S$#s'`BCN3Cs&rK#3Cs&uNs'a3C$I#)Cs%uQs'`*s'bFDDE#JZSAs'cFDDE#8Cs&4FCs%y#/C#s&x)Cs&tQ#*s'hFDDE#J+s'iFDDE(s&q#)Cs'iMs&q*s'kFDDE#J)Cs&sS*s&}*s'mFDDE#J:s'nFDDE%#)Cs'$Qs'n*s'pFDDE#JZSAs'qFDDE#9Cs'#s'(8Cs(>FCs')#/C#s&|)C&Q#*s'wFDDE#J+s'xFDDE)s'$#)Cs'$Qs'x*s'zFDDE#J+s'{FDDE%s''#+s'|FDDE0s'(#+s'}FDDE6s')#l#%#s'ys'sl#&As($#l#'s#&s('#j#)C#j#*C#j#+C#j#,C#j#4C#k##s#gSB1s(7N&#L$CK#k##&#,Is(F(s$m#k##s$>SB'ON1s(JR&#L$C%#k##'#$CLGk##$#k##+#k##.#k#)C#k#*C#k#+C#k#,C#k#4C#\HOS.LSXS-S%IS(l#(:$#l#5s#Vs#S#l#6s#^s#[#l#7s#cC#l#8s#eC#l#9s#js#g#l#:s#os#l#l#;s#ws#q#l#6s#~s#y#l#<s$,s$$#l#=s$.C#l#>s$2C#l#?s$9s$4#l#@s$@s$;#l#As$Js$B#l#5s$Ts$L#l#Bs$_s$V#XSYCs$eG#$CGs$f&Hs(`%#s(l$C#Gj#$C#>CG#s%as$`Hl#B)(#%s$qs(qWSZs$ss(gs(r>Cs$ms$k%$#&Ps(}'#s(.&#s'2>Cs$ws$t&#Hl#Bs$}s$z#-Cs(*s#hA#S)@S$#s(h:s(eFDDEs&<s%U)Cs%nMs%S*s(gFDDE#J+s(hFDDEs&:s'p#+s(iFDDE&s'q#l#%#s(es(_l#&s%_s(l#l#'*s(o#j#)C#j#*C#j#2S+#(Ks%P#s)9I's))L&#s'F#s'6#k##&#k##(#k#)C#k#*C#k#2S+#YHs&[s&\S%RPl#(.$#l#1s&`s&[#Cs%ts%s>#Cs%ws%ss%P#j#Cs%{#U#HnS4$s'#%#D#=s&pI#%$#3s%~$#E#l#Ds'&S'#l#=s',s')#l#Fs'3s'0#<Ks)IZS2Cs'Zs'D$#Hl#Gs'`s']#US[I#s%g##$s%d($#%&s)G$C#G#s'P(($#('#m#,#j#Hs)Y#j#EC##"). Qed.

Lemma StrObj_block_range : forall LB m a S p A alloc,
  StrObj LB m a S -> sown S = Some (p, A, alloc) -> In (p, A, alloc) LB /\ rblock_range A alloc /\ (a + 24 <= A \/ A + alloc <= a).
Proof.
  intros LB m a [bs o] p A alloc H E; cbn in E; subst o; cbn in H.
  destruct H as (_ & Hin & BR & _ & _ & _ & DJ & _). split; [exact Hin|]. split; [exact BR| exact DJ].
Qed.

End HCW.

