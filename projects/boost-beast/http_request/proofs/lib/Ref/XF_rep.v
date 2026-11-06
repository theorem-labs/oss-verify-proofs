(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface XRep XPRep.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape RBTac RBSafe RBOrder RBKey DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Record elt := mkElt { el_f : Z ; el_name : list byte ; el_value : list byte ; el_pad : list byte ; el_tail : list byte }.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition NodeCells (nd : node) (pad : list byte) : list cell :=
  [C8 (wz (n_par nd)); C8 (wz (n_lft nd)); C8 (wz (n_rgt nd)); C4 (wz (n_col nd)); CB 4 pad].

Definition node_wf (nd : node) : Prop :=
  0 <= n_par nd < 2^64 /\ 0 <= n_lft nd < 2^64 /\ 0 <= n_rgt nd < 2^64 /\ 0 <= n_col nd < 2^32.

Definition NSCells (m : mem) (ns : NS) : Prop :=
  forall a nd, ns !! a = Some nd -> node_wf nd /\ exists pad, rw_cells rsegs m a (NodeCells nd pad).

(* [comment removed for export] *)
Definition LNodeCells (n : lnode) : list cell := [C8 (wz (l_next n)); C8 (wz (l_prev n))].

Definition lnode_wf (n : lnode) : Prop := 0 <= l_next n < 2^64 /\ 0 <= l_prev n < 2^64.

Definition LSCells (m : mem) (ls : LS) : Prop :=
  forall a n, ls !! a = Some n -> lnode_wf n /\ rw_cells rsegs m a (LNodeCells n).

(* [comment removed for export] *)
Definition ValCells (d : elt) : list cell :=
  [C2 (wz (zlength (el_name d) + 2)); C2 (wz (zlength (el_value d))); C2 (wz (el_f d)); CB 2 (el_pad d);
   CB (length (el_name d)) (el_name d); CB 2 [b8 58; b8 32]; CB (length (el_value d)) (el_value d);
   CB 2 [b8 13; b8 10]; CB (length (el_tail d)) (el_tail d)].

Definition EMCells (m : mem) (em : gmap Z elt) : Prop :=
  forall e d, em !! e = Some d -> rw_cells rsegs m (e + 48) (ValCells d).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition esize (d : elt) : Z := 60 + zlength (el_name d) + zlength (el_value d) + zlength (el_tail d).

Definition elt_wf (d : elt) : Prop :=
  zlength (el_name d) + 2 < 2^16 /\ zlength (el_value d) < 2^16 /\ 0 <= el_f d < 2^16.

(* [comment removed for export] *)
Definition em_ok (em : gmap Z elt) : Prop :=
  (forall e d, em !! e = Some d -> 0 < e /\ e mod 8 = 0 /\ e + esize d <= hceil /\ elt_wf d)
  /\ (forall e1 d1 e2 d2, em !! e1 = Some d1 -> em !! e2 = Some d2 -> e1 <> e2 ->
        e1 + esize d1 <= e2 \/ e2 + esize d2 <= e1).

(* [comment removed for export] *)
Definition key_of (em : gmap Z elt) (x : Z) : list Z :=
  match em !! (x - 16) with Some d => zbytes (el_name d) | None => [] end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition TreeR (m : mem) (h : Z) (S : list Z) (ns : NS) (em : gmap Z elt) : Prop :=
  NSCells m ns /\ EMCells m em /\ rb_rep h S ns
  /\ (forall x, x ∈ S -> is_Some (em !! (x - 16)))
  /\ (forall a, is_Some (ns !! a) -> a = h \/ is_Some (em !! (a - 16)))
  /\ em_ok em /\ hceil <= h /\ h + 48 <= 2^64.

(* [comment removed for export] *)
Definition FieldsC (m : mem) (Fa : Z) (S L : list Z) (ns : NS) (ls : LS) (em : gmap Z elt) : Prop :=
  NSCells m ns /\ LSCells m ls /\ EMCells m em
  /\ rb_ok Fa S ns /\ sorted key_lt (key_of em) S /\ dl_ok (Fa + 32) L ls
  /\ (forall x, x ∈ S -> x - 16 ∈ L)                 (* [comment removed for export] *)
  /\ (forall e, e ∈ L <-> is_Some (em !! e))         (* [comment removed for export] *)
  /\ em_ok em
  /\ hceil <= Fa /\ Fa + 48 <= 2^64 /\ Fa mod 8 = 0.

(* [comment removed for export] *)
Definition FieldsOwn (LB : list block) (em : gmap Z elt) : Prop :=
  forall e d, em !! e = Some d ->
    exists p, In (p, e, esize d) LB /\ esize d = elem_block_size (el_name d) (el_value d).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma NodeCells_size : forall nd pad, cells_size (NodeCells nd pad) = 32%nat.
Proof. intros; reflexivity. Qed.
Lemma LNodeCells_size : forall n, cells_size (LNodeCells n) = 16%nat.
Proof. intros; reflexivity. Qed.
Lemma ValCells_size : forall d, Z.of_nat (cells_size (ValCells d)) = esize d - 48.
Proof.
  intros d. unfold ValCells, esize, zlength. cbn [cells_size csize]. lia.
Qed.
Lemma esize_ge : forall d, 60 <= esize d.
Proof. intros d. unfold esize, zlength. lia. Qed.

(* [comment removed for export] *)
Lemma NSCells_of_RBcells : forall m (ns : NS),
  RBcells m (fmap (fun nd => mkRBN (n_par nd) (n_lft nd) (n_rgt nd) (n_col nd)) ns) ->
  (forall a nd, ns !! a = Some nd -> node_wf nd) -> NSCells m ns.
Proof.
  intros m ns H WF a nd L. split; [exact (WF a nd L)|].
  destruct (RBcells_lookup m _ a (mkRBN (n_par nd) (n_lft nd) (n_rgt nd) (n_col nd)) H) as [pad C].
  { rewrite lookup_fmap, L. reflexivity. }
  exists pad. exact C.
Qed.

(* [comment removed for export] *)
Lemma NSCells_lookup : forall m ns a nd, NSCells m ns -> ns !! a = Some nd ->
  exists pad, rw_cells rsegs m a (NodeCells nd pad).
Proof. intros m ns a nd H L. exact (proj2 (H a nd L)). Qed.

Lemma NSCells_wf : forall m ns a nd, NSCells m ns -> ns !! a = Some nd -> node_wf nd.
Proof. intros m ns a nd H L. exact (proj1 (H a nd L)). Qed.

Lemma LSCells_lookup : forall m ls a n, LSCells m ls -> ls !! a = Some n -> rw_cells rsegs m a (LNodeCells n).
Proof. intros m ls a n H L. exact (proj2 (H a n L)). Qed.

Lemma LSCells_wf : forall m ls a n, LSCells m ls -> ls !! a = Some n -> lnode_wf n.
Proof. intros m ls a n H L. exact (proj1 (H a n L)). Qed.

Lemma EMCells_lookup : forall m em e d, EMCells m em -> em !! e = Some d -> rw_cells rsegs m (e + 48) (ValCells d).
Proof. intros m em e d H L. exact (H e d L). Qed.

(* [comment removed for export] *)
Lemma EMCells_node : forall m em x d, EMCells m em -> em !! (x - 16) = Some d -> rw_cells rsegs m (x + 32) (ValCells d).
Proof.
  intros m em x d H L. replace (x + 32) with (x - 16 + 48) by lia. exact (H _ d L).
Qed.

Lemma key_of_node : forall em x d, em !! (x - 16) = Some d -> key_of em x = zbytes (el_name d).
Proof. intros em x d L. unfold key_of. rewrite L. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ValCells_shape : forall d, exists rest,
  ValCells d = C2 (wz (zlength (el_name d) + 2)) :: rest.
Proof. intros d. unfold ValCells. eexists. reflexivity. Qed.

Lemma ValCells_name_bytes : forall m v d, rw_cells rsegs m v (ValCells d) -> bytes_at rsegs m (v + 8) (el_name d).
Proof.
  intros m v d H.
  pose proof H as [[WF _] _]. cbn in WF. destruct WF as (_ & _ & _ & LP & _).
  pose proof (rw_cells_bytes_at _ _ _ _ H) as B. unfold ValCells in B.
  cbn [cells_bytes cbytes] in B.
  apply bytes_at_app in B. destruct B as [_ B]. rewrite length_le2 in B.
  apply bytes_at_app in B. destruct B as [_ B]. rewrite length_le2 in B.
  apply bytes_at_app in B. destruct B as [_ B]. rewrite length_le2 in B.
  apply bytes_at_app in B. destruct B as [_ B]. rewrite LP in B.
  apply bytes_at_app in B. destruct B as [B _].
  replace (v + Z.of_nat 2 + Z.of_nat 2 + Z.of_nat 2 + Z.of_nat 2) with (v + 8) in B by lia. exact B.
Qed.

(* [comment removed for export] *)
Lemma em_ok_range : forall em e d, em_ok em -> em !! e = Some d -> 0 < e /\ e mod 8 = 0 /\ e + esize d <= hceil /\ elt_wf d.
Proof. intros em e d [R _] L. exact (R e d L). Qed.

Lemma em_ok_disj : forall em e1 d1 e2 d2, em_ok em -> em !! e1 = Some d1 -> em !! e2 = Some d2 -> e1 <> e2 ->
  e1 + esize d1 <= e2 \/ e2 + esize d2 <= e1.
Proof. intros em e1 d1 e2 d2 [_ D] L1 L2 NE. exact (D e1 d1 e2 d2 L1 L2 NE). Qed.

(* [comment removed for export] *)
Lemma TreeR_node_cases : forall m h S ns em a nd, TreeR m h S ns em -> ns !! a = Some nd ->
  a = h \/ exists d, em !! (a - 16) = Some d /\ 0 < a - 16 /\ a + 32 <= hceil.
Proof.
  intros m h S ns em a nd (NC & EC & RR & SK & DOM & EOK & HH & HB) L.
  destruct (DOM a) as [E|K]; [rewrite L; eexists; reflexivity| left; exact E|].
  destruct (em !! (a - 16)) as [d|] eqn:Ld; [| exfalso; exact (is_Some_None K)]. right. exists d. split; [reflexivity|].
  pose proof (em_ok_range _ _ _ EOK Ld) as (P & _ & R & _). pose proof (esize_ge d). lia.
Qed.

Lemma TreeR_S_payload : forall m h S ns em x, TreeR m h S ns em -> x ∈ S ->
  exists d, em !! (x - 16) = Some d /\ rw_cells rsegs m (x + 32) (ValCells d) /\ bytes_at rsegs m (x + 40) (el_name d)
            /\ key_of em x = zbytes (el_name d) /\ elt_wf d /\ 0 < x - 16 /\ x - 16 + esize d <= hceil.
Proof.
  intros m h S ns em x (NC & EC & RR & SK & DOM & EOK & HH & HB) IN.
  destruct (em !! (x - 16)) as [d|] eqn:Ld. 2:{ exfalso. pose proof (SK x IN) as K. rewrite Ld in K. exact (is_Some_None K). }
  exists d. split; [reflexivity|].
  pose proof (EMCells_node _ _ _ _ EC Ld) as C. split; [exact C|].
  split. { replace (x + 40) with (x + 32 + 8) by lia. apply ValCells_name_bytes. exact C. }
  split. { apply key_of_node. exact Ld. }
  pose proof (em_ok_range _ _ _ EOK Ld) as (P & _ & R & W). split; [exact W|]. lia.
Qed.

(* [comment removed for export] *)
Lemma NSCells_transport : forall W m m' ns,
  NSCells m ns -> munch W m m' -> wmono rsegs m m' ->
  (forall a nd, ns !! a = Some nd -> disjoint_from W a 32) -> NSCells m' ns.
Proof.
  intros W m m' ns H MU WM D a nd L. destruct (H a nd L) as [WF [pad C]]. split; [exact WF|]. exists pad.
  eapply rw_cells_transport; [exact C| exact MU| exact WM|]. rewrite NodeCells_size. exact (D a nd L).
Qed.

Lemma LSCells_transport : forall W m m' ls,
  LSCells m ls -> munch W m m' -> wmono rsegs m m' ->
  (forall a n, ls !! a = Some n -> disjoint_from W a 16) -> LSCells m' ls.
Proof.
  intros W m m' ls H MU WM D a n L. destruct (H a n L) as [WF C]. split; [exact WF|].
  eapply rw_cells_transport; [exact C| exact MU| exact WM|]. rewrite LNodeCells_size. exact (D a n L).
Qed.

Lemma EMCells_transport : forall W m m' em,
  EMCells m em -> munch W m m' -> wmono rsegs m m' ->
  (forall e d, em !! e = Some d -> disjoint_from W (e + 48) (esize d - 48)) -> EMCells m' em.
Proof.
  intros W m m' em H MU WM D e d L.
  eapply rw_cells_transport; [exact (H e d L)| exact MU| exact WM|]. rewrite ValCells_size. exact (D e d L).
Qed.

(* [comment removed for export] *)
Definition ns_out (ns : NS) (lo hi : Z) : Prop := forall a nd, ns !! a = Some nd -> a + 32 <= lo \/ hi <= a.
Scheme kc__1 := Elimination for Corelib.Init.Datatypes.prod Sort Prop.

Lemma NSCells_transport_out : forall W m m' ns lo hi,
  NSCells m ns -> munch W m m' -> wmono rsegs m m' -> ns_out ns lo hi ->
  Forall (fun iv : Z * Z => lo <= fst iv /\ snd iv <= hi) W -> NSCells m' ns.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.mem); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@stdpp.gmap.gmap); constr:(@Corelib.Numbers.BinNums.Z); constr:(@stdpp.numbers.Z.eq_dec); constr:(@stdpp.countable.Z_countable); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBMem.node); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.HCW.NSCells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RSegs.rsegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.HCW.ns_out); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.HCW.NSCells_transport); constr:(@Corelib.Init.Logic.eq); constr:(@stdpp.base.lookup); constr:(@stdpp.gmap.gmap_lookup); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.I); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@Stdlib.Lists.List.Forall_inv); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.Lists.List.Forall_inv_tail); constr:(@kc__1 (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z))|] [|@iv; @F; @W; @l; @p; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__arith; @K1; @IH; @v; @u; @z; @a0; @K; @L; @nd; @a; @OUT; @WM; @MU; @H; @hi; @lo; @ns; @m'; @m|] "#%K#8$)#D#r#%#$#'###s#q#(#&#<#G#x#y#)#,#/#-#d#A#+#.#1#6#;#?#>#B#E#F#T#]#0#*#4#5#i#e#j#l#z#|#o$&$'#7#C#H#I#J#K#L#N#Q#R#V#U#W#Z#^#2#3#b#m#n#p#t#{#~#}$#$%$($)$*$$$+#c#_#[#S#=#P#O#M#@#\#`#v#u#g#w#X#h#f#Y#a#k3#u%#v%#w&#x$#y&#z&#{'#|*#}%#~%$#%$$$$%&$&%$''$('US+M&S&&#&#&#&#&#US,#US-#US,(US-#US.#k##&#XSACS/S0NVSBGEWSCQKGWSDSEQKWSFKGLVSGCCWSHCCH#Q#WSICCH##K$%#j#$(#%)#RUS.NXSJCS/S0NZSKCN1#FRVSLNHWS1&$#WGEFHUSM=0E###R#S'E-$##S#4#3S($$#j#$8#%9#H'FK,k#%$#j#&s#.##S(<#;S$$$#j#$@#US2M%B$#j#%#SN#S)s###BS3$$#j#$s#'#%s#(#H'FS4;k#%$##SOs#*#s#)S)$$#j#$s#.#(MEF%s#0$#(MLE'#S's#$k#%%#k##,#k#'s#G#j#(s#6##S5s#6#s#5SP$$#j#$s#:#%s#;#H'FS$s#.k#%$##S6s#=#s#<S5$$#j#$s#A#1CCLE(M#F%s#D%##S*s#D#s#CS6$$#j#$s#H#1CCGLYSQs#J$#EHU%$0S#s#>##K#GS#-$#'LS#s#B.S7.#.#.#+C#+C&+C(/C$#/C&#VS8#S9+C*+CS7/C)#/C%#VS8#S9US2S%(S%$#(S%*#US+S%VS:CGUSRC2C$E#VS:CK2C#L%2C%F#USSCUSTC,Cs#|,Cs#~)C$O#*&JDDI#PUS;S&,C#US;s$',C#)C%O#*,JDDI#P[SU-JDDI)#USVD,CS&VSWCs#kWSXC$#)C#O1*3JDDI#P)C,O'*5JDDI#P[S<6JDDI%#)C(O5*8JDDI#P)C3O,*:JDDI#P[S<;JDDI%#\S=<JDDI(0#\S==JDDI21#VSY>IVSZS>S?VS[HEWS1S>#S?m$%#WS\CS]FXS^HE$#l#)*)#l#*s#(s#'#l#+s#0s#/#j#,C#j#-C#j#.C#j#/C#j#0C##LF#EG$$#0Fs$/##G#KF-$##s$2L#GE-$#k##&#k##+#k#,C#k#-C#k#.C#k#/C#k#0C#[HS*S@KQS3FS$l#15$##S@s$L#s$KS*$$#j#$s$P#1CCKGYS_s$R$#LFUE#XS`s#cs#b*#l#2s#is#h#(Ms#kE'#S(s$Im#%#j#%s#s#j#3s#{#j#&s$m#j#4C#j#5C#V#FHj#6C#j#6C#YSaCCs$-#Hj#7M#ZSbMs$Is$B#S)Gl#8s$Ws$R#j#9s$Y#j#:N#j#;C#\ScS$RS'S4GLE#j#%s$b#j#<s$k#j#=s$m#j#>s$o#j#?s$q#j#@C#j#AC#j#Bs$u#j#Cs$w#j#DSd#j#&s%)##"). Qed.

Lemma ns_out_insert : forall ns lo hi a nd, ns_out ns lo hi -> (a + 32 <= lo \/ hi <= a) -> ns_out (<[a := nd]> ns) lo hi.
Proof.
  intros ns lo hi a nd H K b ndb Lb. destruct (Z.eq_dec b a) as [->|NE]; [exact K|].
  rewrite lookup_insert_ne in Lb by (intros E; apply NE; symmetry; exact E). exact (H b ndb Lb).
Qed.

Lemma ns_out_mono : forall ns lo hi lo' hi', ns_out ns lo hi -> lo <= lo' -> hi' <= hi -> ns_out ns lo' hi'.
Proof. intros ns lo hi lo' hi' H H1 H2 a nd L. destruct (H a nd L); lia. Qed.

(* [comment removed for export] *)
Definition stackW (SP : Z) (W : list (Z * Z)) : Prop :=
  Forall (fun iv : Z * Z => hceil <= fst iv /\ snd iv <= SP) W.

Lemma stackW_disjoint_low : forall SP W a n, stackW SP W -> a + n <= hceil -> disjoint_from W a n.
Proof.
  intros SP W a n F LE. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
  pose proof (Forall_inv F) as K. cbn in K. split; [lia| apply IH; exact (Forall_inv_tail F)].
Qed.

Lemma stackW_disjoint_high : forall SP W a n, stackW SP W -> SP <= a -> disjoint_from W a n.
Proof.
  intros SP W a n F LE. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
  pose proof (Forall_inv F) as K. cbn in K. split; [lia| apply IH; exact (Forall_inv_tail F)].
Qed.

Lemma TreeR_transport : forall SP W m m' h S ns em,
  TreeR m h S ns em -> munch W m m' -> wmono rsegs m m' -> stackW SP W -> SP <= h -> TreeR m' h S ns em.
Proof.
  intros SP W m m' h S ns em TR MU WM SW LE.
  pose proof TR as (NC & EC & RR & SK & DOM & EOK & HH & HB).
  split.
  { eapply NSCells_transport; [exact NC| exact MU| exact WM|]. intros a nd L.
    destruct (TreeR_node_cases _ _ _ _ _ _ _ TR L) as [->|(d & Ld & P & R)].
    - eapply stackW_disjoint_high; [exact SW| exact LE].
    - eapply stackW_disjoint_low; [exact SW| exact R]. }
  split.
  { eapply EMCells_transport; [exact EC| exact MU| exact WM|]. intros e d L.
    pose proof (em_ok_range _ _ _ EOK L) as (P & _ & R & _). eapply stackW_disjoint_low; [exact SW| lia]. }
  split; [exact RR|]. split; [exact SK|]. split; [exact DOM|]. split; [exact EOK|]. split; [exact HH| exact HB].
Qed.

Lemma FieldsC_transport : forall SP W m m' Fa S L ns ls em,
  FieldsC m Fa S L ns ls em -> munch W m m' -> wmono rsegs m m' -> stackW SP W -> SP <= Fa ->
  FieldsC m' Fa S L ns ls em.
Proof.
  intros SP W m m' Fa S L ns ls em FC MU WM SW LE.
  pose proof FC as (NC & LC & EC & OK & SO & DL & SL & LE' & EOK & HH & HB & AL).
  split.
  { eapply NSCells_transport; [exact NC| exact MU| exact WM|]. intros a nd La.
    pose proof (rb_ok_dom _ _ _ a OK) as Da.
    assert (K : a = Fa \/ a ∈ S). { apply Da. rewrite La. eexists; reflexivity. }
    destruct K as [->|IN].
    - eapply stackW_disjoint_high; [exact SW| exact LE].
    - pose proof (SL a IN) as INL. apply LE' in INL. destruct (em !! (a - 16)) as [d|] eqn:Ld; [| exfalso; exact (is_Some_None INL)].
      pose proof (em_ok_range _ _ _ EOK Ld) as (P & _ & R & _). pose proof (esize_ge d).
      eapply stackW_disjoint_low; [exact SW| lia]. }
  split.
  { eapply LSCells_transport; [exact LC| exact MU| exact WM|]. intros a n La.
    destruct DL as (ND & DOM & NXT).
    assert (K : a ∈ Fa + 32 :: L). { apply DOM. rewrite La. eexists; reflexivity. }
    rewrite elem_of_cons in K. destruct K as [->|IN].
    - eapply stackW_disjoint_high; [exact SW| lia].
    - apply LE' in IN. destruct (em !! a) as [d|] eqn:Ld; [| exfalso; exact (is_Some_None IN)].
      pose proof (em_ok_range _ _ _ EOK Ld) as (P & _ & R & _). pose proof (esize_ge d).
      eapply stackW_disjoint_low; [exact SW| lia]. }
  split.
  { eapply EMCells_transport; [exact EC| exact MU| exact WM|]. intros e d Ld.
    pose proof (em_ok_range _ _ _ EOK Ld) as (P & _ & R & _). eapply stackW_disjoint_low; [exact SW| lia]. }
  split; [exact OK|]. split; [exact SO|]. split; [exact DL|]. split; [exact SL|]. split; [exact LE'|].
  split; [exact EOK|]. split; [exact HH|]. split; [exact HB| exact AL].
Qed.

Lemma TreeR_ns_out : forall m h S ns em lo hi, TreeR m h S ns em -> hceil <= lo -> hi <= h -> ns_out ns lo hi.
Proof.
  intros m h S ns em lo hi TR LO HI a nd L.
  destruct (TreeR_node_cases _ _ _ _ _ _ _ TR L) as [->|(d & Ld & P & R)]; lia.
Qed.

(* [comment removed for export] *)
Lemma FieldsC_TreeR : forall m Fa S L ns ls em, FieldsC m Fa S L ns ls em -> TreeR m Fa S ns em.
Proof.
  intros m Fa S L ns ls em (NC & LC & EC & OK & SO & DL & SL & LE & EOK & HH & HB & AL).
  split; [exact NC|]. split; [exact EC|]. split; [apply rb_ok_rep; exact OK|].
  split. { intros x IN. apply LE. apply SL. exact IN. }
  split. { intros a Ha. destruct (proj1 (rb_ok_dom _ _ _ a OK) Ha) as [E|IN].
           { left; exact E. } { right. apply LE. apply SL. exact IN. } }
  split; [exact EOK|]. split; [exact HH| exact HB].
Qed.

Lemma FieldsC_sorted : forall m Fa S L ns ls em, FieldsC m Fa S L ns ls em -> sorted key_lt (key_of em) S.
Proof. intros m Fa S L ns ls em FC. exact (proj1 (proj2 (proj2 (proj2 (proj2 FC))))). Qed.

Lemma FieldsC_rb_ok : forall m Fa S L ns ls em, FieldsC m Fa S L ns ls em -> rb_ok Fa S ns.
Proof. intros m Fa S L ns ls em FC. exact (proj1 (proj2 (proj2 (proj2 FC)))). Qed.

Lemma FieldsC_dl_ok : forall m Fa S L ns ls em, FieldsC m Fa S L ns ls em -> dl_ok (Fa + 32) L ls.
Proof. intros m Fa S L ns ls em FC. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 FC)))))). Qed.

Lemma FieldsC_S_L : forall m Fa S L ns ls em, FieldsC m Fa S L ns ls em -> forall x, x ∈ S -> x - 16 ∈ L.
Proof. intros m Fa S L ns ls em FC. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 FC))))))). Qed.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.False Sort Prop.

(* [comment removed for export] *)
Lemma FieldsC_empty : forall m Fa pad,
  rw_cells rsegs m Fa (NodeCells (init_header_node Fa) pad) ->
  rw_cells rsegs m (Fa + 32) (LNodeCells (init_lheader_node (Fa + 32))) ->
  hceil <= Fa -> Fa + 48 <= 2^64 -> Fa mod 8 = 0 ->
  FieldsC m Fa [] [] {[ Fa := init_header_node Fa ]} {[ Fa + 32 := init_lheader_node (Fa + 32) ]} ∅.
Proof.
  ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RSegs.rsegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.HCW.NodeCells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBMem.init_header_node); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.HCW.LNodeCells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBMem.init_lheader_node); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(HCEIL); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil_range); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.HCW.NSCells); constr:(@stdpp.base.singletonM); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBMem.node); constr:(@stdpp.gmap.gmap); constr:(@stdpp.numbers.Z.eq_dec); constr:(@stdpp.countable.Z_countable); constr:(@stdpp.fin_maps.map_singleton); constr:(@stdpp.gmap.gmap_partial_alter); constr:(@stdpp.gmap.gmap_empty); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.HCW.LSCells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBMem.lnode); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.HCW.EMCells); constr:(@stdpp.base.empty); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.elt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBShape.rb_ok); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBOrder.sorted); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBKey.key_lt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.HCW.key_of); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.DList.dl_ok); constr:(@stdpp.base.elem_of); constr:(@stdpp.base.list_elem_of); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Corelib.Init.Logic.iff); constr:(@stdpp.base.is_Some); constr:(@stdpp.base.lookup); constr:(@stdpp.gmap.gmap_lookup); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.HCW.em_ok); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Classes.Morphisms.iff_impl_subrelation); constr:(@stdpp.fin_maps.lookup_singleton_Some); constr:(@stdpp.gmap.gmap_fmap); constr:(@stdpp.gmap.gmap_omap); constr:(@stdpp.gmap.gmap_merge); constr:(@stdpp.gmap.gmap_fold); constr:(@stdpp.gmap.gmap_finmap); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.HCW.node_wf); constr:(@Corelib.Init.Logic.ex); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.X); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBMem.RED); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBMem.n_par); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBMem.n_lft); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBMem.n_rgt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBMem.n_col); constr:(@Corelib.Init.Logic.ex_intro); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.HCW.lnode_wf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBMem.l_next); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBMem.l_prev); constr:(@stdpp.fin_maps.lookup_empty); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Logic.False_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.HCW.ValCells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBShape.rb_ok_empty); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.DList.dl_ok_empty); constr:(@stdpp.list_basics.list.elem_of_nil); constr:(@kc__3); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.iff_Transitive); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@stdpp.option.is_Some_None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.HCW.esize); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.HCW.elt_wf); constr:(@Corelib.Init.Logic.not); constr:(@Corelib.Init.Logic.or)|] [|@x; @e; @lemma; @pad; @a; @nd; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__p1; @__arith; @__sat3; @__sat1; @__sat0; @__sat2; @__sat4; @H; @L; @n; @o; @e0; @d; @IN; @K; @d2; @e2; @d1; @e1; @H1; @H0; @HCEILB; @AL; @HB; @HH; @HL; @HN; @Fa; @m|] "#+@#;$h#C$;###T$<$:#e#$#%#\#Z#b#&#]$Y#*#'$C#F#;#(#)#+#0#2#3$A#-#1#4$'$-#,#.#/$H#A#_#5$Z#>#O#Q#^#g#n#[#r#`#v$$$%$($)$2$.$3$B$E$F$G$K$L$O#|#B$_$^$a$b#o$i$j$k#N#U#X#a#d#c#f#j#h#i#k#m#s#w#x#y#z#{$+$*$5$6$4$7$9$D$I$M$N$J#:#6$P$Q$R$S$T#7$V$W$\$]$`$e$c$d$g$f#@#V#R#M#P#I$&#W#q$?$>#E#t$8#H$=#J#L#Y$##S#G#K#l$@#p#}#~$0$U$h#?#D#u$1$/$,$X$[O$A$$B%$C&$D%$E$$F%$G%$H'$I)$J'$K*$L'$M%$N+$O$$P*$Q$$R$$S)$T)$U%#i%$V%$W$$X($Y%#d$$Z%$[$$\%$]%$^$$_$$`$$a$#Q'#S'#R'$b&$c$$d&$e&$f0$g%#S7##########D#US;#D(US;#=#k##&#E%1J9#E.S%KJ#3.(K#4#:#.S%O%#US]S<&#O'S7########3#(S##3@3<VS=$#&&#3B7S'#%C#FUS^S<'1'#'#'#'#'#'#'#'#'#'#'#'###'#'#'#'#'#'#'#'###############################################3#&#s#A's#%'#'#'#'#'#'#'#'###############################################3#&s#c#$s#%#m#s#U#FCLPMXS8CLPMGCLPMYS>CM%$#1R5CM'$R#VS_S)#FCLPNXS8CLPNGCLPNYS>CN%$#(Rs#v4#5CN(%$#VS`S)#FCLPIGCLPIVSa$#VSbS)#US?CWScR#1ECUSd'XSe$Sf#&WSg/'-UShC;C'#E)3s$7VS@J#;C*&#,k##&#k#$C#HCLPI+CI4#E2>I#8+#k#%C#USi6&s$0R(Rs$*&#s$'7Rs$&%C#F$%#$(#$*#$,#$2#$:#$<#$@#$s###$s#(#=MHCLPM1S35CMs#:s#7S3#+CMs#;%J#/ME%($#1S.5CMs#?s#<S.#m##s#@+CMs#A+K#/MJ%.$#%CS.K%M)J$$#8&#1S45CMs#Is#FS4#+CMs#J4O#/MK%7$#%CS4O%M(K$$#I&#Ej#&,#WSACLPWSjCLPWSBCLPWSCCLPWS8CLPWSkCLPWSlCLPWSmCLPWSnCLPdSDC+*)('&%$L#MS.K?JV-#E?O9S#E.S%S/S'#j#'s$q#@s$r#$'#j##6#1S5%M#O%CS*S'1S+%M#S(?R9S)E.S%S9K#j#'s$}#@s$~#$'#k##)#j#(C#1S/%M#S'?E9JE.S%S9S0#j#'s%+#@s%,#$'#j#)M#?51S,9#E.S%S0S,#j#'s%3#@s%4#VSES+s${&FS+&Fs$}7S0s$~&F#k##%#k##'#VSFs%*s%8)Fs%+&Fs%:VS=s%-s%;)F#k##%#k##'#&Fs%1WSGs%2s%@Jj##S1#j#*%#&F*k##S1#k#*(#VSFs%8s%7&Fs%8)Fs%8k##$#k##3#WSGs%=s%<Jj##S1#j#*0#&Fs%>k##S1#k#*3#VSoFs%CVSHSp#m##<UJ#US#$JSIJ#J#AC#AC&ACSIKC$#KC&#VSJ#SKUS?S2LS2$#LS2%#ES2VSqCKUSrCXSsC$J#UStCUSuC<Cs%%VSLCs%y,C$S-#-&HDDG#S$ZSv'HDDGS#2(HDDG$#USMDVSLCS7<Cs%dWSNC$#<Cs%dWSOC#s%},C%S-#-0HDDG#S$,C/S-)-2HDDG#S$<CF,C#S-#-5HDDG#S$,C%S6*-7HDDG#S$28HDDG%#,C(S-1-:HDDG#S$,C3S6/-<HDDG#S$2=HDDG%#Ds&3WSOC4#,C/S6#-AHDDG#S$2BHDDG/#2s##HDDG(#2s#$HDDG)#2s#%HDDG/#0s#&HDDG6?#0s#'HDDG9@#0s#(HDDGBA#VSws#)GVSHSPSQVSxEK%SP#SQm$%#WSyCFJXSzEK$#l#+*)#l#,s#3s#2#l#-s#8s#7#j#.C#j#/C#j#0S&#&s%XJ$#K(Js&5&#s&2&OK&FF$#s#[&FO)Os&7$$#$'s#k$$#$%#$)#k##,#k##.#k##1#k#.C#k#/C#k#0S&#ZEs%Is&NS{S,S9S|l#18$#l#2s#^s#v#l#3s#`s#k#l#4s#hs#e#l#3s#ps#l#l#5s#us#r#l#2s$$s#z#l#6s$,s$&#)S+s&L$s$-#&FSR)SRs$&$$#$&#$'#$@#m#+#US}s$O&F#)$s&W$$#US~s$S&F#)$s&[$$#UT#s$W&F#)$s&_$$#UT$s$[&F#)$s$:$$#$'#$,#$1#m#6#m##s$PXT%s&~s$MS/S**s$Rs$M$#6Ms$fs$T#S(Ej#7s$\#6CS/s$_#S(Ej#7s$j#V#JEj##s$m#j##s%*#YSSs%+s%*s$q#El#8s$ys%3#j#8s%=#j#)M#j#(C#m##s%u=NHCLPN(S3s'/4#5CNs%ys%v$#+CNs%z&J#/NE%)$#(S.s'54#5CNs&#s%|$#m##s&$+CNs&%-K#/NJ%0$#%C)K%N)J$$#8&#(S4s'@4#5CNs&.s&+$#+CNs&/7O#/NK%:$#%C(O%N(K$$#I&#Ej#&-#dSDCs%Js%Is%Hs%Gs%Fs%Es%Ds%CLs%BN8K7JV$#EBO:O.S%S*S##$%#j##+#(S5s'R4#%N#O(S*s'U%C#S'(S/s'W(S+s'X4#%N#S(BR:R.S%S0J#$%#k##'#j#(C#4,%N#S'BE(S,s'd:E.S%S0$#$&#j#9N#B2:3.S%S,5#<Cs'lWSNCs$\#,Cs$TS-#-s$fHDDG#S$,C%S6s$[-s$hHDDG#S$2s$iHDDG%#2s$jHDDG##0s$kHDDGs$[s$d#0s$lHDDGs$^s$e#0s$mHDDGs$gs$f#l#+#s$Gs$Al#,s$qs$p#l#-s$vs$u#j#.C#j#/C#j#0S&#(Os'}&F#)$s'o$$#$##k##s$A#k##s$C#k##s$F#k#.C#k#/C#k#0S&#ZEs&~s('T&S*S+S,l#1/$#l#3s%8s%C#l#4s%@s%=#l#3s%Hs%D#l#5s%^s%X#UT's#7&F#)$s($$$#UT(s#;&F#)$s(($$#$'#m#,#m##s#1*s#2s#0#S56Ns#Cs#4#S(Ej#7s#;#6Cs#Gs#>#S(Ej#7s#I#V#JEj##s#M#j##s#\#YSSs#]s#\s#R#El#8s#Xs#f#j#8s#q#j#9N#j#(C#m##s'/=I+CIs'0s&{Js'./IE%%$#+CIs'3s&~Ks'1/IK%(E#j#:)#USMIMCs&Ss&Rs&Qs&Ps&Os&Ns&Ms&LLs&KIK6,(%E$#/IJ%.&#nST$I$#:S&E#%$##Q#S1j#;0#61)#S:,EUT)O.S%S*s(O#N#El#7&Q#l#8,*#j#84#j#<I#j#%C#m##s'DVSERs(R&FR7S3s(T&F#k##s&7#k##&#ACs%qKC#s%mVSJ#SKLS2#s%l,Cs%]SUs%T-s%fHDDG#S$ZSVs%gHDDG#0s%hHDDGs%Xs%a#0s%iHDDGs%cs%b#l#+#s%Cs%=l#,s%ms%l#l#-*s%q#j#.C#j#/C#j#0S&#&KJ%CKFk###Qk##%#k##s%?#k#.C#k#/C#k#0S&#YEs'ws(|S5S'S)l#1,$#l#3s&1s&<#l#4s&9s&6#l#3s&As&=#l#5s#$?#VT*R#,Cs#ySUs%n-s&$HDDG#S$ZSVs&%HDDG#0s&&HDDGs%rs%{#0s&'HDDGs%}s%|#l#+#s%]s%Wl#,s&+s&*#l#-s#$s&/#j#.C#j#/C#j#0S&#%Cs)6Fk###Qk##>#k##s%X#k#.C#k#/C#k#0S&#l#1*#;l#3s&Is&T#l#4s&Qs&N#l#3s&Ys&U#l#5s#<s#7#VT+s(+#;Cs'~s'zJs($8#Q;Cs($s'|Ks(&I#QEj#&%#VSWCJV$#EVS@Os(#;Cs(*s(&#s(,j##Q#VSX#El#='Q#j#=s()#j#$C#8s(+Q>Is#eVT,S&#]T-S&SYT.3QE$$#j#&&#VSWCE>IE8Q#j#:s#m#>Is#fk##Q#k##$Qj##Q%VSX#Ej#7Q#VT/IEj#>)#*)(%#MCs'cs'bs'as'`s'_s'^s']s'\Ls'[IEZT0s#xs#p-$s(7#V21#j#%C#)FK7Ks)W%C#FCJ(K#&#s)hUSZJ$$#$(#$+#k##s$&#k#<I#k#%C#+CIs(Ys(HOs(W%s$-#s$(%s$.s$*s$#%CS'OUS[#CS'(S(#&#S#CO(S##&#S(VS\&#k##*#k##-#k##/#k#?I#k#@C#k#AI#k#BC#)FS#7S#s)w%C#F&/s**USZO$$#$&#$)#N#El#7s$9Q#l#8s$?s$=#j#8s$G#j#<I#j#%C#+CIs(zs(iS#s(x/IS#%s$OE#j#:s$P#MCs(=s(<s(;s(:s(9s(8s(7s(6Ls(5IS#6s$R'$Es$J#/IO%s$Ts$L#%CS(S#US[#+CIs)(s(sS's)&j#%s$Xs$K6s$Y$#S:-JCR(S)#&#S(&s#-S)VS\$#N#El#C)Q#j#D-#j#7s#7#l#831#j#8s#9#j#?I#j#@C#j#AI#j#BC#*s#@s#-?#*s(~s(|KJ*s)%s(|O#*s)'s(|%#*s))s(|s#Q#*s)/s(|s#h#*s)7s(|s#w#*s)9s(|S:#*s)=s(|s$5#*s)@s(|s$Z#*s)Es(|s$t#*s)Ns(|s&7#l#Es)Vs)W#j#Fs*O#j#Gs*S#j#Hs*_#j#Is*b#j#Js*h#j#'s*l#j#KC#j#Ls*o##"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ns_sep (ns : NS) : Prop :=
  forall a b nda ndb, ns !! a = Some nda -> ns !! b = Some ndb -> a <> b -> a + 32 <= b \/ b + 32 <= a.
Definition ls_sep (ls : LS) : Prop :=
  forall a b na nb, ls !! a = Some na -> ls !! b = Some nb -> a <> b -> a + 16 <= b \/ b + 16 <= a.

Lemma disjoint_from_single : forall lo hi a n, (a + n <= lo \/ hi <= a) -> disjoint_from [(lo, hi)] a n.
Proof. intros lo hi a n H. cbn. split; [exact H| exact I]. Qed.

Lemma NSCells_update : forall W m m' ns a nd nd' pad',
  NSCells m ns -> ns !! a = Some nd ->
  munch W m m' -> wmono rsegs m m' ->
  (forall b ndb, ns !! b = Some ndb -> b <> a -> disjoint_from W b 32) ->
  node_wf nd' -> rw_cells rsegs m' a (NodeCells nd' pad') ->
  NSCells m' (<[ a := nd' ]> ns).
Proof.
  intros W m m' ns a nd nd' pad' H L MU WM D WF' C b ndb Lb.
  destruct (Z.eq_dec b a) as [->|NE].
  - rewrite lookup_insert_eq in Lb. injection Lb as <-. split; [exact WF'| exists pad'; exact C].
  - rewrite lookup_insert_ne in Lb by (intros E; apply NE; symmetry; exact E).
    destruct (H b ndb Lb) as [WF [pad Cb]]. split; [exact WF|]. exists pad.
    eapply rw_cells_transport; [exact Cb| exact MU| exact WM|]. rewrite NodeCells_size. exact (D b ndb Lb NE).
Qed.

(* [comment removed for export] *)
Lemma NSCells_update_node : forall m m' ns a nd nd' pad' k n,
  NSCells m ns -> ns_sep ns -> ns !! a = Some nd ->
  munch [(a + k, a + k + n)] m m' -> wmono rsegs m m' -> 0 <= k -> k + n <= 32 ->
  node_wf nd' -> rw_cells rsegs m' a (NodeCells nd' pad') ->
  NSCells m' (<[ a := nd' ]> ns).
Proof.
  intros m m' ns a nd nd' pad' k n H SEP L MU WM K1 K2 WF' C.
  eapply NSCells_update; [exact H| exact L| exact MU| exact WM| | exact WF'| exact C].
  intros b ndb Lb NE. apply disjoint_from_single. destruct (SEP a b nd ndb L Lb ltac:(intros E; apply NE; symmetry; exact E)); lia.
Qed.

(* [comment removed for export] *)
Lemma NSCells_add : forall m ns a nd pad,
  NSCells m ns -> node_wf nd -> rw_cells rsegs m a (NodeCells nd pad) -> NSCells m (<[ a := nd ]> ns).
Proof.
  intros m ns a nd pad H WF C b ndb Lb. destruct (Z.eq_dec b a) as [->|NE].
  - rewrite lookup_insert_eq in Lb. injection Lb as <-. split; [exact WF| exists pad; exact C].
  - rewrite lookup_insert_ne in Lb by (intros E; apply NE; symmetry; exact E). exact (H b ndb Lb).
Qed.

Lemma LSCells_update : forall W m m' ls a n n',
  LSCells m ls -> ls !! a = Some n ->
  munch W m m' -> wmono rsegs m m' ->
  (forall b nb, ls !! b = Some nb -> b <> a -> disjoint_from W b 16) ->
  lnode_wf n' -> rw_cells rsegs m' a (LNodeCells n') ->
  LSCells m' (<[ a := n' ]> ls).
Proof.
  intros W m m' ls a n n' H L MU WM D WF' C b nb Lb.
  destruct (Z.eq_dec b a) as [->|NE].
  - rewrite lookup_insert_eq in Lb. injection Lb as <-. split; [exact WF'| exact C].
  - rewrite lookup_insert_ne in Lb by (intros E; apply NE; symmetry; exact E).
    destruct (H b nb Lb) as [WF Cb]. split; [exact WF|].
    eapply rw_cells_transport; [exact Cb| exact MU| exact WM|]. rewrite LNodeCells_size. exact (D b nb Lb NE).
Qed.

Lemma LSCells_update_node : forall m m' ls a n n' k w,
  LSCells m ls -> ls_sep ls -> ls !! a = Some n ->
  munch [(a + k, a + k + w)] m m' -> wmono rsegs m m' -> 0 <= k -> k + w <= 16 ->
  lnode_wf n' -> rw_cells rsegs m' a (LNodeCells n') ->
  LSCells m' (<[ a := n' ]> ls).
Proof.
  intros m m' ls a n n' k w H SEP L MU WM K1 K2 WF' C.
  eapply LSCells_update; [exact H| exact L| exact MU| exact WM| | exact WF'| exact C].
  intros b nb Lb NE. apply disjoint_from_single. destruct (SEP a b n nb L Lb ltac:(intros E; apply NE; symmetry; exact E)); lia.
Qed.

Lemma LSCells_add : forall m ls a n,
  LSCells m ls -> lnode_wf n -> rw_cells rsegs m a (LNodeCells n) -> LSCells m (<[ a := n ]> ls).
Proof.
  intros m ls a n H WF C b nb Lb. destruct (Z.eq_dec b a) as [->|NE].
  - rewrite lookup_insert_eq in Lb. injection Lb as <-. split; [exact WF| exact C].
  - rewrite lookup_insert_ne in Lb by (intros E; apply NE; symmetry; exact E). exact (H b nb Lb).
Qed.

Lemma EMCells_add : forall m em e d,
  EMCells m em -> rw_cells rsegs m (e + 48) (ValCells d) -> EMCells m (<[ e := d ]> em).
Proof.
  intros m em e d H C b db Lb. destruct (Z.eq_dec b e) as [->|NE].
  - rewrite lookup_insert_eq in Lb. injection Lb as <-. exact C.
  - rewrite lookup_insert_ne in Lb by (intros E; apply NE; symmetry; exact E). exact (H b db Lb).
Qed.

(* [comment removed for export] *)
Lemma FieldsC_node_cases : forall m Fa S L ns ls em a nd, FieldsC m Fa S L ns ls em -> ns !! a = Some nd ->
  a = Fa \/ exists d, em !! (a - 16) = Some d /\ a - 16 ∈ L /\ 0 < a - 16 /\ (a - 16) mod 8 = 0 /\ a - 16 + esize d <= hceil.
Proof.
  intros m Fa S L ns ls em a nd (NC & LC & EC & OK & SO & DL & SL & LE & EOK & HH & HB & AL) La.
  destruct (proj1 (rb_ok_dom _ _ _ a OK)) as [E|IN]; [rewrite La; eexists; reflexivity| left; exact E|].
  right. pose proof (SL a IN) as INL. pose proof (proj1 (LE _) INL) as K.
  destruct (em !! (a - 16)) as [d|] eqn:Ld; [| exfalso; exact (is_Some_None K)].
  exists d. split; [reflexivity|]. split; [exact INL|]. pose proof (em_ok_range _ _ _ EOK Ld) as (P & Q & R & _). lia.
Qed.

Lemma FieldsC_lnode_cases : forall m Fa S L ns ls em a n, FieldsC m Fa S L ns ls em -> ls !! a = Some n ->
  a = Fa + 32 \/ exists d, em !! a = Some d /\ a ∈ L /\ 0 < a /\ a mod 8 = 0 /\ a + esize d <= hceil.
Proof.
  intros m Fa S L ns ls em a n (NC & LC & EC & OK & SO & DL & SL & LE & EOK & HH & HB & AL) La.
  destruct DL as (ND & DOM & NXT).
  assert (K : a ∈ Fa + 32 :: L). { apply DOM. rewrite La. eexists; reflexivity. }
  rewrite elem_of_cons in K. destruct K as [E|IN]; [left; exact E| right].
  pose proof (proj1 (LE _) IN) as K. destruct (em !! a) as [d|] eqn:Ld; [| exfalso; exact (is_Some_None K)].
  exists d. split; [reflexivity|]. split; [exact IN|]. pose proof (em_ok_range _ _ _ EOK Ld) as (P & Q & R & _). lia.
Qed.

Lemma FieldsC_ns_sep : forall m Fa S L ns ls em, FieldsC m Fa S L ns ls em -> ns_sep ns.
Proof.
  intros m Fa S L ns ls em FC a b nda ndb La Lb NE.
  pose proof FC as (NC & LC & EC & OK & SO & DL & SL & LE & EOK & HH & HB & AL).
  destruct (FieldsC_node_cases _ _ _ _ _ _ _ _ _ FC La) as [->|(da & Lda & _ & Pa & _ & Ra)];
  destruct (FieldsC_node_cases _ _ _ _ _ _ _ _ _ FC Lb) as [->|(db & Ldb & _ & Pb & _ & Rb)].
  - exfalso. exact (NE eq_refl).
  - pose proof (esize_ge db). lia.
  - pose proof (esize_ge da). lia.
  - pose proof (esize_ge da). pose proof (esize_ge db).
    destruct (em_ok_disj _ _ _ _ _ EOK Lda Ldb ltac:(intros E; apply NE; lia)); lia.
Qed.

Lemma FieldsC_ls_sep : forall m Fa S L ns ls em, FieldsC m Fa S L ns ls em -> ls_sep ls.
Proof.
  intros m Fa S L ns ls em FC a b na nb La Lb NE.
  pose proof FC as (NC & LC & EC & OK & SO & DL & SL & LE & EOK & HH & HB & AL).
  destruct (FieldsC_lnode_cases _ _ _ _ _ _ _ _ _ FC La) as [->|(da & Lda & _ & Pa & _ & Ra)];
  destruct (FieldsC_lnode_cases _ _ _ _ _ _ _ _ _ FC Lb) as [->|(db & Ldb & _ & Pb & _ & Rb)].
  - exfalso. exact (NE eq_refl).
  - pose proof (esize_ge db). lia.
  - pose proof (esize_ge da). lia.
  - pose proof (esize_ge da). pose proof (esize_ge db).
    destruct (em_ok_disj _ _ _ _ _ EOK Lda Ldb NE); lia.
Qed.

(* [comment removed for export] *)
Lemma FieldsC_node_lnode_disj : forall m Fa S L ns ls em a nd b n,
  FieldsC m Fa S L ns ls em -> ns !! a = Some nd -> ls !! b = Some n -> a + 32 <= b \/ b + 16 <= a.
Proof.
  intros m Fa S L ns ls em a nd b n FC La Lb.
  pose proof FC as (NC & LC & EC & OK & SO & DL & SL & LE & EOK & HH & HB & AL).
  destruct (FieldsC_node_cases _ _ _ _ _ _ _ _ _ FC La) as [->|(da & Lda & _ & Pa & _ & Ra)];
  destruct (FieldsC_lnode_cases _ _ _ _ _ _ _ _ _ FC Lb) as [->|(db & Ldb & _ & Pb & _ & Rb)].
  - lia.
  - pose proof (esize_ge db). lia.
  - pose proof (esize_ge da). lia.
  - pose proof (esize_ge da). pose proof (esize_ge db).
    destruct (Z.eq_dec (a - 16) b) as [E|NE]; [lia|].
    destruct (em_ok_disj _ _ _ _ _ EOK Lda Ldb NE); lia.
Qed.

Lemma FieldsC_node_payload_disj : forall m Fa S L ns ls em a nd e d,
  FieldsC m Fa S L ns ls em -> ns !! a = Some nd -> em !! e = Some d -> a + 32 <= e + 48 \/ e + esize d <= a.
Proof.
  intros m Fa S L ns ls em a nd e d FC La Le.
  pose proof FC as (NC & LC & EC & OK & SO & DL & SL & LE & EOK & HH & HB & AL).
  pose proof (em_ok_range _ _ _ EOK Le) as (Pe & _ & Re & _). pose proof (esize_ge d).
  destruct (FieldsC_node_cases _ _ _ _ _ _ _ _ _ FC La) as [->|(da & Lda & _ & Pa & _ & Ra)]; [lia|].
  destruct (Z.eq_dec (a - 16) e) as [E|NE]; [lia|]. pose proof (esize_ge da).
  destruct (em_ok_disj _ _ _ _ _ EOK Lda Le NE); lia.
Qed.

Lemma FieldsC_lnode_payload_disj : forall m Fa S L ns ls em b n e d,
  FieldsC m Fa S L ns ls em -> ls !! b = Some n -> em !! e = Some d -> b + 16 <= e + 48 \/ e + esize d <= b.
Proof.
  intros m Fa S L ns ls em b n e d FC Lb Le.
  pose proof FC as (NC & LC & EC & OK & SO & DL & SL & LE & EOK & HH & HB & AL).
  pose proof (em_ok_range _ _ _ EOK Le) as (Pe & _ & Re & _). pose proof (esize_ge d).
  destruct (FieldsC_lnode_cases _ _ _ _ _ _ _ _ _ FC Lb) as [->|(db & Ldb & _ & Pb & _ & Rb)]; [lia|].
  destruct (Z.eq_dec b e) as [E|NE]; [lia|]. pose proof (esize_ge db).
  destruct (em_ok_disj _ _ _ _ _ EOK Ldb Le NE); lia.
Qed.

End HCW.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_le_to_Z_bound : forall bs : list byte, 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  rewrite lor_shiftl8_add by lia.
  replace (8 * Z.of_nat (S (length bs))) with (8 + 8 * Z.of_nat (length bs)) by lia.
  rewrite Z.pow_add_r by lia. change (2^8) with 256. nia.
Qed.

Lemma Z_to_le_bytes_of_bytes : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@LinuxProcessSemantics.LinuxProcessSem.BvBase.Z_to_le_bytes); constr:(@Corelib.Init.Datatypes.length); constr:(@LinuxProcessSemantics.LinuxProcessSem.BvBase.bytes_le_to_Z); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.nil); constr:(@stdpp.bitvector.definitions.bv_unsigned_in_range); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@stdpp.bitvector.definitions.bv_modulus); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.bytes_le_to_Z_bound); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@kc__2); constr:(@Corelib.Init.Datatypes.cons); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Stdlib.ZArith.BinInt.Z.lor); constr:(@Stdlib.ZArith.BinInt.Z.shiftl); constr:(@Stdlib.ZArith.BinInt.Z.shiftr); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@stdpp.tactics.f_equal_help); constr:(@Corelib.Numbers.BinNums.N); constr:(@stdpp.bitvector.definitions.bv_eq); constr:(@stdpp.bitvector.definitions.bv_wrap); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@stdpp.bitvector.definitions.Z_to_bv_unsigned); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.ZArith.BinInt.Z.shiftr_div_pow2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Bytes.lor_shiftl8_add)|] [|@bs; @z; @b2; @b1; @n; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__arith; @H0; @r; @q; @H3; @H2; @H1; @H; @_H; @B0; @Hb; @IH; @b|] "#(5#6$8#X#|#}#{###%#H#$#&$(#'#+#(#,#h$&#=#*#R#t$)$,#)#1#9#D#U#T#Q#[#-#^#b#.#c#/#d#0#e#2#p#k#u$2$3#4#Z#;#E#K#L#\#]#_#g#f#m#l#s#r#w#x#z$*$+$/$0$4$5$1$6#5$7#3$8$9$:#>#?#O#B#I#J#Y#j#G$$$##F#y#A#<#@#`#a#n#:#o#M#C#P#S#q$'#~$.$-#N#V#i#v$%#WG#q&#r%#s$#t%#u%#v%#w&#x%#y'#z*#{%#|+#}%#5&#~$$#%$$%$%%$&%$'$$($$)%$*%$+$$,%$-%$.%$/*$0&$1&$2$$3%$4%$5%$6%$7)1S#1#1#USB#6#US+#/$G%G2$##&#Gj#$'#US,)9)#VSC,H&-H*I#USD/'%#-%#USEH%H*I#A8A7/6H:#$%#8'#'*#-*#%K*I#/>K:#$-#8/#'(#-(#&s#%O%MVS-#3VS.%#;s#)#/s#)MB%72$#0s#,&#0s#-OM#s#-$#j##.#:)$>#8@#'0#%O*I#%S)/s#7S):#$s#&#8s#(#''#&s#=N1s#?1#1#1#1#A#%S$$$#(+#;s#GG/s#GNBGs#52$#0s#J&#0s#KPN#s#K$#j#%C#;s#O+VS%s#O#VS%s#PN/s#QS$B/s#?2$#k##s#Ss#SUS%s#Uk##s#V$9#$6G6J6H##JG&KH&KJ#C$#k##&#&HJ&HG#C$#6K##HJk##%#-)#6M##KHk##-#j##&#j##$Gj##/#WSFHJGYS/1+&$#j#&8#j#':#j#(S0#k#&;/k#'=#k#(S0#&s#vP%N$s#7#(%#;s#z#VSGs#{$&s#|S1#CG#j#%C#VS2(s#>#Cs#?IUSH#%P$s#B#(*#3#s#D$s#E#4%s#F($##C'#k##+#VS3)s#J'Is#K&s$1S4%S1$s#N#(%#4#s#P*I#'$s#R-$#k##+#VS5(s#U's#VI&s$<S6%S4$s#Y#(%#4#s#['s#\#*$I-$#k##+#VS7(s#`&s$FS8%S6$s#c#(%#3#s#e#C#Ik##s#*#VS9&s#h&s$NS*%S8$s#k#(%#4#s#m#C#$k##s#2#3&s#p&s$VS:%S*$s#s#(%#4#s#uVSIIs#v9SJ#m##s#/UO#*IG'Gs#{-$#USKS#VSLC#7S;7#7#5C#WS<C'#5CS;)C$#VSMCs$*WSNC#%7)7#5C#5C%)C#,)C%#)C)#<#S&C-#)C1/7+5C#WS<C8+5C7)C$#)C&#)C3#<#S&C+#US,Q0Q$#0Q/#US+QDCMUSOCXS=C$H#DCKXS=C$J#USPCUSQCECI=CS#+C$R#,&FDDE#LECs$N+C&S'#,)FDDE#L>*FDDE&#USRD+C'S(+,-FDDE#LZSS.FDDE#=Cs%>USTS#=C#?C-#@C&#=Cs%B?C0#@C#4+C&S(#,8FDDE#L.9FDDE-0#+C9R-,;FDDE#L+C/S'7,=FDDE#L>>FDDE%#+C=S(2,@FDDE#L.AFDDE%8#.BFDDE+9#.s##FDDE;:#VSUs#$E9S>S?VSVGH#S>#S?m$%#WSWCIJXSXGH$#l#)*)#l#*s#.s#-#l#+s#5s#4#j#,C#j#-C#j#.C#j#/C#k##s$<SY$s$zM(K#$s$|O(#H#C%#k##(#*IK'Ks%%-$##CKMk##$#k##(#k##s#h#k#,C#k#-C#k#.C#k#/C#%S@&s%qSZ[GK$#HJNS:l#08&#l#1s#ts#q#l#2s#yC#l#3s$#C#l#4s$,s$%#l#5s$5s$.#l#6s$As$7#l#1s$Ms$C#l#7s$Zs$O##Cs$_s$dm#$#&s%~s$bVS[s&#s$dFCs$cs$`%$#XGs&%s$eP#l#7s$ns$k#\SAs&&s%0s%/s%/s%6Ns%-#8s%qs%p3s%A#2s%@G#s&)#Nj#%C#VS2s%Es%H3s$os%I$s%J#4s$qs%K($##Cs$s#k##s$l#VS3s$us%O*Is$h's$is%Q-$#k##s$f#VS5s$os%T's%Us$c*s$dI-$#k##s$`#VS7s$hs%Y3s$^s%Z#C#Ik##s${#VS9s$as%]4s$Xs%^#C#s$Yk##s%##)Cs$*s$8)Cs$>#)Cs$6#<#S&5Cs$D)Cs$A#)Cs$;#)Cs$B%<#S&C%#0Q#s$.0Q*#+Cs$%Rs#p,s$'FDDE#L+Cs#rS's$#,s$)FDDE#L>s$*FDDE%#?Cs$&s$)@Cs#y#?Cs$(s#|@C#s#x+C%S(#,s$0FDDE#L.s$1FDDEs$%s$(#+Cs$1Rs$#,s$3FDDE#L+Cs$%S's$/,s$5FDDE#L>s$6FDDE%#.s$7FDDE#s$.s#u.s$8FDDE)s$/#.s$9FDDE1s$0#l#)#s#ts#nl#*s$=s$<#l#+9s$C#j#,C#j#-C#j#.C#j#/C#$s&,H(M#$s&.K(#O#C%#k##s#r#*IM'Ms&3-$#k###s#lk##'#k##s#o#k#,C#k#-C#k#.C#k#/C#&s&}S@%S\[GH$K#JNS*l#06&#l#1s%%s$~#l#2s%2C#l#3s%;C#l#4s#Ds#A#l#5s#Is#F#l#6s#Os#K#l#1s#Us#Q#l#7s#]s#W#3s&Es&H#Cs&H#/s'.P2#G#s'/#Pj#%C#ZS]Cs%v#S$s#cGl#7*(#ECs&}+Cs$eR#,s$gFDDE#Ll#)#s$Fs$@l#*s$ns$j#l#+s$ts$q#*Is''l#0$#GWS^s&Us')#FCs#ss#p,s&I#\SAs'=s'=s&Ms&Ls&IS$s#v#VS-s&Zs',VS.s&b#DCJ.s$sFDDEs$ks$js$kl#)#s$Rs$Ll#*%s$v#l#+s%$s$}#j#,C#*IJ'Js&d-$#k##s%H#k#,C#VGs&5S)l#0)$#.s%#FDDEs${s$vs${l#)#s$^s$Xl#*1s%&#l#+s%0s%-#j#,C#k##s%S.k#,C#VGs&=Hl#0&$#XS_s&ys&r,#FCs&qs&i<:#j#8s&|#j#9s''#V#JGj##s'+#j##s'B#YS/s'Cs'>s'1#Gl#7s'Ps'F#l#:s'Ws'R#0s'aHJ/s'b#%$2$##s'd#&m#(#j#;s'b#j#$s'g#j#<s'i#YS`s'js'ds'b#Gj#$s'j##"). Qed.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. pose proof (bytes_le_to_Z_bound bs) as B. rewrite L in B.
  rewrite Z_to_bv_unsigned, (bv_wrap_small 64) by (unfold bv_modulus; cbn in B |- *; lia).
  rewrite <- L. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le4. pose proof (bytes_le_to_Z_bound bs) as B. rewrite L in B.
  rewrite Z_to_bv_unsigned, (bv_wrap_small 64) by (unfold bv_modulus; cbn in B |- *; lia).
  rewrite <- L. apply Z_to_le_bytes_of_bytes.
Qed.

Section HCW6.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma NodeCells_of_junk : forall m a junk,
  rw_cells rsegs m a [CB 32 junk] -> exists nd pad, node_wf nd /\ rw_cells rsegs m a (NodeCells nd pad).
Proof.
  ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RSegs.rsegs); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.CB); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Datatypes.nil); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_at); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.wr_at); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Logic.ex); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBMem.node); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.node_wf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.NodeCells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_wf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.bytes_at); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_bytes); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.length); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Lists.ListDef.firstn); constr:(@Corelib.Lists.ListDef.skipn); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Nat.min); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.ZArith.BinInt.Z.min); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_sym); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_iff); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.Arith.PeanoNat.Nat.min); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_min); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.min_spec); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.Lists.List.length_firstn); constr:(@Corelib.Init.Nat.sub); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.Arith.PeanoNat.Nat.sub); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_sub_max); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.Lists.List.length_skipn); constr:(@Corelib.Init.Datatypes.app); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.eq_Transitive); constr:(@Corelib.Classes.RelationClasses.symmetry); constr:(@Corelib.Classes.RelationClasses.eq_Symmetric); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@Stdlib.Lists.List.firstn_skipn); constr:(@stdpp.tactics.f_equal_help); constr:(@Corelib.Init.Nat.add); constr:(@Stdlib.Lists.List.skipn_skipn); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.bytes_le_to_Z_bound); constr:(@LinuxProcessSemantics.LinuxProcessSem.BvBase.bytes_le_to_Z); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.ex_intro); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBMem.mkNode); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.micromega.ZifyClasses.eq_iff); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBMem.n_par); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBMem.n_lft); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBMem.n_rgt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RB.RBMem.n_col); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.rw_cells_recells); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.le8); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.le4); constr:(@Stdlib.Lists.List.app_nil_r); constr:(@Stdlib.Lists.List.app_assoc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.le4_of_bytes); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XF_rep.le8_of_bytes); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C4)|] [|@pad; @nd; @n; @y; @x; @__ff; @__varmap; @__wit; @__x1; @__x2; @__p1; @__arith; @z4; @H4; @cstr; @L0; @m; @__x3; @z5; @H5; @cstr0; @L1; @cstr1; @L2; @z3; @H3; @cstr2; @L3; @cstr3; @L4; @lemma; @l; @Ha; @__x4; @__sat12; @__sat10; @__sat8; @__sat6; @__sat5; @__sat7; @__sat9; @__sat11; @cstr4; @LP0; @B4; @junk; @B3; @B2; @B1; @B0; @EJ; @LP; @b3; @b2; @b1; @b0; @_H; @L; @_H0; @WF; @H0; @H; @a|] "#3R#T%&#\$?#t$,$@$>###i$I#$#%#v#&$G#'#T#a#_#5#;#2#4#1#3$0#*#)$J#6#+#-#<$/#m#(#,$Y#.$7#/#|#8#0$j$i%##Z#s$&$'$V$W$X$Z$\#F#E$`$b$^$c$]$g$k$p$o$u$v#X#e#n#o#p#q#7$-#9$4$9#:$[#D#G$e$f$d%$%*%+#f#W#]#d#g$C$N$O#@#=#>#?#C$m$r$s$t$y%&$l#[$$$#$6$5$:$;$=$K$L$P$Q$M#A#B$_$a#H$q#M#S$x$w#O#P#Q#R$z${$|$}%'%)%,$~#k$+$(#u$E$D#c#`#x#~#y$B$U$)$*$<#w$h$.$T#b$%#Y$8#z$2#^#}$H$A%%#l%(#r$1$F$n#j$3#{#h$R$SU#R&$W%#`&$X%#C%$Y%$Z%#*$$['$\*$]$$^&$_&$`/$a)$b*$c%$d'$e$$f+$g&$h$$i%#O%$j%$k%$l5#N%$m$$n'#K%$o%$p&$q'$r$$s%$t*$u%$v%$w'$x$$y%$z%${'$|$$}%$~'%#'%$&%%%?SA?#?#?#?#?#USW#USm#USW(USm#UT$#k##&#USn%-So-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#-#<#IUSXS#.S#$#DS$ML#<'L.S##&DS$OM#<*M.S##)XSpS$QO#O$*#RS$QO#$&#USYLVSZLIDS$S,S-#$%#j#$s#5#Is#6#j#%S4#IS4#j##+#<:O.S##9O#*#RS$S5Q#<?Q.S##>XSpS$S-S5#<BS5.S##AUS[#K$XS\S$S,S-#$%#<s#(S-.S##s#'O#*#RS$S0S,#DS$S8S1=$?#j#$s#O#Is#P#j#%S4#IS4#k##)#j##/#K.XS\S$S0S,#<s#7S,.S##s#6US[#<s#:S0.S##s#9K#XS\S$S1S6#<s#>S6.S##s#=O#*#RS$S8S1#)s#fS1#E#s#D$#NDS$S'S)s#6$s#8#j#$s#h#Is#i#j#%S4#IS4#j##)#)s#pS:#E#s#N7s#rs#gS)/s#ss#hS'7s#ts#i#/s#us#bS*7s#vs#k#/s#ws#\S(7s#xs#q#/s#ys#ZS%)s#zS/Bs#p##EIs#qj#&E##E%s#sEs$**(A$##C#%USBEUSBC*L*I#C$##ELIVT%LIWT&%$#j#'E#j#(E#(C0(C0=EEECCCSCJJJS;SDs$(2$71#0EC/J.&71#s$)3%#E9s#nEs$;#C5#(C$0EC4J3+=7)s#r%#4'%#S-)s$;S]5#*$&F#)s$?S<*#VS^@#'A$AB%#C#s##$%#&(s#%#C&)$$#9&#)s$JS_*#As#+#PCs$GUT'SAVT(C#PCs$LWS`C$#CC'#L#S9PCs$OWS`C(#PCSoCC(#CC%#L#S9CC'&L#S9USXS+.S+$#.S+'#.S+.#USnS+VSaCMUT)C@C$L#UT*CUT+CZSq#HDDGQMCSAFCs#G+C$P#,'HDDG#K2(HDDG'#MCs$u+C#S.',+HDDG#K+C*P%,-HDDG#K2.HDDG%#G/HDDG)#UT,DFCs#@+C+P#,3HDDG#K64HDDG#&/65HDDG('#VT-6G(SrSsVT.IM#Sr#Ssm$%#WT/CFLXT0IM$#l#)*)#l#*@?#l#+s#%s#$#j#,C#j#-C#j#.R##CIs#e$M#&Ls#g#CIL$$#9&##CMs#X#CMs#lk##$#k##&#k#,C#k#-C#k#.R#)s%7S&*#'s#t#YI#$LMQl#/4'#l#0s#NC#l#1s#Zs#R#l#2s#`s#^#l#3s#cs#f#Qs#|s#xs#j#7s%As%6S/)s%B#Ss%Cs%8S/1Es$'s$%&$#)s%EQ#E#s%;/s%Gs%<S])s%H#Bs%>#Ts#ms%?Bs%@I#E#s%Aj#&E#Bs%C&#E#s%D3s#qs$/;F#As$1##C#s$23LI;F#j#4C#j#&C#(Cs#y=EEECCCSEJJJ$SFs#|s#z#s%Ns$8s$*=EEECCCSCJJJS;SDs%Os$9s$+2+#0ECs$6Js$5s$-/+#s%Ps$:s$,)s%\S5#E#s%R*$#C#s$>(C$0ECs$<Js$;s$3'%#s%Vs$@s$24'%#I#Es$&s%@#Cs$&s$0(Cs$'0ECs$AJs$@s$8s$)s$(#s%Cs$2s$04&%#S0)s%hS,5#*$&F#)s%lSb5#*$&F#3s#:s$OVSGF#'F$;F%#C#&$%#&(F#C&F$$#9&#)s%zS2*#3#s$[;F#VS^s$]I's$^IAs$_I#C#s$`$%#&Is$b#C&I$$#9&#As$fLPCs&%CCs$6s$:CC$#L#S9WS`Cs$?s$ACC#s$9L#S9.S+#s$5.S+'#.S+(#.S+s$A#.S+s$B#VSaCO@C#Os$5@C#Ls$7MCs&C+Cs$2S7#,s$6HDDG#K2s$7HDDG#s$2+C&S.s$5,s$9HDDG#K+Cs$8P(,s$;HDDG#K2s$<HDDG%#Gs$=HDDG(#ZSqs$>HDDGS5UScSAMC#WSHC#s$>+C0P#,s$CHDDG#K2s$DHDDG(#FCF+C'S.#,s$GHDDG#K+C6P%,s$IHDDG#K2s$JHDDG%#Gs$KHDDG)#+C.Ps$=,s$MHDDG#K6s$NHDDG#s$@s$I6s$OHDDG&s$A#6s$PHDDG5s$B#l#)#s$=s$7l#*As$S#l#+s#%s$X#j#,C#j#-C#j#5C#j#.R#'s%>M$#s$8&Ms%@#CIM$$#9&#3Ms%D#CO#$Q#&%F#COF$$#9&##COs%8#COs%Lk##$#k##&#k##.#k#,C#k#-C#k#5C#k#.R#)s&uSt*#3#s%V'F#[I#O%LMQS,l#/>(#l#6s#RC#l#7s#\s#T#l#0s#^C#l#1s#ks#c#l#8s#ps#n#l#2s#us#s#l#9s#xs#{#l#9s#~s$%#Qs$6s$2s$*#WSIs'(s&yS]1Es$=s$:$s$?#7s'*s&{s$A)s'+#Ss',s&}s$C1Es$Bs%j&$#/s'.s&wS<)s'/#Bs'%#Ts%Ps&zBs''##E#s'(Es':3s%S#;F#As%r##C#s%s(C'=EEECCCSEJJJs$ASFs%Ys%Xs$3s''(#=EEECCCSCJJJS;SDs'0s%vs%h,'#0ECs%sJs%rs%j,'#s'1s%ws%i#Es$3s'2#Cs$2s%y(Cs$30ECs%wJs%vs%ns$6s$4#s'5s%{s%m4&%#M#Es$4s&{#Cs$3s%k(Cs$40ECs%|Js%{s%ss$7s$5#s&~s%ms%k4&%#S1)s'GS05#*$&F#5s&C*s&D&F#)s'NSu5#*$&F#)s'RSv*#3#BVSGF#'F$;F%#C#&$%#&(F#C&F$$#9&#)s'^Sw*#3#s#.;F#@Cs%_Os%^@C#Ls$,UScs'mMC#+Cs%\S7#,s%`HDDG#K2s%aHDDG#s%\+C&S.s%_,s%cHDDG#K+Cs%bP(,s%eHDDG#K2s%fHDDG%#Gs%gHDDG(#FCs#=WSHCs$7#+C.P#,s%kHDDG#K2s%lHDDGs$0#+C&S.s$*,s%nHDDG#K+C3Ps$,,s%pHDDG#K2s%qHDDG%#Gs%rHDDG(#+Cs$APs%d,s%tHDDG#K6s%uHDDG#s%gs%p6s%vHDDG&s%h#6s%wHDDG2s%i#l#)#s%ds%^l#*?s%z#l#+s$Ls&##j#,C#j#-C#j#5C#j#.R#3Ms#T#CO#$Q#&%F$#s$#9%#k###s#|k##s$+#k#,C#k#-C#k#5C#k#.R#)s(6Sx*#3#s#b'F#[I#O%LMQS0l#/4(#l#6s$oC#l#7s$ys$q#l#0s#;C#l#1s#Hs#@#l#:s#Os#M#l#8s#Ts#R#l#2s#Xs#V#l#;s#[s#^#l#;s#as#d#l#;s%As%D#Qs#qs#ls#h#WSIs(Gs(4S<1Es#us%Y$s#w#7s(Is(>s#y)s(J#Ss(Ks(@s#{1Es#zs'-&$#/s(Ms(2S_)s(N#Bs(H##EIs(Ij#&E#Ts&fs(7Bs(LI#E#s(Mj#&E#Bs(O&#E#s(PEs(`?s$q?#?#E#3s&p#;F#A)##C#*(C+(Cs&u(C)=EEECCCSEJJJs%kSFs&xs&w$s(I*#=EEECCCSCJJJS;SDs(^/&5)#0ECs'AJs'@s'82)#s(_0')s(gS6#E#s(]*$#C#s'I(C$0ECs'GJs'Fs'>'%#s(as'Ks'=4'%#Q#Es%Rs(K#Cs%Rs';(Cs%S0ECs'LJs'Ks'Cs%Us%T#s(Ns'=s';4&%#S:5.&F-)s(uS85#*$&F#)s(yS=5#*$&F#5s$f&Fs$f)s)#T1*#3#s#'VSGF#'F$;F%#C#&$%#&(F#C&F$$#9&#)s)/T2*#3#s#3;F#VS^s#9I's#:IAs#;I#C#s#<$%#&Is#>#C&I$$#9&#As#BL@Cs'9Os%c@C#Ls$:FCs#EMCs#E+C$S7#,s';HDDG#K+Cs':P&,s'=HDDG#K2s'>HDDG%#+C(S.),s'@HDDG#K+Cs'?P*,s'BHDDG#K2s'CHDDG%#Gs'DHDDG(#FCs#NWSHCs$F#+C0P#,s'HHDDG#K2s'IHDDGs%i#+C&S.s%c,s'KHDDG#K+C5Ps%e,s'MHDDG#K2s'NHDDG%#Gs'OHDDG(#+Cs$PPs'A,s'QHDDG#K6s'RHDDG#s'D76s'SHDDG&s'E#6s'THDDG2s'F#l#)#s'As';l#*As'W#l#+s&)s'\#j#,C#j#-C#j#5C#j#.R#'s#iM#CIs#j$$#&Ms#l$#s%c9%#3Ms#k#CO#$Q#&%F$#s%b9%##COs#uk##s%b#k##%#k##,#k#,C#k#-C#k#5C#k#.R#)s)wSJ*#3#s#{'F#[I#O%LMQS6l#/<(#l#0s#CC#l#1s#Ms#E#l#<s#OC#l#=s#\s#T#l#>s#bs#a#l#:s#fs#d#l#8s#ks#i#l#2s#os#n#l#?s#qs#t#l#?s#ws#z#l#?s%Hs%K#l#?s'(s'+#Qs$4s$+s$%#WSIs*.s)oS_1Es$;s$8$s$?#7s*0s*)s$A)s*1#Ss*2s*+s$C1Es$Bs$@&$##Es'Ms*-Ts''s)r#E#s*/UScs&O?#?#E#3s'+#;F##C#s$C(C&=EEECCCSEJJJs'FSFs'1s'/s%Ys)|'#0ECs(wJs(vs(n-&#s*9s$Fs$=#Es'Cs*:#Cs'Bs$H0ECs(zJs(ys(qs'Es'Cs'As*<s$Is$@4%$#I#Es$.s*:#Cs$-s)%(Cs$.0ECs)#Js(~s(vs$1s$/#s*=s)'s(u4&%#S-#Es%Vs*'#Cs%Vs(s(Cs%W0ECs)(Js)'s({s%Ys%X#s**s(us(s4&%#S)5s)=*s)>&F#)s*RS)5#*$&F#)s*VS*5#*$&F#5s%&&Fs%&)s*\Sd*#3#s#&VSGF#'F$;F%#C#&$%#&(F#C&F$$#9&#)s*hSK*#3#s#2;F#CCs(zs(tCCs(w#L#S9.S+#s(q.S+s(u#.S+s(|#@Cs(nMs(o@C#Ls(oFCs#<WSHCs$7#+Cs(mP#,s(pHDDG#K2s(qHDDGs(p#+C&S.s'/,s(sHDDG#K+Cs(rPs'1,s(uHDDG#K2s(vHDDG%#Gs(wHDDG(#+Cs$APs(i,s(yHDDG#K6s(zHDDG#s(ls$?6s({HDDG&s(m#l#)#s(hs(bl#*3s(~#l#+6s)'#j#,C#j#-C#j#.R#3Ls#Q#CI#$M#&%F#CIF$$#9&##CMs%:k##s(c#k##%#k#,C#k#-C#k#.R#)s+:Se*#3#s#`'F#YI#%LMS0l#/5(#l#0s#3C#l#1s#@s#8#l#@s#Fs#E#l#>s#Js#H#l#:s#Os#M#l#8s#Ts#R#l#2s&Ys&W#l#As#Ws#Z#l#As#]s#`#l#As%:s%=#l#As&gs&j#l#As#es#g#Qs#ts#ms#j#/s+Ms+.Sb)s+N#WSIs+Os+0Sb1Es#ys%]&$#7s+Qs+FS&/s+Rs+GS&%s+S$##s+Q#S&USBs+RUT3s+S7s+Ws+LS2/s+Xs+MS2%s+Y$#UT4s+WZSLs+X(#$S2I7s+\s+Q&/s+]s+JS27s+^s+S#/s+_s+DS27s+`s+Y#/s+as+BS2%s+b$#%s+c'#%s+d*#%s+e0#VSMs+c#]SNs+d43S20.$$#j#B6#WSOs+is+^S&VSPs+j;7s+ks+`;/s+ls+YS&7s+ms+b#/s+ns+SS&7s+os+h#/s+ps+QS&%s+q$#%s+r'#%s+s*#k##s+qs+q(#-/s+vs+ks#&%s+w.##s+u#s#(/s+ys+ns##%s+z@#ZSLs+xs#(s###s#%IVSMs+y:]SNs+zs#*s#)s#'%$;;#j#B(#WSOs,#s+ts#/VSfs+us+u/s,%#S&%s,&s#(I#s,$#Aj#Cs,%#VSPs,)<(4#/s,+s+|=%s,,=##s,*#?/s,.s,#s#/%s,/s#/#ZSLs,-s#9s#4#s#1IVSMs,.s#,]SNs,/s#;s#:s#3%$s#-s#-#j#B(#WSOs,4s,)s#&VSfs,*s+~/s,6#S&%s,7s#7I#s,5#s#3j#Cs,6#VSPs,:s#+(s#%#/s,<s,5s#,%s,=s#,##s,;#s#./s,?s,8s#>%s,@s#>#ZSLs,>s#Js#E#s#@IVSMs,?s#>]SNs,@s#Ls#Ks#B%$s#?s#?#j#B(#WSOs,Es,>s#5VSfs,?s,+/s,G#S&%s,Hs#FI#s,F#s#Ej#Cs,G#(s,Hs#8%s,Ls#;'#s,J#s#:m#%#XSgs,Os,Hs,4S&1s,M+($6#V/.#\Shs,Os,O::s#Bs#?9#%s,Ss#D?#s,Q#s#@m#%#XSgs,Vs,Ks,CS&1s,Ts##@$s#.#Vs#'s#&#\Shs,Vs,Vs#2s#2s#Ks#Es#1#%s,Zs#Ms#7#s,X#s#Fm#%#XSgs,]s,Rs,RS&1s,[s#;s#8$s#F#Vs#?s#>#\Shs,]s,]s#Ts#Ts#ls#Ks#I#Vs#Ws#V#%s,bS-S5%s,cS,#%s,dS0#%s,eS6##s,cS&#USQS18S1&F#Es,s>s+Js'}:$#''#$'#8S:&F#>s+Ps+I:*#'&#$&#j#&E#ZSREs&_#Is,kS-8S8&F#*s,n>s+Y#:3#''#$'#USQS8>s+^s&f:8#',#$,#8S=&F#'$5$$#j#&E#ZSREs+v#Is,}S,'<0$<#USQS:>s+ks%>:s#%#'A#$A#8S)&F#'$B$$#j#&E#ZSREs&z#Is-.S0'5=$5#USQS=>s+xs&|:s#2#':#$:#8S'&F#'$s#/$$#j#&E#ZSREs%R#Is-?S6*s-@>s,'#:s#=#'8#$8#DS$T5Ses,u$s,w#j#$s-K#Is-L#j#%S4#8S%8S(8S*XSy%$#58S/XSy#'&%USY#VSZ$IDS$SeSJ#$%#j#$s-X#USY*VSZ+S)DS$SJSK#'@8$@#>s,@s'g:s#V#'s#$#$s#$#j#(CIU#s'l>s,F#:s#\#'s#*#(Rs#*#Rs#+s#+m#$#WSSs#-s#-#'LIUT6#j#'C#j#(C#(Cs#3:LIXSzCCS{#(C#j#4C#j#&C#(Cs#l>LIXSzCCS{#(C#j#4C#j#&C#(Cs,Vj#(E#`S|ECCCJJ==#s-ys(*s'}=CCCCCCS>>>>S>&s,`s,`s,Rs#<=#=CCCCCCS????S?-s#vs#v,s#<=#0CCS3@S34s#Ds#D3s#<=#ZSTs#Ds#'s#D=9#4s#'s###I&Fs#6's#7s#j$$#>s,hs,h:s#~#'s#;#$(#Us#*s,l>s,m#:s$'#'s#@#(R-#R..m#$#WSS00#(Cs#E`S|ECCCJJs#3s#39s./s,us,g=CCCCCCS>s#4s#4s#4S><s,vs,vs,hs#|,#=CCCCCCS?s#5s#5s#5S?s##s$0s$0Bs#|,#0CCS3s#6S3s#*s#Is#I&s#|,#ZST656,(#451#O&Fs#I's#Js$$$$#'s#L7$&#'s#N4(R(#R))m#$#WSS++#(Cs#S0CCS3s#DS3s#8s#Ts#T#s$.:1ZST.-.)%#4-+#S-8S<&F#'$s$3$$#'&s#&$&#'(s##(R(#R))m#$#WSS++#(C-0CCS3s#SS3s#G..#s$=s#)@ZST.-.)%#4-+#S6)s.]S%#E#s.W*$#C#s(f(C$0ECs-=Js-<s-4'%#s.[s(hs(_4'%#S=#Es-+s.]#Cs-*s(k0ECs-AJs-@s-8s--s-+s+ls._s(ls(c4%$#S'#Es,|s.]#Cs,|s-H0ECs-EJs-Ds-<s,~s,}s(fs._s-Is-;4%$#S(#Es,7s.a#Cs,7s-L(Cs,80ECs-JJs-Is-As,:s,9#s.ds-Ns-@4&%#S/#Es*%s.f#Cs*$s-Q(Cs*%0ECs-OJs-Ns-Fs*(s*&#s.is-Ss-E4&%#S<)s.vT7#E#s.T*$#C#s-E(C$0ECs-VJs-Us-M'%#s.Xs-Gs-E4'%#St5s+a&Fs+a5s*/&Fs*/)s/%T85#*$&F#VSUs$ys-Q'Fs$z&Fs-S:s$|s-T'F#k##%#k##'#&Fs%$WSVs%%s-YLj##N#j#D%#&F*k##N#k#D(#VSUs%+s$4&Fs$5'Fs$5k##$#k##3#WSVs%0s$9Lj##N#j#D0#&Fs$;k##N#k#D3#Es/FVSUs%7#&F$:s%9%'F#k##%#k##@#WSVs%=)Lj##N#j#D=#&F)k##N#k#D@#VSUs%Cs$$&Fs$%'Fs$%k##$#k##s#+#WSVs%Hs$)Lj##N#j#Ds#(#&Fs$+k##N#k#Ds#+#VT9Fs%N(T:#m##s#4UL#UQ$US,%US1&VSaCQ@C#Ms-^@C#Ls,-+Cs+vS.s-[,s-^HDDG#KFCs%ZWS}C#s/j+Cs-_S7#,s-bHDDG#K2s-cHDDG'#+Cs+}S.s-],s-eHDDG#K+Cs-_S7(,s-gHDDG#K2s-hHDDG%#+Cs,&S.s,+,s-jHDDG#K+Cs,-S7-,s-lHDDG#K2s-mHDDG%#+Cs,+S.s,<,s-oHDDG#KUSWs/|WS}C4#+Cs,@S7#,s-sHDDG#K2s-tHDDG'#2s-uHDDG*#2s-vHDDG0#2s-wHDDG6#6s-xHDDG&s-j#6s-yHDDG.s-k#6s-zHDDG4s-l#6s-{HDDG:s-m#l#)#s-hs-bl#*s##s-~#l#+s.+s.'#j#,C#j#-C#j#5C#j#EC#&FI'Is#H$$#&FM'Ms#K$$#&FQ'Qs#N$$#&FS-'S-s#j$$#&FS5'S5s#T$$#'S-s#V$)#&FS,'S,s#r$$#$&#$)#$0#k##.#k##2#k##6#k##:#k#,C#k#-C#k#5C#k#EC#8T;8T<8T=8T>\I&%$#S2SuSvSwl#/s#'(#l#Fs#Qs$'#l#Gs#Ss#x#l#Hs#Us#l#l#Is#Ws#b#l#Js#_s#\#l#Is#gs#c#l#Ks#ls#i#l#Hs#us#p#l#Ls#{s#x#l#Gs$'s$##l#Ms$,s$)#l#Fs$7s$1#l#Ns$;s$9#l#@s(ds(c#l#>s$@s$?#l#:s*Cs*B#l#8s$Bs$A#l#2s$Es$D#l#As$Gs$J#l#As$Os$R#l#As$Us$X#l#As$[s$]#l#As$`s$b#l#Os$es$h#l#Ps$ms$v#l#Ps$}s%*#l#Ps%0s%?#l#Ps%Gs%h#UT?s%y&F#'$s$.$$#UT@s%}&F#'$s$2$$#UTAs&%&F#'$s$6$$#UTBs&)&F#'$s$S$$#$'#$,#$1#m#6#m##s&)<s0aSd.S##s0`#Es)6s1#$#N$N#$N#$N#N'NS6S@NN'S@#NN'S@#NN'S@#NN'S@#US[s&5m#$#Hs19s&CUSi#Hs1;s&DUSi#Hs1=s&EUS~#USXs1<%s1=S'#%s1>%#%s1?(#%s1@+#%s1AI#%s1BSK(#s1@$#j#Cs1A#%s1EI(%s1FS/##s1D#'j#Cs1E#%s1II-%s1JS%#%s1KS/##s1I#,j#Cs1J#%s1NI3%s1OS(#%s1PS%#%s1QS/##s1O#2j#Cs1P#%s1TS'S)%s1US*#%s1VS(#%s1WS%#%s1XS*=%s1YS(#%s1ZS%#%s1[S/#%s1\IB#s1Z$#j#Qs1[#%s1_S%S(%s1`S)s#&%s1aS'#%s1bS*#%s1c&#%s1dS*S'%s1eS(#%s1fS%#%s1gS/#%s1h#s#.#s1fI#j#Cs1g#%s1k.S*%s1l#-%s1m$S'%s1n#0%s1o$S)%s1p#s#6%s1q4>%s1rS/S%%s1s#S(%s1t#S*%s1u#S'%s1v#s#<#s1t#=j#Cs1u#%s1y0s#'#s1wIIj#Cs1x#(s1y/VTCs1}01s1{1%$0#Js2#6S'S)1s1}3*$)#Js2%s#$S*s#/1s2#+,$3#Js2'S%S(s#01s2%5.$s#/#Js2):S)s#K1s2'8>$:#Js2+>S's#)1s2)<@$>#Js2-s#,S*s#*1s2+@B$s#)#%s2/S(s#+%s20S%#Js21S%S(s#-1s2/s#-s#&&$#1s20s#:s#3#SdS0Hs27s'QUS~#VTDS'S11s24S's#B&$#USis#\VSjS*S81s27S*s#K%$#VSjS(S:1s29S(s#R$s#a#VSjS%S=1s2;S%s#X$s#e#Hs2Bs$.USk#Hs2Ds$,USk#Hs2Fs$*USk#Hs2Hs$(UTE#<s2@S).S##s2#.S#%#.S#(#.S#+#.S#.#K#Ks$'#s2L$#m#4#Ks'R#s2O#&m#%#Os$-(E#\TFSJSKs$/s'WSxs$#%#Ns'Ys'Ws$2#XT#s2Us'[S)#XT#S4s'gs'c#l#Rs'rs'm#l#Rs'}s'y#l#Ss(%s(##l#Ss(0s(,#l#Ts(4s(2#l#Ts(?s(;#l#Us(Hs(A#l#Us(Xs(Q#l#Vs(_s(Z#l#Ws)qs+1#l#?s+3s+2#l#;s,ws/}#l#9s.;s/~#l#3s0%s0##l#$s1Ms2e#l#Xs1Os2f#l#Ys1Rs2g#l#Zs1Us2h#l#[s1Xs2i#j#\N#j#]s1[#V#LIj##N#j##s1h#YSls1iNs1a#Mj#^s1l#j#\s1r#j#_s1w#V#LIj##s1|#j##s23#YSls24s22s2$#Ij#`s28#V#LIj##s2=#j##s2P#YSls2Qs2Ns2D#Il#`Is2U#j#as2Y#j#Qs2~#j#bC#j#4s3%##"). Qed.

End HCW6.
