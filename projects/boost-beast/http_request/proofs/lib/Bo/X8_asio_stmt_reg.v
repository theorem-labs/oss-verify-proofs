(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsImgSh AsIface AsIface5 AsIface6 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import X8Kit X8SRKit XL_mutex X8_asio_stmt_alloc X8_asio_stmt_sp X8_asio_stmt_sp2.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record svce := mkSE { se_addr : Z ; se_hdr : svch ; se_tiname : Z }.

Definition svch_ok (S : svch) : Prop :=
  0 <= sv_vptr S < 2^64 /\ 0 <= sv_ti S < 2^64 /\ 0 <= sv_id S < 2^64 /\ 0 <= sv_owner S < 2^64
  /\ 0 <= sv_next S < 2^64 /\ 0 <= sv_destroy S < 2^64.

(* [comment removed for export] *)
Definition keys_match (kti kid kname : Z) (e : svce) : bool :=
  (negb (sv_id (se_hdr e) =? 0) && (sv_id (se_hdr e) =? kid))
  || (negb (sv_ti (se_hdr e) =? 0) && negb (kti =? 0) && (se_tiname e =? kname)).

(* [comment removed for export] *)
Fixpoint find_svc (kti kid kname : Z) (L : list svce) : Z :=
  match L with
  | [] => 0
  | e :: L' => if keys_match kti kid kname e then se_addr e else find_svc kti kid kname L'
  end.

Lemma keys_match_false_inv : forall kti kid kname e,
  keys_match kti kid kname e = false ->
  (sv_id (se_hdr e) = 0 \/ sv_id (se_hdr e) <> kid)
  /\ (sv_ti (se_hdr e) = 0 \/ kti = 0 \/ se_tiname e <> kname).
Proof.
  intros kti kid kname e H. unfold keys_match in H.
  apply orb_false_iff in H. destruct H as [H1 H2].
  apply andb_false_iff in H1. apply andb_false_iff in H2.
  split.
  - destruct H1 as [H1|H1].
    + left. apply negb_false_iff in H1. apply Z.eqb_eq in H1. exact H1.
    + right. apply Z.eqb_neq in H1. exact H1.
  - destruct H2 as [H2|H2].
    + apply andb_false_iff in H2. destruct H2 as [H2|H2]; apply negb_false_iff in H2; apply Z.eqb_eq in H2; lia.
    + right; right. apply Z.eqb_neq in H2. exact H2.
Qed.

Lemma keys_match_true_id : forall kti kid kname a S nm,
  sv_id S <> 0 -> sv_id S = kid -> keys_match kti kid kname (mkSE a S nm) = true.
Proof.
  intros. unfold keys_match; cbn [se_hdr se_tiname]. apply orb_true_iff. left. apply andb_true_iff. split.
  - apply negb_true_iff. apply Z.eqb_neq. assumption.
  - apply Z.eqb_eq. assumption.
Qed.
Lemma keys_match_true_ti : forall kti kid kname a S nm,
  sv_ti S <> 0 -> kti <> 0 -> nm = kname -> keys_match kti kid kname (mkSE a S nm) = true.
Proof.
  intros. unfold keys_match; cbn [se_hdr se_tiname]. apply orb_true_iff. right. repeat (apply andb_true_iff; split).
  - apply negb_true_iff. apply Z.eqb_neq. assumption.
  - apply negb_true_iff. apply Z.eqb_neq. assumption.
  - apply Z.eqb_eq. assumption.
Qed.
Lemma keys_match_false_intro : forall kti kid kname a S nm,
  (sv_id S = 0 \/ sv_id S <> kid) -> (sv_ti S = 0 \/ kti = 0 \/ nm <> kname) ->
  keys_match kti kid kname (mkSE a S nm) = false.
Proof.
  intros kti kid kname a S nm H1 H2. unfold keys_match; cbn [se_hdr se_tiname]. apply orb_false_iff. split.
  - apply andb_false_iff. destruct H1 as [H1|H1]; [left; apply negb_false_iff; apply Z.eqb_eq; exact H1| right; apply Z.eqb_neq; exact H1].
  - apply andb_false_iff. destruct H2 as [H2|[H2|H2]].
    + left. apply andb_false_iff. left. apply negb_false_iff. apply Z.eqb_eq. exact H2.
    + left. apply andb_false_iff. right. apply negb_false_iff. apply Z.eqb_eq. exact H2.
    + right. apply Z.eqb_neq. exact H2.
Qed.
Lemma find_svc_none : forall kti kid kname L,
  Forall (fun e => keys_match kti kid kname e = false) L -> find_svc kti kid kname L = 0.
Proof. induction L as [|e L IH]; intros F; [reflexivity|]. cbn. rewrite (Forall_inv F). apply IH. exact (Forall_inv_tail F). Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition ati_ok (m : mem) (ti nm : Z) : Prop :=
  ro_cells bsegs m (ti + 8) [C8 (wz nm)] /\ 0 <= nm < 2^64
  /\ 0x119000 <= ti /\ ti + 16 <= 0x12a180 /\ ti mod 8 = 0 /\ aimg0b (ti + 8) 8 = true.

Definition asvce_ok (m : mem) (e : svce) : Prop :=
  0 < se_addr e /\ se_addr e mod 8 = 0 /\ aapp (se_addr e) 48
  /\ ro_cells bsegs m (se_addr e) (SvcHdrCells (se_hdr e)) /\ svch_ok (se_hdr e)
  /\ accessible m (se_addr e) 48
  /\ (sv_ti (se_hdr e) <> 0 -> ati_ok m (sv_ti (se_hdr e)) (se_tiname e)).

Fixpoint ASvcChain (m : mem) (first : Z) (L : list svce) : Prop :=
  match L with
  | [] => first = 0
  | e :: L' => first = se_addr e /\ asvce_ok m e /\ ASvcChain m (sv_next (se_hdr e)) L'
  end.

Lemma ASvcChain_nil_inv : forall m first, ASvcChain m first [] -> first = 0.
Proof. intros m first H. exact H. Qed.
Lemma ASvcChain_head : forall m first L, ASvcChain m first L -> L <> [] -> 0 < first /\ first + 48 <= aceil /\ first mod 8 = 0.
Proof.
  intros m first [|e L] CH NE; [congruence|]. cbn in CH. destruct CH as (-> & (POS & A8 & AP & _) & _).
  pose proof (aapp_bounds _ _ AP ltac:(lia)) as (B1 & B2 & B3 & B4 & B5). lia.
Qed.
Lemma ASvcChain_zero : forall m L, ASvcChain m 0 L -> L = [].
Proof. intros m [|e L] CH; [reflexivity|]. cbn in CH. destruct CH as (E & (POS & _) & _). lia. Qed.

(* [comment removed for export] *)
Lemma ati_ok_transport : forall W m m' ti nm,
  ati_ok m ti nm -> munch W m m' -> Forall (fun iv : Z * Z => 0x12a180 <= fst iv \/ snd iv <= 0x119000) W -> ati_ok m' ti nm.
Proof.
  intros W m m' ti nm (RO & R & LO' & HI' & T8 & IMG) MU FW. split; [| split; [exact R| split; [exact LO'| split; [exact HI'| split; [exact T8| exact IMG]]]]].
  eapply ro_cells_transport; [exact RO| exact MU|]. cbn [cells_size csize Nat.add].
  clear - FW LO' HI'. induction W as [|[lo hi] W IH]; [exact I|].
  pose proof (Forall_inv FW) as H1. cbn in H1. cbn. split; [lia|]. apply IH. exact (Forall_inv_tail FW).
Qed.

(* [comment removed for export] *)
Lemma ASvcChain_transport_fr : forall W m m' ff k first L,
  ASvcChain m first L -> munch W m m' ->
  Forall (win_fr ff k) W -> 0 <= ff -> ff mod 8 = 0 -> 0 <= k ->
  Forall (fun iv : Z * Z => 0x12a180 <= fst iv \/ snd iv <= 0x119000) W ->
  Forall (fun e => disjoint_from W (se_addr e) 48 /\ (se_addr e + 48 <= ff \/ ff + 8 * k <= se_addr e)) L ->
  ASvcChain m' first L.
Proof.
  intros W m m' ff k first L. revert first. induction L as [|e L IH]; intros first CH MU FW F0 F8 K0 FI OFF; [exact CH|].
  cbn in CH |- *. destruct CH as (E & (POS & A8 & AP & HD & OK & AC & TI) & CH').
  pose proof (Forall_inv OFF) as [O1 O2].
  split; [exact E|]. split.
  - split; [exact POS|]. split; [exact A8|]. split; [exact AP|].
    split. { eapply ro_cells_transport; [exact HD| exact MU|]. cbn [cells_size csize Nat.add SvcHdrCells]. exact O1. }
    split; [exact OK|].
    split. { eapply accessible_transport_fr; [exact AC| exact MU| exact FW| exact F0| exact F8| exact K0| exact O2]. }
    intros NZ. eapply ati_ok_transport; [exact (TI NZ)| exact MU| exact FI].
  - apply IH; [exact CH'| exact MU| exact FW| exact F0| exact F8| exact K0| exact FI| exact (Forall_inv_tail OFF)].
Qed.

Lemma ASvcChain_Forall : forall m first L, ASvcChain m first L -> Forall (asvce_ok m) L.
Proof.
  intros m first L. revert first. induction L as [|e L IH]; intros first CH; [constructor|].
  cbn in CH. destruct CH as (_ & OK & CH'). constructor; [exact OK| exact (IH _ CH')].
Qed.

(* [comment removed for export] *)
Lemma ati_ok_transport_hi : forall W m m' ti nm, ati_ok m ti nm -> munch W m m' -> wins_hi W -> ati_ok m' ti nm.
Proof.
  intros W m m' ti nm TI MU WH. eapply ati_ok_transport; [exact TI| exact MU|].
  eapply Forall_impl; [| exact WH]. intros [l h] K. cbn [fst snd] in *. unfold AIMG_TOP, AHI_LO in K. lia.
Qed.
Lemma ASvcChain_transport_hi : forall W m m' first L,
  ASvcChain m first L -> munch W m m' -> wins_hi W -> Forall (fun e => disjoint_from W (se_addr e) 48) L ->
  ASvcChain m' first L.
Proof.
  intros W m m' first L CH MU WH OFF.
  eapply (ASvcChain_transport_fr W m m' 0 0); [exact CH| exact MU| | lia| reflexivity| lia| |].
  - eapply Forall_impl; [| exact WH]. intros [l h] K. unfold win_fr. cbn [fst snd] in *. lia.
  - eapply Forall_impl; [| exact WH]. intros [l h] K. cbn [fst snd] in *. unfold AIMG_TOP, AHI_LO in K. lia.
  - pose proof (ASvcChain_Forall _ _ _ CH) as FO. clear CH MU WH. induction L as [|e L IH]; [constructor|].
    pose proof (Forall_inv FO) as (POS & _). constructor; [split; [exact (Forall_inv OFF)| right; lia]|].
    apply IH; [exact (Forall_inv_tail OFF)| exact (Forall_inv_tail FO)].
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

(* [comment removed for export] *)
Lemma ASvcChain_off3 : forall m first L lo h r svc,
  ASvcChain m first L -> aceil <= lo ->
  Forall (fun e => (se_addr e + 48 <= r \/ r + SZ_REG <= se_addr e) /\ (se_addr e + 48 <= svc \/ svc + SZ_SVC <= se_addr e)) L ->
  Forall (fun e => disjoint_from [(lo, h); (r, r + SZ_REG); (svc, svc + SZ_SVC)]%Z (se_addr e) 48) L.
Proof.
  ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.mem); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_asio_stmt_reg.svce); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_asio_stmt_reg.HCW.ASvcChain); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aceil); constr:(HCEIL); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_asio_stmt_reg.se_addr); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.SZ_REG); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.SZ_SVC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_asio_stmt_reg.HCW.ASvcChain_Forall); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_asio_stmt_reg.HCW.asvce_ok); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Lists.ListDef.Forall_nil); constr:(@Stdlib.Lists.List.Forall_inv); constr:(@kc__1); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aapp); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.ro_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.SvcHdrCells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_asio_stmt_reg.se_hdr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_asio_stmt_reg.svch_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.accessible); constr:(@Corelib.Init.Logic.not); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.sv_ti); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_asio_stmt_reg.HCW.ati_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_asio_stmt_reg.se_tiname); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aapp_bounds); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.AIMG_TOP); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.AAPP_HI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@Corelib.Lists.ListDef.Forall_cons); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Logic.or_introl); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Corelib.Init.Logic.I); constr:(@Stdlib.Lists.List.Forall_inv_tail)|] [|@e; @FO; @OFF; @L; @__ff; @__varmap; @__wit; @__arith; @__x1; @__x2; @__x3; @B5; @B4; @H; @B3; @B2; @B1; @O2; @O1; @_H0; @AP; @_H; @POS; @IH; @CE; @CH; @svc; @r; @h; @lo; @first; @m|] "#+)#V$P#Z#\#x###k$1#j#$#%#,#`#)#;$2#+#*#-#}#4$0$?#&#:#P#0#1#3#=#(#'#/#.#2#6#7#8#<#J#Q#5#>$5$6#F#I#?#B#O#i#9$+$>#C#A#H#G#E#N#R#[#f#u#m$4$:$;#D#K#M#S$C$H$I$F$L$N$S#]#_#h#l#q#t$,$-$/$7$9$<$=$8$*$@#@#L$E$J$K$P$D$Q$R#U$A#n#Y#b#^#d#p#r#e#c#w#a#y#o$#$'#~#|$$$%$&$)$(#{#v#g#z$3$.#s$G$O$M$BC$1%$2%$3%$4&$5'$6$$7%$8%$9&$:&$;&$<$$=$$>$$?'$@$$A&$B$$C$$D&$E&$F($G$#a$$H%$I'$J*$K$$L%$M%$N+$O'USNDWS`NS/S0USaM$#S0(FUSbSC9#9#9#9#USO#%)#$#S0%S0I$#,)%#$'S(%S(G$#0)%##'#j#$D#+D#NXScLQRK:L+D#R$1R%RI$#:)%#$5N%NG$#>)%##'#j#$D#+D#F:S1+D#JVSdCC'CCS2S#%LI'CCL#%QG'CCQ#>(&)$#&*'#&+*#-#s#/s#)j#$D#+D#Kk#%0#k#&3#j#'s#8#%NI$#s#6)=#$s#1S/%S/G$#s#:)%##'#j#$D#>D+D$#:S2+D#%'CCS#L%QI'CCQ#%RG'CCR#&s#$#>&s#%&#&s#&)#-#s#Js#Dj#$D#VSeD#j#%.#j#&1#$s#HQ$/s#P)$#$/s#R)s#=##%#j#$D#+D#F:S++D#J'CCS1S2%S#I'CCS##%LG'CCL#&s#;#s#5&s#<&#&s#=)#-#s#as#[j#$D#+D#Kk#%.#k#&1#$s#_L$s#Bs#g)$#$s#Bs#i)=##%#j#$D#&DKJ+D$#:S,&DS(K+D$#:S3YSPD#S0S(FVSQS3S0(S/*E#9SC9#9#USO#;(#,C#E7M*s#w.S/0#1S$S--#2%3S-/s#|/',C#E4#.N/#5N6S%$#k##'##+##-##/##3##5##<#'CCS3S,%S+I'CCS+#%S1G'CCS1#&s#s#s#m&s#t&#&s#u)#-#s$=s$7j#$D#&DNS/+D$#j##/#(N;#s#',C#E7M%s$?0>1S$S%'#2@3S%)s$C,CAE4#.R/#5R6S:$#k##'##*##,##.##1##3#(R*E#(Q;#s#=,C#E7M%s$U.Q0#1S$S4(#2%3S4*s$Z/',C#E4#.L/#5L6S5$#k##'##+##-##/##3##5#(L;#s#S,C#E7M%s$k001S$S5'#223S5)s$o,C3E4#.S#/#5S#6S6$#k##'##*##,##.##1##3#'CCS4S:%S%I'CCS%#%S-G'CCS-#&s$d#s$^&s$e&#&s$f)#-#s%.s%(j#$D#&DS#L+D$#j##/#(S#7M#s%.0;1S$S6%#2=3S6's%2,C>E4#.S2/#5S26SD$#k##'##*##,##.##1#(S2;#s$),C#E(S17M#s%B.S10#1S$S)&#2%3S)(s%G/',C#E4#.S+/#5S+6O$#k##'##+##-##/##3#(S+7M#s%U0-1S$O%#2/3O's%Y,C0E4#.S,/#5S,6S7$#k##'##*##,##.##1#'CCS)SD%S6I'CCS6#%S5G'CCS5#&s%M#s%G&s%N&#&s%O)#-#s%ss%mj#$D#&DS,S++D$#j##/#(S,091S$S7$#2;3S7&s%v,C<E4#.S3/#5S36S.$#k##'##*##,##.#(S37M#s&&(S-.S-0#1S$S;%#2%3S;'s&,/',C#E4#.S%/#5S%6S@$#k##'##+##-##/#$s&7O%OI$#s&@)%#$s&;S)%S)G$#s&D)%##'#j#$D#YSPD#S%S-S,U$S%(S:%#s&E$#O$0%)$#$&S)$/()$##&#'CCS@S;%S.I'CCS.#%S7G'CCS7#&s&5#s&/&s&6&#&s&7)#-#s&[s&Uj#$D#&DS4S:+D$#j##/#(S4%#s&[$#O%OG$#&)%#(S5%#s&a$#S.$7%)$#(S6%#s&f$#S.%S.G$#&)%#(SD>SEUSNSEUSfCUSgCUShCVSRCEVSRCs&r<C$S<#=&S&HHP#S=VSi'PVSjSSSTVSkFK,SS#STm$%#WSlCEJXSmFK$#l#(*)#l#)10#l#*43#$Es'#l#+$#Fm##$YSnM9s'&N#$SF:%;s'($#s'1*$S'*E>USoM$s'5##%##'##)##,#(S)$SF#%$s'4$#s'=*$S'*E'##-#%##'##*#'CCSUSG%SAI'CCSA#%SHG'CCSH#&s'$#s&z&s'%&#&s'&)#-#s'Js'Dj#$D#&DOS)+D$#j##/#(O%#s'J$#s'S*$S'*E&##s###%##'#(S7$SF#(S.%#s'T$#s']*$S'*E&##s#-#%##'#(S;%#s'\$#s'e*$S'*E&##s#5#%##'#'CCSISJ%S>I'CCS>#%SKG'CCSK#&s'K#s'E&s'L&#&s'M)#-#s'qs'kj#$D#&DS@S;+D$#j##/#(S@%#s'q*#S'*E%##s#I#%#(Sp%#s'w$#s($(SH%#s'z*#S'*E%##s#R#%#(SA%#s($*#S'*E%##s#X#%#'CCSqSV%S8I'CCS8#%S?G'CCS?#&s'm#s'g&s'n&#&s'o)#-#s(7s(1j#$D#&DSGSA+D$#j##/#(SG*E###s#i(SU%#s(:*#S'(SK*E###s#o(S>*E###s#r'CCS*SB%SLI'CCSL#%SWG'CCSW#&s(*#s($&s(+&#&s(,)#-#s(Ps(Jj#$D#&DSJS>+D$#j##/#(SI*E#'CCSXSM%S9I'CCS9#%S*G'CCS*#&s(9#s(3&s(:&#&s(;)#-#s(_s(Yj#$D#(S8%#s(\$#SM$S9%)$#$&S*%S*I$#))%#$*SB%SBG$#-)%###SY#(#USZS[USZ#?C#?C%?CS[WS\C$#WS\C&#VSr#Ss&SE#s$dVS]CKVS]CS(XStC$J#@CSCWS^C#s$c@Cs(}<C$S<#=s$hS&HHP#S=USuH@Cs'i<C'S<#=s$lS&HHP#S=<C*S<%=s$nS&HHP#S=As$oS&HHP%(#As$pS&HHP*)#l#(#s$ls$fl#)1s$s#l#*5s$v#j#,C#j#-C#j#.C#%Fs)-$#K$S(K%Ks)0$#S(k##%#k##'#k#,C#k#-C#k#.C#(SVYFs)@SX#S#SLl#+/%#m##s#;WSvs#<s#;#WS^C>B<C#S<s#%=s%,S&HHP#S=[Sws%-S&HHP=#As%.S&HHP#s###l#(#s%*s%$l#)s#+s%1#l#*s%5s%4#j#,C#j#-C#j#.C#$<J%JK$#F)%#%Js)K$#K%KS($#J)%#k##(#k#,C#k#-C#k#.C#XFIS9?S4l#+1$#m##s#QXFGS*BS:l#+4'#m##s#PBs#QSY#SxBs#Vs#Q'#Bs#[s#Qs###'CCSMS9'CCS*s#['CCSBs#X&s)C#s)=&s)D%#&s)E'#-#s#fs)cm#*#$s)dS9$s#rs)l)$#$s)gS*$s#ss)o)$##&#j#$D#YS_D#S8S?SJ:SyYS_D#S8S?S>VSI%#ZSzDs#uS8S?/#j#/s%G#j#0s$%#V#JFj##s%J#j##s$8#8s$9s%Ls$+#Fj#1s$<#j#2s$@#V#JFj##s$E#j##s$Y#8s$Zs$Xs$J#Fj#1s$^#j#3s$e#V#JFj##s$j#j##s%'#8s%(s%$s$r#Fj#1s%,#j#4s%5#V#JFj##s%9#j##s%W#8s%Xs%Qs%C#Fl#1s%fs%[#j#5s&##j#6s&*#V#JFj##s&1#j##s&I#8s&Js&Gs&9#Fl#1s&Qs&P#j#7s&]#j#8s&o#V#JFj##s&s#j##s'C#8s'Ds'6s'(#Fj#1s'G#j#9s'[#V#JFj##s'`#j##s(4#8s(5s(%s's#Fj#1s(9#j#:s(P#V#JFj##s(T#j##s)4#8s)5s(xs(j#Fl#1s)9s)8#j#%s)<#j#&s)@#j#;s)J#j#'s*V#j#$D#[S{Ds)~s)d#QJFl#%s*Bs*@#j#&s*D#j#<s*X#j#=s*[#j#>C#j#?C#j#@C#j#AC#j#'s*a#j#BC#j#CS|##"). Qed.

Section W.
  Variable H : asr.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ADAS_STACK : Z := 144 + AINTRIN_STACK.

Definition das_W (lo : Z) (sp : word) (r svc ff fp : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (r, r + SZ_REG); (svc, svc + SZ_SVC);
   (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 128); (sh ff, sh ff + 16)]%Z.

Definition do_add_service_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LB : list block) (LF : list fframe) (r svc owner first kti kid lo shi : Z) (S0 : svch) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ff fp : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (das_W lo sp r svc ff fp) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ ARegistry LB m' r owner svc 0
    /\ rw_cells bsegs m' svc (SvcHdrCells (mkSVC (sv_vptr S0) kti kid owner first (sv_destroy S0)))
    /\ fresh_frame H LF 1 ff fp /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi.

Definition do_add_service_stmt : Prop :=
  forall (r K svc lo shi : Z) (LB : list block) (LF : list fframe) (L : list svce) (S0 : svch) (owner first kti kid kname : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  ARegistry LB m r owner first 0 ->
  rw_cells bsegs m svc (SvcHdrCells S0) -> svch_ok S0 -> sv_owner S0 = owner -> sv_destroy S0 <> 0 ->
  ro_cells bsegs m K [C8 (wz kti); C8 (wz kid)] -> 0 <= kti < 2^64 -> 0 <= kid < 2^64 -> 0 <= kname < 2^64 ->
  (kti <> 0 -> ati_ok m kti kname) ->
  ASvcChain m first L -> Forall (fun e => keys_match kti kid kname e = false) L ->
  Forall (fun e => fsobj H LF (se_addr e) 48 /\ (se_addr e + 48 <= r \/ r + SZ_REG <= se_addr e)
                   /\ (se_addr e + 48 <= svc \/ svc + SZ_SVC <= se_addr e)) L ->
  bv_unsigned sp <= K -> K + 80 <= shi -> K mod 8 = 0 ->
  (r + NEWSZ_REG <= svc \/ svc + SZ_SVC <= r) ->
  stk bsegs m lo (bv_unsigned sp) -> lo + ADAS_STACK <= bv_unsigned sp -> aceil <= lo ->
  bv_unsigned ra mod 2 = 0 ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  bv_unsigned sp mod 16 = 0 -> tp = Z_to_bv 64 ATP -> ACONST m -> athr_cells m ->
  as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat ->
  stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->
  fsobj H LF r NEWSZ_REG ->
  aapp svc SZ_SVC -> fsobj H LF svc SZ_SVC -> accessible m svc SZ_SVC -> shvis m svc (svc + SZ_SVC) -> svc mod 8 = 0 ->
  (* [comment removed for export] *)
  0 < owner -> owner mod 8 = 0 ->
  evt bsegs (do_add_service_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB LF r svc owner first kti kid lo shi S0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) (wz K) (wz svc) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_DO_ADD_SERVICE) fc None m (seg_rom bsegs)).

End W.
End HCW.
