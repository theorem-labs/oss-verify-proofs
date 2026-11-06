(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanAllocModel AllocSim MmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocWalkKit.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AW_LargeAlloc1 AW_PoisonRemap1 SecLazy.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition wmono_out (X : list ivl) (m m' : mem) : Prop :=
  forall x : word, outside X (bv_unsigned x) -> wview asegs m x <> None -> wview asegs m' x <> None.

Lemma wmono_out_of_wmono : forall X m m', wmono asegs m m' -> wmono_out X m m'.
Proof. intros X m m' WM x _ Hx. exact (WM x Hx). Qed.

Lemma wmono_out_refl : forall X m, wmono_out X m m.
Proof. intros X m x _ Hx. exact Hx. Qed.

Lemma wmono_out_trans : forall X m1 m2 m3, wmono_out X m1 m2 -> wmono_out X m2 m3 -> wmono_out X m1 m3.
Proof. intros X m1 m2 m3 A B x Ho Hx. exact (B x Ho (A x Ho Hx)). Qed.

Lemma wmono_out_wmono_l : forall X m1 m2 m3, wmono asegs m1 m2 -> wmono_out X m2 m3 -> wmono_out X m1 m3.
Proof. intros X m1 m2 m3 A B. eapply wmono_out_trans; [apply wmono_out_of_wmono; exact A| exact B]. Qed.

Lemma wmono_out_wmono_r : forall X m1 m2 m3, wmono_out X m1 m2 -> wmono asegs m2 m3 -> wmono_out X m1 m3.
Proof. intros X m1 m2 m3 A B. eapply wmono_out_trans; [exact A| apply wmono_out_of_wmono; exact B]. Qed.

(* [comment removed for export] *)
Lemma wmono_out_weaken : forall X X' m m', sub_fp X X' -> wmono_out X m m' -> wmono_out X' m m'.
Proof. intros X X' m m' SUB A x Ho Hx. exact (A x (SUB _ Ho) Hx). Qed.

(* [comment removed for export] *)
Lemma wview_pointwise : forall (m m' : mem) (x : word), m' x = m x -> wview asegs m' x = wview asegs m x.
Proof. intros m m' x E. unfold wview. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Lemma munch_wmono_out : forall W m m', munch W m m' -> wmono_out W m m'.
Proof. intros W m m' MU x Ho Hx. rewrite (wview_pointwise m m' x (MU x Ho)). exact Hx. Qed.

Lemma unfill_wmono_out : forall (a n : word) (m : mem),
  wmono_out [(bv_unsigned a, bv_unsigned a + bv_unsigned n)] m (unfill a n m).
Proof. intros a n m. apply munch_wmono_out. apply unfill_munch. Qed.

(* [comment removed for export] *)
Lemma unfill_none : forall (a n : word) (m : mem) (x : word),
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> unfill a n m x = None.
Proof.
  intros a n m x Hx. unfold unfill.
  destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned a + bv_unsigned n)); cbn [andb];
    try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma none_range_munch : forall W (m m' : mem) (lo hi : Z),
  (forall x : word, lo <= bv_unsigned x < hi -> m x = None) -> munch W m m' -> disjoint_from W lo (hi - lo) ->
  forall x : word, lo <= bv_unsigned x < hi -> m' x = None.
Proof.
  intros W m m' lo hi N MU D x Hx. rewrite (MU x); [exact (N x Hx)|].
  eapply disjoint_outside; [exact D| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section MuTransport.
  Variables (W : list ivl) (m m' : mem).
  Hypothesis MU : munch W m m'.

  Lemma wr_at_transport_mu : forall A n, wr_at asegs m A n -> disjoint_from W A n -> wr_at asegs m' A n.
  Proof.
    intros A n (Ha & Hn & H) D. split; [exact Ha|]. split; [exact Hn|]. intros i Hi.
    rewrite (wview_pointwise m m'); [exact (H i Hi)|]. apply MU. eapply disjoint_outside; [exact D|]. rewrite wa_unsigned by lia. lia.
  Qed.

  Lemma rw_cells_transport_mu : forall A cs,
    rw_cells asegs m A cs -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs.
  Proof.
    intros A cs [[Hwf Hb] Hw] D. split; [split; [exact Hwf|]|].
    - eapply bytes_at_transport; [exact Hb| exact MU|]. rewrite cells_bytes_length by assumption. exact D.
    - eapply wr_at_transport_mu; [exact Hw| exact D].
  Qed.

  Lemma stk_transport_mu : forall lo hi, stk asegs m lo hi -> disjoint_from W lo (hi - lo) -> stk asegs m' lo hi.
  Proof.
    intros lo hi (H1 & H2 & H) D. split; [exact H1|]. split; [exact H2|]. intros a Ha.
    assert (E : m' (wa a) = m (wa a)) by (apply MU; eapply disjoint_outside; [exact D|]; rewrite wa_unsigned by lia; lia).
    destruct (H a Ha) as [Hw (b & Hb)]. split.
    - rewrite (wview_pointwise m m' (wa a) E). exact Hw.
    - exists b. unfold mrd in *. rewrite E. exact Hb.
  Qed.

  Lemma u8arr_transport_mu : forall A bs, u8arr asegs m A bs -> disjoint_from W A (Z.of_nat (length bs)) -> u8arr asegs m' A bs.
  Proof.
    intros A bs [Hb Hw] D. split; [eapply bytes_at_transport; [exact Hb| exact MU| exact D]| eapply wr_at_transport_mu; [exact Hw| exact D]].
  Qed.

  Lemma u64arr_transport_mu : forall A ws, u64arr asegs m A ws -> disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
  Proof.
    intros A ws [Hb Hw] D. split.
    - eapply bytes_at_transport; [exact Hb| exact MU|]. rewrite u64s_length, Nat2Z.inj_mul. exact D.
    - eapply wr_at_transport_mu; [exact Hw| exact D].
  Qed.
Scheme kc__1 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.As.AW_LargeAlloc1.SENV Sort Prop.

  Lemma senv_transport_mu : forall tp TSD CTX TH,
    SENV tp TSD CTX TH m ->
    disjoint_from W 1215712 8 -> disjoint_from W (bv_unsigned tp + -88) 8 -> disjoint_from W TSD 8 -> disjoint_from W (CTX + 152) 8 ->
    disjoint_from W 1215708 1 -> disjoint_from W 1160104 120 -> disjoint_from W 1217656 8 -> disjoint_from W 1220960 24 ->
    disjoint_from W 1814560 8 -> disjoint_from W 1814584 8 -> disjoint_from W 1814700 1 -> disjoint_from W 1168200 8 ->
    disjoint_from W 1806112 8 -> disjoint_from W 1168256 8 ->
    SENV tp TSD CTX TH m'.
  Proof.
    ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AW_LargeAlloc1.SENV); constr:(m); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(W); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@kc__1); constr:(m'); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.asegs); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.b8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.CB); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C4); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.wz); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C8); constr:(@Corelib.Lists.ListDef.map); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRep.AGOT_VALS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AW_LargeAlloc1.mkSENV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.SecLazy2.HCW.MuTransport.rw_cells_transport_mu); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size)|] [|@v; @se_name; @se_psc; @se_rms; @se_dpm; @se_mlim; @se_thresh; @se_hme; @se_shb; @se_got; @se_can; @se_ctx; @se_tsd; @se_tp; @se_tsdi; @E; @TH; @CTX; @TSD; @tp|] "#,]#R#m#]#Y#h#[#f#(###5#6#D#P#X#&#%#$#4#3#O#V#U#2#d#j#i#n#s#C#0#Q#/#.#N#-#,#+#*#)#'#b#m#k#p#t#L#K#J#I#H#G#F#E#B#A#@#?#u#c#1#W#_#g#^#\#e#x#w#v#q#r#`#a#Z#l#o3#]$#^$#_&#`$#a&#b'#c$#d$#e'#f$#g$#h%#i%#j(#k$#l$#N##########US%#US&#0OPQIF$*##$#######$#$#$###$###$###########&#&<#N##$###$#######$#$#####$#$#$###########&##*$#$#$#####&##=$#$###$#$#####$#$#$###$###$#######&#$s#+##$#######$#$#$#$#######&#$s#:########$###$#$###########&#$N##$#$#$###$#$#############$###########&#$)$#######&#$2##$###$#$#####&#$s#T##$#####$#$###$#####$#######&##s#1##$#$#$#$#####$###########&#$;##############&##s#~$#$###$#$###$#$###$#$#$#$#$#####&##s#]####$#$#$#$#$#$#$#$#$#&##s#2$#$#######&##s#n$#$#$#$#$#####$#$#$#####&#$s#=########&#$s#\$#$#######&##s#a######&#$s$?########&#$s$D######&##s%0$#$###$#$#######$#$#$#$#######&#$s#8##$#######&#'Cs%7s%L/s%cH$s%j$#######US9#.)#'C#s%U'CHs%V$s%j######&#.H#'C#s%]#s%f$#$#$#####&#&N'Cs%J#$s&%$###$#$###$###$###$#####$#######&#$N$#$#######&#'Cs%Q#$s&4##$#$#######$#$#$#######&#'Cs%Rs&3$s&D######$#$#####$###########&##s#(####&#'Cs%W#$'$#$###$#$#######$#$#$#$###########&#'Cs%Vs&[$*$#######&#'Cs%Ws&b$6####$#$###$#$#####&#'Cs%Zs#g$s#e##$###$#####$#$#$###$#######&#'Cs%[s'##s#7$#########$#$#$###########&#'Cs%\s'3$>####$###########&#'Cs%^s'>0JRS#S'F0KJRS#S(j##$#US)s$;US*#1S:1#1#US%s'aUS&#US)S+2$%%$#%&%#%'&#VS;*#,S+US<#2E%E$#%E'#%E3#(GFs'@#/s'lK.#s$b,J-#%E#+(GF&#(GFK$.Ks$`(GF#&%E>0(GFs'D#,I-#j#$D#XS,DE#S=(GFs'6#$s$I$#$#$#$#$#$#$#$#$#$#$###############################&#,#-#%E#s#5(GFs'H#$7$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#&#,#-#-s#[%E#s#Z%E$#%E&#(GFs'`#$+$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#&#,#-#%E#s#r(GFs'a#(GFs'\<US*s#}%E#s#v(GFs'V#$s)($###$#$#$###$#################&#,s'.-#%E#s$/(GFs'[##s);##########&#,#-#%E#s$:(GFs'W##s%D####$#$#$#$#$#$#$#$#$#&#,s'=-#%E#s$K(GFs'_#/s)VL.#s&L,S--#%E#s$Q(GF&#(GFL$.Ls&J(GF#&)s$S*#'Cs)6#m#S>#m##$+s)9s$XS.#/s)eS/.#s&[,M-#%E#s$`)#*#'C(#m#S?#m##$++(S0#,S$-#%E#s$i)#*#'CM#m#S@#m##$+M(S1#.S$s&f,S2-#%E#s$s)#*#'C(#m#SA#m##$++(S3#)s$l*#'Cs)S#m#SB#m##$+s)Vs$qS4##s&$$#$###$#######&##s*2$#$###$#$#$#######$#$#$#######&#$s&R######&#$s&X########&##s%}######&##s%i$#$#######&#$s%o########&##s#8$#$#$#####&##s&,$#$#######&#2D%Ds(W#%Ds(J#%Ds'X#%Ds(F#%Ds(@#%Ds(<#%Ds)?#%Ds)t#%Ds(9#%Ds(5#%Ds**#%Ds(&#%Ds'|#%Ds).#%Ds)8#XS,DEs%g#)#*#'Cs*@#m#SC#)s%k*#'Cs*D#m#&#+s*Fs%oS5#)s%P*#'Cs*;#m#SD#m##$+s*>s%US6#)s%/*#'Cs*2#m#SE#m##$+s*5s%4S7#)s${*#'Cs*##m#L#m##$+s*&s%$H#)s%=*#'Cs*##m#S-#m##$+s*&s%BS8#)s%'*#'Cs)|#m#SF#m##$+s*#s%,O#)s$t*#'Cs)r#m#SG#m##$+s)us$yP#)s$o*#'Cs)i#m#SH#m##$+s)ls$tQ#)s$d*#'Cs)f#m#SI#m##$+s)is$iI#gSJS/MS$S2S(s$Zs$Os$Fs$<s$6s#3s#-s#'A;5/)#j#%s$j#j#&s$|#j#'s%,#j#(s%B#j#)s%F#j#*s%H#j#+s%_#j#,s&+#j#-s&L#j#.s&R#j#/s$k#j#0s$n#j#1s$p#j#2s&a#b#S.S0S1S3S4S5S6S7HS8OPQIj#%s$y#j#&s%/#j#'s%;#j#(s%Q#j#)s%U#j#*s%W#j#+s%n#j#,s&:#j#-s&[#j#.s&a#j#/s&d#j#0s&g#j#1s&i#j#2s&p#\SKJRS#S'Fs')#SLj##s'-#j##s'9#j##s'J#j##s'\#j##s'i#j##s'q#j##s(*#j##s(?#j##s(O#j##s(j#j##s(t#j##s(|#j##s(~#j##s),#j#3s,/#j#4D#j#5D#j#6D#j#7s,4##"). Qed.
Scheme kc__2 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.As.AW_PoisonRemap1.RENV Sort Prop.

  Lemma renv_transport_mu : forall g b,
    RENV g b m ->
    disjoint_from W 1160104 120 -> disjoint_from W 1217656 8 -> disjoint_from W 1220960 24 -> disjoint_from W 1814560 8 ->
    disjoint_from W 1814584 8 -> disjoint_from W 1814659 1 -> disjoint_from W 1814684 1 -> disjoint_from W 1168200 8 ->
    disjoint_from W 1806112 8 -> disjoint_from W 6805360 8 -> disjoint_from W 1163568 8 -> disjoint_from W 6804720 8 ->
    RENV g b m'.
  Proof.
    ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AW_PoisonRemap1.RENV); constr:(m); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(W); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@kc__2); constr:(m'); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.asegs); constr:(@Corelib.Lists.ListDef.map); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.wz); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocRep.AGOT_VALS); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.b8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AW_PoisonRemap1.mkRENV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.SecLazy2.HCW.MuTransport.rw_cells_transport_mu); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size)|] [|@v; @re_grd; @re_ssp; @re_lpg; @re_psc; @re_rms; @re_madv; @re_dd; @re_mlim; @re_thresh; @re_hme; @re_shb; @re_got; @E; @b; @g|] "#,>#J#_#T#\#]#R#Z###P#$#1#H#N#M#0#X#[#b#<#B#.#-#,#+#*#)#(#'#&#%#I#2#`#c#e#6#F#E#D#C#A#@#?#>#=#;#f#W#/#O#V#U#a#S#Y#i#h#g#^#_#d#Q0#R$#S$#T$#U&#V&#W'#X$#Y$#Z'#[$#\$#]$#^&#I##########UM#UN#UM(UN#/JHF$+$###$#$###$###$###$#####$#######%#$I$#$#######%##I####$#$###$#$#####$#$#$###$###$#######%#$6##$#####$###$#######$#$#$#$#######%#$2########$###$#$###########%#$I##$#$#$###$#$#############$###########%#$)$#######%#$2##########$#$#%#$)$#$#####%#$s#_##$#####$#$###$#####$#######%##s#7##$#$#$#$#####$###########%##s#J$#$#$#$#$###$###$#$#$###$#$#$#########%##s#5######$#####$#$#########%##<##$#$#$#$#########%##s$R$#$###$#$###$#$###$#$#$#$#$#####%##s#J$#$#######%##s$0$#$#$#$#$#####$#$#$#####%#$s#p####$#########%#$s#w$#$#######%##s#|######%#$s$`########%#$s$e######%##s%)$#$###$#$#######$#$#$#$#######%#$s#;##$#######%##s#8########%#'Cs%Is%^$s&%##$#####$###$#$#######$#$#$#######%#%s&7'Cs%K#$4######$#$#####$###########%##s&-####%#'Cs%P#$'$#$###$#$#######$#$#$#$###########%#'Cs%Os#+$*$#######%#'Cs%Ps#2$6####$#########$#$#%#%I'Cs%T#$+$#$#####%#'Cs%U*$s&r##$###$#####$#$#$###$#######%#'Cs%Vs#W#s#?$#########$#$#$###########%#'Cs%Ws#g$s#V##$#$#$###$#$#####$#$###$#$#########%#'Cs%Ws#|#s#7####$###$#$###$#########%#'Cs%Xs$/#@$#$#$#####$#$#########%#'Cs%[s$=/KOF/S0KPj##$#-H,#j#$D#XQDE#S1(GFs'D#$s'^$#$#$#$#$#$#$#$#$#$#$###############################%#-#,#URE&E$#(GFs'R#$8$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#%#-#,#-S2,#&E#s#)&E$#&E'#(GFs'k#$,$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#%#-#,#&E#s#A(GFs'l#(GFs'g<US3s$j.#&E#s#F(GFs'b#.S4&E#s#I(GFs'_#$s))$###$#$#$###$#################%#-s&n,#&E#s#^(GFs'd##s)<##########%#-#,#&E#s#i(GFs'`#(GFs'L$-s'4,#&E#s#n(GFs'B#,S#&E#s#q(GFs':#.S$&E#s#t(GFs(.#,L&E#s#w(GFs'@#$s%5####$###########%##s%j$#$###$#######%##s&H$#$###$#$#$#######$#$#$#######%#$s&<######%#$s&B########%##s%_######%##s#4$#$#######%#$s#:########%##s#8$#$#$#####%##s%j$#$#######%#URD&Ds'x#&Ds'k#&Ds&9#&Ds'd#&Ds'^#&Ds'Z#&Ds(x#&Ds)W#&Ds'W#&Ds'S#&Ds)i#&Ds'D#&Ds'>#&Ds'9#&Ds(q#XQDEs%A#)#*#'Cs*(#m#S5#)s%E*#'Cs*,#m#&#+s*.s%IS%#)s%)*#'Cs)z#m#S6#m##$+s)}s%.S&#)s$c*#'Cs)q#m#S7#m##$+s)ts$hS'#)s$S*#'Cs)b#m#S8#m##$+s)es$XS(#)s$q*#'Cs)b#m#S$#m##$+s)es$vS)#)s$Z*#'Cs)_#m#S9#m##$+s)bs$_S*#.L&E#s%I)#*#'Cs)a#m#S:#m##$+s)d(S+#)s$P*#'Cs)W#m#S;#m##$+s)Zs$US,#)s$K*#'Cs)N#m#S<#m##$+s)Qs$PS-#'Cs)='m#S=#m##$+s)@s$TS.#)s$P*#'Cs)5#m#S##m##$+s)8s$UJ#,S/&E#s%g)#*#'Cs)2#m#S>#m##$+s)5(H#cS?S/LPs#Gs#As#;s#5s#/s#)A;51+#j#%s$U#j#&s$_#j#'s$d#j#(s$f#j#)s$r#j#*s$]#j#+s%0#j#,s%5#j#-s%7#j#.s%N#j#/s%w#j#0s&=#`#S%S&S'S(S)S*S+S,S-S.JHj#%s$h#j#&s$l#j#'s$q#j#(s$s#j#)s%##j#*s%9#j#+s%=#j#,s%B#j#-s%D#j#.s%[#j#/s&(#j#0s&J#ZS@KOFs&P#SAj##s&T#j##s&c#j##s&s#j##s'-#j##s'>#j##s'P#j##s'X#j##s'f#j##s'n#j##s('#j##s(<#j##s(R#j#1s+l#j#2s+n#j#3s+q##"). Qed.
End MuTransport.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rem_uncovered : forall (e : word * word) (C : list (word * word)),
  (forall x, lo e <= x < hi e -> zcovb C x = false) -> rem e C = bv_unsigned (snd e).
Proof.
  intros e C H. unfold rem. rewrite <- hi_minus_lo. apply zmeasure_all; [apply lo_hi|].
  intros x Hx. rewrite (H x Hx). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zcovb_maps_subtract_false : forall C l h x,
  entries_nowrap C -> 0 <= l -> l <= h -> zcovb C x = false -> zcovb (maps_subtract C l h) x = false.
Proof. intros C l h x NW Hl Hlh H. rewrite (zcovb_maps_subtract C l h x NW Hl Hlh), H. reflexivity. Qed.

Lemma zcovb_app_false : forall C1 C2 x, zcovb C1 x = false -> zcovb C2 x = false -> zcovb (C1 ++ C2) x = false.
Proof. intros C1 C2 x H1 H2. rewrite zcovb_app, H1, H2. reflexivity. Qed.

Lemma zcovb_cons_false : forall c C x, zin_rangeb x c = false -> zcovb C x = false -> zcovb (c :: C) x = false.
Proof. intros c C x H1 H2. rewrite zcovb_cons, H1, H2. reflexivity. Qed.

(* [comment removed for export] *)
Lemma in_rangesb_false_zcovb : forall (C : list (word * word)) (x : Z),
  0 <= x < 2^64 -> in_rangesb (wz x) C = false -> zcovb C x = false.
Proof. intros C x Hx H. rewrite in_rangesb_zcovb in H. unfold wz in H. rewrite unsigned_lit in H by lia. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ecall_85b10 : fetch_word asegs (Z_to_bv 64 0x085998) = Some ECALLW.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.option); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.Some); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@stdpp.bitvector.definitions.Z_to_bv_obligation_1); constr:(@Corelib.Init.Logic.eq); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.asegs); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.SecLazy.ECALLW)|] Array.empty "##a###3#+#)#.#,#(#'#0#-#&#4#2#3#5#1#*#/%#1$#2$#C########UD#UG#UH#$C$#####$#$#UE#VI,#WJ-$#VF-#VK-##1UD#$4##$#$###$#$#######$#########UE##C######$###$#$#####$#$#####$#$#######UE#VLs#'#VMN#VFs#7OWPs#7$#m$s#-##"). Qed.

End HCW.

