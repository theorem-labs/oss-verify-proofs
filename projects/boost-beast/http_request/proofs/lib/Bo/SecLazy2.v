(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
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
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AllocWf AllocKit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AllocRep AllocWalkKit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AW_LargeAlloc1 AW_PoisonRemap1 SecLazy.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition wmono_out (X : list ivl) (m m' : mem) : Prop :=
  forall x : word, outside X (bv_unsigned x) -> wview bsegs m x <> None -> wview bsegs m' x <> None.

Lemma wmono_out_of_wmono : forall X m m', wmono bsegs m m' -> wmono_out X m m'.
Proof. intros X m m' WM x _ Hx. exact (WM x Hx). Qed.

Lemma wmono_out_refl : forall X m, wmono_out X m m.
Proof. intros X m x _ Hx. exact Hx. Qed.

Lemma wmono_out_trans : forall X m1 m2 m3, wmono_out X m1 m2 -> wmono_out X m2 m3 -> wmono_out X m1 m3.
Proof. intros X m1 m2 m3 A B x Ho Hx. exact (B x Ho (A x Ho Hx)). Qed.

Lemma wmono_out_wmono_l : forall X m1 m2 m3, wmono bsegs m1 m2 -> wmono_out X m2 m3 -> wmono_out X m1 m3.
Proof. intros X m1 m2 m3 A B. eapply wmono_out_trans; [apply wmono_out_of_wmono; exact A| exact B]. Qed.

Lemma wmono_out_wmono_r : forall X m1 m2 m3, wmono_out X m1 m2 -> wmono bsegs m2 m3 -> wmono_out X m1 m3.
Proof. intros X m1 m2 m3 A B. eapply wmono_out_trans; [exact A| apply wmono_out_of_wmono; exact B]. Qed.

(* [comment removed for export] *)
Lemma wmono_out_weaken : forall X X' m m', sub_fp X X' -> wmono_out X m m' -> wmono_out X' m m'.
Proof. intros X X' m m' SUB A x Ho Hx. exact (A x (SUB _ Ho) Hx). Qed.

(* [comment removed for export] *)
Lemma wview_pointwise : forall (m m' : mem) (x : word), m' x = m x -> wview bsegs m' x = wview bsegs m x.
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

  Lemma wr_at_transport_mu : forall A n, wr_at bsegs m A n -> disjoint_from W A n -> wr_at bsegs m' A n.
  Proof.
    intros A n (Ha & Hn & H) D. split; [exact Ha|]. split; [exact Hn|]. intros i Hi.
    rewrite (wview_pointwise m m'); [exact (H i Hi)|]. apply MU. eapply disjoint_outside; [exact D|]. rewrite wa_unsigned by lia. lia.
  Qed.

  Lemma rw_cells_transport_mu : forall A cs,
    rw_cells bsegs m A cs -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells bsegs m' A cs.
  Proof.
    intros A cs [[Hwf Hb] Hw] D. split; [split; [exact Hwf|]|].
    - eapply bytes_at_transport; [exact Hb| exact MU|]. rewrite cells_bytes_length by assumption. exact D.
    - eapply wr_at_transport_mu; [exact Hw| exact D].
  Qed.

  Lemma stk_transport_mu : forall lo hi, stk bsegs m lo hi -> disjoint_from W lo (hi - lo) -> stk bsegs m' lo hi.
  Proof.
    intros lo hi (H1 & H2 & H) D. split; [exact H1|]. split; [exact H2|]. intros a Ha.
    assert (E : m' (wa a) = m (wa a)) by (apply MU; eapply disjoint_outside; [exact D|]; rewrite wa_unsigned by lia; lia).
    destruct (H a Ha) as [Hw (b & Hb)]. split.
    - rewrite (wview_pointwise m m' (wa a) E). exact Hw.
    - exists b. unfold mrd in *. rewrite E. exact Hb.
  Qed.

  Lemma u8arr_transport_mu : forall A bs, u8arr bsegs m A bs -> disjoint_from W A (Z.of_nat (length bs)) -> u8arr bsegs m' A bs.
  Proof.
    intros A bs [Hb Hw] D. split; [eapply bytes_at_transport; [exact Hb| exact MU| exact D]| eapply wr_at_transport_mu; [exact Hw| exact D]].
  Qed.

  Lemma u64arr_transport_mu : forall A ws, u64arr bsegs m A ws -> disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr bsegs m' A ws.
  Proof.
    intros A ws [Hb Hw] D. split.
    - eapply bytes_at_transport; [exact Hb| exact MU|]. rewrite u64s_length, Nat2Z.inj_mul. exact D.
    - eapply wr_at_transport_mu; [exact Hw| exact D].
  Qed.
Scheme kc__1 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_LargeAlloc1.SENV Sort Prop.

  Lemma senv_transport_mu : forall tp TSD CTX TH,
    SENV tp TSD CTX TH m ->
    disjoint_from W 1232928 8 -> disjoint_from W (bv_unsigned tp + -88) 8 -> disjoint_from W TSD 8 -> disjoint_from W (CTX + 152) 8 ->
    disjoint_from W 1232924 1 -> disjoint_from W 1177192 120 -> disjoint_from W 1234872 8 -> disjoint_from W 1238176 24 ->
    disjoint_from W 1831776 8 -> disjoint_from W 1831800 8 -> disjoint_from W 1831916 1 -> disjoint_from W 1185288 8 ->
    disjoint_from W 1823328 8 -> disjoint_from W 1185344 8 ->
    SENV tp TSD CTX TH m'.
  Proof.
    ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_LargeAlloc1.SENV); constr:(m); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(W); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@kc__1); constr:(m'); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.b8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.CB); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C4); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.wz); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C8); constr:(@Corelib.Lists.ListDef.map); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.AGOT_VALS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_LargeAlloc1.mkSENV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.SecLazy2.HCW.MuTransport.rw_cells_transport_mu); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size)|] [|@v; @se_name; @se_psc; @se_rms; @se_dpm; @se_mlim; @se_thresh; @se_hme; @se_shb; @se_got; @se_can; @se_ctx; @se_tsd; @se_tp; @se_tsdi; @E; @TH; @CTX; @TSD; @tp|] "#,Q#R#m#]#Y#h#[#f#(###5#6#D#P#X#&#%#$#4#3#O#V#U#2#d#j#i#n#s#C#0#Q#/#.#N#-#,#+#*#)#'#b#m#k#p#t#L#K#J#I#H#G#F#E#B#A#@#?#u#c#1#W#_#g#^#\#e#x#w#v#q#r#`#a#Z#l#o3#]$#^$#_&#`$#a&#b'#c$#d$#e'#f$#g$#h%#i%#j(#k$#l$#N##########US%#US&#0OPQIF$*##$#$###$#######$#$#$#$###########&#&<#N##$###$#$###$#############$###########&##*$#$#$#####&##=$#$#$#$#$###$#$#####$#$###$#######&#$s#)$#$#$###$#$#$#######&#$s#8####$#####$###$###########&#$N##$#$#$#$#$#$#####$#$###$#$###########&#$)$#######&#$2$#$###$#$#####&##s#m####$###$#$###########$#######&##s#2$#####$#####$#$###########&#$:############&##s#{####$#$#$#$###$###$#$#$#######&##s#\##$###$###$#$#$#$#####&##s#0$#$#######&##s#i$#$###$#$#$#####&#$s#8########&#$s#V$#$#######&##s#[######&#$s$:########&#$s$?######&##s%($###$#$#$#$#$###$#$#$#######&#$s#7##$#######&#'Cs%/s%D/s%[H$s%b$#######US9#.)#'C#s%M'CHs%N$s%b######&#.H#'C#s%U#s%^$#$#$#####&#&N'Cs%B#$s%y$#$#$#$#$###############$#######&#$N$#$#######&#'Cs%I#$s&+####$###$#$#$#$#######&#'Cs%Ks&*$s&;####$#$#####$#$###########&##s#'####&#'Cs%P#$'$#$#$#$#$###$###$#####$###########&#'Cs%Os&R$*$#######&#'Cs%Ps&Y$4##$###$#$#####&#'Cs%Qs#d#s&v####$###$#$#$#$###$###$#######&#'Cs%Rs&u#s#6$###$#########$###########&#'Cs%Ss')$<$###########&#'Cs%Ts'20JRS#S'F0KJRS#S(j##$#US)s$7US*#1S:1#1#US%s'UUS&#US)S+2$%%$#%&%#%'&#VS;*#,S+US<#2E%E$#%E'#%E3#(GFs'4#/s'`K.#s$^,J-#%E#+(GF&#(GFK$.Ks$\(GF#&%E>0(GFs'8#,I-#j#$D#XS,DE#S=(GFs'*#$s$E$#$#$#$#$#$#$#$#$#$#$###############################&#,#-#%E#s#5(GFs'>#$7$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#&#,#-#-s#[%E#s#Z%E$#%E&#(GFs'V#$+$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#&#,#-#%E#s#r(GFs'W#(GFs'R<US*s#}%E#s#v(GFs'L##s%^##$#############$#######$#####&#,s'%-#%E#s$/(GFs'P##s)/##########&#,#-#%E#s$:(GFs'L##s%A##$###$###$#$#$#$#####&#,s'4-#%E#s$K(GFs'U#/s)JL.#s&H,S--#%E#s$Q(GF&#(GFL$.Ls&F(GF#&)s$S*#'Cs)*#m#S>#m##$+s)-s$XS.#/s)YS/.#s&W,M-#%E#s$`)#*#'C(#m#S?#m##$++(S0#,S$-#%E#s$i)#*#'CM#m#S@#m##$+M(S1#.S$s&b,S2-#%E#s$s)#*#'C(#m#SA#m##$++(S3#)s$l*#'Cs)G#m#SB#m##$+s)Js$qS4##s%~$###$###$#######&##s*&$#$#######$###$#$#$#$#######&#$s&O######&#$s&U########&##s%{######&##s%i$#$#######&#$s%o########&##s#7$#$#$#####&##s&*$#$#######&#2D%Ds(N#%Ds(E#%Ds'T#%Ds(A#%Ds(;#%Ds(7#%Ds)4#%Ds)j#%Ds(4#%Ds(0#%Ds)|#%Ds'~#%Ds'x#%Ds)$#%Ds)-#XS,DEs%g#)#*#'Cs*4#m#SC#)s%k*#'Cs*8#m#&#+s*:s%oS5#)s%P*#'Cs*1#m#SD#m##$+s*4s%US6#)s%/*#'Cs*(#m#SE#m##$+s*+s%4S7#)s${*#'Cs)u#m#L#m##$+s)xs%$H#)s%=*#'Cs)u#m#S-#m##$+s)xs%BS8#)s%'*#'Cs)r#m#SF#m##$+s)us%,O#)s$t*#'Cs)g#m#SG#m##$+s)js$yP#)s$o*#'Cs)^#m#SH#m##$+s)as$tQ#)s$d*#'Cs)\#m#SI#m##$+s)_s$iI#gSJS/MS$S2S(s$Zs$Os$Fs$<s$6s#3s#-s#'A;5/)#j#%s$j#j#&s$|#j#'s%,#j#(s%B#j#)s%F#j#*s%H#j#+s%_#j#,s&+#j#-s&L#j#.s&R#j#/s$k#j#0s$n#j#1s$p#j#2s&a#b#S.S0S1S3S4S5S6S7HS8OPQIj#%s$y#j#&s%/#j#'s%;#j#(s%Q#j#)s%U#j#*s%W#j#+s%n#j#,s&:#j#-s&[#j#.s&a#j#/s&d#j#0s&g#j#1s&i#j#2s&p#\SKJRS#S'Fs')#SLj##s'-#j##s'7#j##s'H#j##s'[#j##s'f#j##s'n#j##s('#j##s(<#j##s(K#j##s(f#j##s(p#j##s(x#j##s(z#j##s)(#j#3s,##j#4D#j#5D#j#6D#j#7s,(##"). Qed.
Scheme kc__2 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_PoisonRemap1.RENV Sort Prop.

  Lemma renv_transport_mu : forall g b,
    RENV g b m ->
    disjoint_from W 1177192 120 -> disjoint_from W 1234872 8 -> disjoint_from W 1238176 24 -> disjoint_from W 1831776 8 ->
    disjoint_from W 1831800 8 -> disjoint_from W 1831875 1 -> disjoint_from W 1831900 1 -> disjoint_from W 1185288 8 ->
    disjoint_from W 1823328 8 -> disjoint_from W 6822576 8 -> disjoint_from W 1180656 8 -> disjoint_from W 6821936 8 ->
    RENV g b m'.
  Proof.
    ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_PoisonRemap1.RENV); constr:(m); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(W); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@kc__2); constr:(m'); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@Corelib.Lists.ListDef.map); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.wz); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.AGOT_VALS); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.b8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_PoisonRemap1.mkRENV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.SecLazy2.HCW.MuTransport.rw_cells_transport_mu); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size)|] [|@v; @re_grd; @re_ssp; @re_lpg; @re_psc; @re_rms; @re_madv; @re_dd; @re_mlim; @re_thresh; @re_hme; @re_shb; @re_got; @E; @b; @g|] "#,3#J#_#T#\#]#R#Z###P#$#1#H#N#M#0#X#[#b#<#B#.#-#,#+#*#)#(#'#&#%#I#2#`#c#e#6#F#E#D#C#A#@#?#>#=#;#f#W#/#O#V#U#a#S#Y#i#h#g#^#_#d#Q0#R$#S$#T$#U&#V&#W'#X$#Y$#Z'#[$#\$#]$#^&#I##########UM#UN#UM(UN#/JHF$+$#$#$#$#$###############$#######%#$I$#$#######%##I####$#$#$#$#$###$#$#####$#$###$#######%#$6##$#$###$###$#$#$#$###$#$#$#######%#$2####$#####$###$###########%#$I##$#$#$#$#$#$#####$#$###$#$###########%#$)$#######%#$2$#########$#$#%#$)$#$#####%##s#M####$###$#$###########$#######%##s#8$#####$#####$#$###########%##s#J##########$#$###$###$###$#$#########%##s#4####$#$#$#$#$#$#########%##<######$#$#########%##s$Q####$#$#$#$###$###$#$#$#######%##s#H$#$#######%##s$+$#$###$#$#$#####%#$s#i##$#########%#$s#p$#$#######%##s#u######%#$s$Z########%#$s$_######%##s$~$###$#$#$#$#$###$#$#$#######%#$s#9##$#######%##s#7########%#'Cs%Bs%W$s%z##$#$###$#$#####$###$#$#$#$#######%#%s&0'Cs%D#$4####$#$#####$#$###########%##s&&####%#'Cs%I#$'$#$#$#$#$###$###$#####$###########%#'Cs%Hs#+$*$#######%#'Cs%Is#2$4##########$#$#%#%I'Cs%K#$+$#$#####%#'Cs%L*#s#W####$###$#$#$#$###$###$#######%#'Cs%Ms#V#s#>$###$#########$###########%#'Cs%Ns#f$s#U$#########$#$#$#####$#$#$#$#########%#'Cs%Os#{#s#7##$###$#$#####$#########%#'Cs%Ps$.#?$#####$#$#$#########%#'Cs%Rs$;/KOF/S0KPj##$#-H,#j#$D#XQDE#S1(GFs';#$s'U$#$#$#$#$#$#$#$#$#$#$###############################%#-#,#URE&E$#(GFs'I#$8$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#%#-#,#-S2,#&E#s#)&E$#&E'#(GFs'b#$,$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#%#-#,#&E#s#A(GFs'c#(GFs'^<US3s$j.#&E#s#F(GFs'Y#.S4&E#s#I(GFs'V##s(t##$#############$#######$#####%#-s&f,#&E#s#^(GFs'Z##s)3##########%#-#,#&E#s#i(GFs'V#(GFs'C$-s'+,#&E#s#n(GFs'9#,S#&E#s#q(GFs'1#.S$&E#s#t(GFs(%#,L&E#s#w(GFs'7#$s%2$###########%##s%g$###$###$#######%##s&D$#$#######$###$#$#$#$#######%#$s&8######%#$s&>########%##s%\######%##s#4$#$#######%#$s#:########%##s#7$#$#$#####%##s%g$#$#######%#URD&Ds'n#&Ds'e#&Ds&7#&Ds'_#&Ds'Y#&Ds'U#&Ds(l#&Ds)L#&Ds'R#&Ds'N#&Ds)^#&Ds'@#&Ds':#&Ds'5#&Ds(e#XQDEs%?#)#*#'Cs)y#m#S5#)s%C*#'Cs)}#m#&#+s*#s%GS%#)s%'*#'Cs)o#m#S6#m##$+s)rs%,S&#)s$a*#'Cs)f#m#S7#m##$+s)is$fS'#)s$Q*#'Cs)W#m#S8#m##$+s)Zs$VS(#)s$o*#'Cs)W#m#S$#m##$+s)Zs$tS)#)s$X*#'Cs)T#m#S9#m##$+s)Ws$]S*#.L&E#s%G)#*#'Cs)V#m#S:#m##$+s)Y(S+#)s$N*#'Cs)K#m#S;#m##$+s)Ns$SS,#)s$I*#'Cs)B#m#S<#m##$+s)Es$NS-#'Cs)2'm#S=#m##$+s)5s$RS.#)s$N*#'Cs)*#m#S##m##$+s)-s$SJ#,S/&E#s%e)#*#'Cs)'#m#S>#m##$+s)*(H#cS?S/LPs#Gs#As#;s#5s#/s#)A;51+#j#%s$S#j#&s$]#j#'s$b#j#(s$d#j#)s$p#j#*s$[#j#+s%.#j#,s%3#j#-s%5#j#.s%L#j#/s%u#j#0s&;#`#S%S&S'S(S)S*S+S,S-S.JHj#%s$f#j#&s$j#j#'s$o#j#(s$q#j#)s$}#j#*s%7#j#+s%;#j#,s%@#j#-s%B#j#.s%Y#j#/s&&#j#0s&H#ZS@KOFs&N#SAj##s&R#j##s&`#j##s&p#j##s'*#j##s';#j##s'N#j##s'V#j##s'b#j##s'j#j##s(##j##s(8#j##s(N#j#1s+a#j#2s+c#j#3s+f##"). Qed.
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
Lemma ecall_86de4 : fetch_word bsegs (Z_to_bv 64 0x086c64) = Some ECALLW.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.option); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.Some); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@stdpp.bitvector.definitions.Z_to_bv_obligation_1); constr:(@Corelib.Init.Logic.eq); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.SecLazy.ECALLW)|] Array.empty "##a###3#+#)#.#,#(#'#0#-#&#4#2#3#5#1#*#/%#1$#2$#C########UD#UG#UH#$C$#####$#$#UE#VI,#WJ-$#VF-#VK-##1UD#$4$###$#$###$#$#$#$#####$#####UE##C######$#$###$#$#######$#$#####$#####UE#VLs#'#VMN#VFs#7OWPs#7$#m$s#-##"). Qed.

End HCW.

