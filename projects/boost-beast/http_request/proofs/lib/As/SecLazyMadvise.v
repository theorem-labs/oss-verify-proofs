(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AllocSim MmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes LazyMadvise.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs SecLazy.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma ecall_85b48 : fetch_word asegs (Z_to_bv 64 0x0859d0) = Some ECALLW.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.option); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.Some); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@stdpp.bitvector.definitions.Z_to_bv_obligation_1); constr:(@Corelib.Init.Logic.eq); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.asegs); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.SecLazy.ECALLW)|] Array.empty "##a###3#+#)#.#,#(#'#0#-#&#4#2#3#5#1#*#/%#1$#2$#C########UD#UG#UH#$C$#####$#$#UE#VI,#WJ-$#VF-#VK-##1UD#$4##$#$###$#$###$#####$#######UE##C######$###$#$#####$#$#$###$#########UE#VLs#'#VMN#VFs#7OWPs#7$#m$s#-##"). Qed.

(* [comment removed for export] *)
Lemma zfill_zero_id : forall (a n : word) (m : word -> option byte) (A : Z) (k : nat),
  u8arr asegs m A (repeat (b8 0) k) -> 6811648 <= A ->
  A <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= A + Z.of_nat k ->
  zfill a n m = m.
Proof.
  intros a n m A k [BA WR] HI LO UP. apply functional_extensionality. intros x.
  unfold zfill, AllocSim.zmem.
  destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned a + bv_unsigned n)); cbn [andb]; try reflexivity.
  destruct BA as (_ & BH & BA). destruct WR as (_ & _ & WR). rewrite repeat_length in *.
  pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
  assert (EX : wa (A + Z.of_nat (Z.to_nat (bv_unsigned x - A))) = x).
  { unfold wa. replace (A + Z.of_nat (Z.to_nat (bv_unsigned x - A))) with (bv_unsigned x) by lia. apply Z_to_bv_bv_unsigned. }
  specialize (BA (Z.to_nat (bv_unsigned x - A)) ltac:(lia)). specialize (WR (Z.of_nat (Z.to_nat (bv_unsigned x - A))) ltac:(lia)).
  rewrite EX in BA, WR. rewrite nth_error_repeat in BA by lia.
  unfold mrd in BA. unfold wview in WR.
  destruct (m x) as [b|] eqn:E.
  - symmetry. exact BA.
  - exfalso. apply WR. rewrite asegs_find_segment_none_high by lia. reflexivity.
Qed.

Section CjMadvise.
  Variables (L S Zr : list (word * word)).
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
            (F : bvmap 5 word) (pc : Z) (fc : bv 32) (rv : option word) (m : word -> option byte).
  Let R := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  Let Ra (a : word) := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.

  (* [comment removed for export] *)
  Lemma sr_madvise_MS : forall msF mo (Q : config -> Prop),
    lzok asegs L S Zr (mkCfg msF mo) ->
    restrict L S msF = MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs) ->
    x17 = Z_to_bv 64 233 ->
    let addr := x10 in
    let nZ := page_round_up_Z (bv_unsigned x11) in
    let n := Z_to_bv 64 nZ in
    let h := m_vmmaps mo in
    bv_unsigned addr mod page_size = 0 -> bv_unsigned x12 mod 2 ^ 32 = 4 -> x11 <> Z_to_bv 64 0 -> bv_unsigned addr + nZ < 2 ^ 64 ->
    region_free (vm_reserved h) addr n = true -> map_contains (vm_maps h) addr n = true -> region_free (vm_noaccess h) addr n = true ->
    (forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + nZ -> hiddenb L S x = true -> in_rangesb x Zr = true) ->
    (forall msF' : machine_state,
       let mo' := madvise_dontneed_next mo addr n in
       lzok asegs L S Zr (mkCfg msF' mo') ->
       restrict L S msF' = MS (Ra (Z_to_bv 64 0)) F (Z_to_bv 64 (pc + 4)) fc rv (mzero L S (addr, n) m) (seg_rom asegs) ->
       hid_same L S msF msF' ->
       same_but_materialized mo mo' ->
       sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF mo).
  Proof.
    ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.config); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazySR.lzok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.asegs); constr:(L); constr:(S); constr:(Zr); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.restrict); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.MSsvc); constr:(R); constr:(F); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(pc); constr:(x17); constr:(fc); constr:(rv); constr:(m); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.PropExec.seg_rom); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(x10); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Corelib.Numbers.BinNums.Z0); constr:(x12); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.not); constr:(x11); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z); constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.region_free); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(@Corelib.Init.Datatypes.true); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.map_contains); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_maps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.hiddenb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.in_rangesb); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise.madvise_dontneed_next); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.MS); constr:(Ra); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyMadvise.mzero); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazySR.hid_same); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.same_but_materialized); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SReach.sreach); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Scfg.hunspell_scfg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyMadvise.sreach_madvise_dontneed_lazy); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.option); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.sysret); constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap_set); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Init.Logic.I); constr:(@stdpp.bitvector.definitions.bv_add); constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.mkR); constr:(x1); constr:(x2); constr:(x3); constr:(x4); constr:(x5); constr:(x6); constr:(x7); constr:(x8); constr:(x9); constr:(x13); constr:(x14); constr:(x15); constr:(x16); constr:(x18); constr:(x19); constr:(x20); constr:(x21); constr:(x22); constr:(x23); constr:(x24); constr:(x25); constr:(x26); constr:(x27); constr:(x28); constr:(x29); constr:(x30); constr:(x31); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.lit_add_lit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.SysStep.mkR_set_a0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.SecLazy.sysret_MSsvc); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.VmMaps)|] [|@x; @msF'; @x17; @m; @b; @SBM; @HS'; @VIS'; @OK'; @mo'; @K; @HZ; @NA; @MC; @RF; @NW; @LEN; @ADV; @AL; @h; @n; @nZ; @addr; @H17; @VIS; @OK; @Q; @mo; @msF|] "#%N#9$C#<#A#B#Z#@###&#O#d#h#%#I#P#Q#$#C#W#'#(#`#3#4#x#R#]#-#5#*#)#N#H#\#+#,#1$)$*$+$,$-$.$/$0$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$@$A$B$C#=#/#8#M#K#[#^#f#j#i#k#m#l#0#t#s$#$(#.#>#9#S#G#T#_#c#n#o#r#{#|#~$$$%$&$'$D$E$F#y$G#E#L#D#J#Y#U#V#p#q#}#?#F#b#a#g#e#u#v#w#X#z8$.&$/$$0%$1%$2%$3$$4$$5&$6*$7)$8($9&$:%$;%$<$$=&$>'$?%$@'$A%$B%k##SdSe%MQ-GDER#.DEI$ST$#$#$#$#$#USU#&#S0USfG\SgS1N$JOPS*##C-#USh')ST)#$#)#$#$#)#(#&0##,J#'2F6#SV#S##S2'5S+(<(9VSW$#6&#(?#S#$#&<S2#8S&#USi#'?S&USj#/1#(s##VSW/#0%#1S3USX#&s#')2$F##K#L1S4USY#WSZ#F'#K#L1S,US[#2#F+#K#L's#2HVS\s###0$5VS]$#WSkDEQ#K#LVSlMR#K#Lk##%#k##(#k#$s#7#*S^F8%H#-GDER#.DEQUSms#'/S0s#*&s#C#XS_s#?s#?F?XS`DE#S*+'N%OP#s#D#C)#3DES'M*S'Fs#$4S'#*S(Fs#&%S$#5GS)S'#k##&#k##)#k##+#k##4#k#%C#USns#NUSos#Q7$##S#s#&s#Ij#&s#R#7S#s#K,s#Ts#K$#JS4*S5Fs#5%H#-GDER#WSps#Zs#C:#C@#3DES(M4S(7#CH=j#'C#)s#iUSU#$$(#WSq%#SrYSa&s#c#s#NS1&s#is#QWSss#js#i#+%N#OPs#(s#iVSt*s#gi#BSbS6S7S8S9S:S;S<S=S>s#SS&S+S?S@SASBJSCSDSESFSGSHSISJSKSLSMSNSOSP+HN&OPs#+s#l#C#s#+j#(&#+&NHOPs#.s#o#C#s#.j#(s#n#7Cs#0VSuS0s#],s#qs#5%$.#i#BSbS6S7S8S9S:S;S<S=S>FS&S+S?S@SASBJSCSDSESFSGSHSISJSKSLSMSNSOSPYSa6s#s3s#^#i#CSvS6S7S8S9S:S;S<S=S>FS&S+S?S@SASBJSCSDSESFSGSHSISJSKSLSMSNSOSPs#_,0/,&$##C2s#7m#$#^SwS1Ns#|JOPS*s#{s#cs#:,C5>$s###.DES$,Cs#%@$#MYS%S$I#QHj#)s#$#j#*s#&#j#+s#(#j#,s#+#%QH-GDER#.DEM#C#s#.3DES-I4S-I%S%S$5GS)S-#k##%#k##'#k##)#k##,#l#-s#:SQ#m#0#j#%C#i#:SxGS)DERS5s$6S^JSRScS,s#Bs#>S3S.S/S%S$IMQ#j#.s#F#j#/s#]#j#0s#i#j#1s#n#j#2s#s#j#3s#y#j#4s$$#j#5s$(#j#6s$0#&s$CH1S.'s$EI6#SV#S##S2's$HS//#S%0#s$)USXS$2#S.S%#K#LUSYS%WSZ#S3S/#K#LUS[S/2#S4S.#K#L's$TScVS\#s$%/$S,0s$'#VS]%#k###s#}k#$s$U#*S(SRS,XS_s$Ws$WS5SRXS`DE#S*+s#{Ns#yOP#s$\#Cs#5#3DESSI4SSI5GS)SSs#4k##$#k##&#k##(#k##s#=#l#-.SQ#k#%C#%S-S(5GS)S'#k##%#k##4#k##<#k##@#k##s#$#k##s#(#k##s$U#k##s$Y#k##s#.#l#7s#2Sy#l#8s#4s$p#l#9s$XS##l#:Fs$r#m#s#8#j#;s$j#j#<s$v#j#=s%'#j#>s%*#j#?SQ#j#@C##"). Qed.
End CjMadvise.
