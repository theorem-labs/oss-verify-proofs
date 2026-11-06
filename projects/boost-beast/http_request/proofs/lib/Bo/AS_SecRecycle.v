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
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AllocWf AllocKit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AllocRep.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AsAtomics.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AsDepotInv AllocWalkKit F_memset.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AW_Leaves AW_PoisonShadow AW_AllocBase AW_LargeAlloc1 AW_SysconfPg AW_PoisonRemap1 SecLazy SecLazy2 AW_GetBlockBegin AW_SecRecycle1 AW_LargeDealloc1 AW_LargeDealloc2 AW_LargeDealloc3 AS_SecRecycle1 AS_SecRecycle2 AllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section SecRecycle.
  Context {HCEIL : HeapCeil}.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo a msz sz idx pa nres nch lst lidx TSD CTX TH sb n actx : Z) (chunks : list Z) (ob0 ob1 : byte) (sbs : list byte) (g : word) (b244 : byte).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 800 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis AR : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0 /\ msz mod 4096 = 0 /\ 0x11000 <= msz < 2^40.
  Hypothesis SBX : hidden (a + msz <= sb \/ sb + kSpaceSize <= a).
  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize <= aceil).
  Hypothesis TPR : hidden (6354696 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (6354608 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  (* [comment removed for export] *)
  Hypothesis PLC : hidden ((CTX + 160 <= TH \/ TH + 4096 <= CTX) /\ (pa + kPtrArrayReserve <= TH \/ TH + 4096 <= pa) /\ (pa + kPtrArrayReserve <= CTX \/ CTX + 160 <= pa)
                        /\ (a + msz <= TH \/ TH + 4096 <= a) /\ (a + msz <= CTX \/ CTX + 160 <= a) /\ (a + msz <= pa \/ pa + kPtrArrayReserve <= a)).
  Hypothesis PAR : aapp pa kPtrArrayReserve /\ pa + kPtrArrayReserve <= aceil /\ pa mod 4096 = 0.
  Hypothesis NCH : zlen chunks = nch /\ 0 <= idx < nch /\ nch <= nres <= 2^20.
  Hypothesis IDX : nth_error chunks (Z.to_nat idx) = Some a.
  Hypothesis LNTH : nth_error chunks (Z.to_nat (nch - 1)) = Some lst.
  Hypothesis LR : aapp lst 4096 /\ lst + 4096 <= aceil.
  Hypothesis PLCL : idx < nch - 1 -> hidden ((a + msz <= lst \/ lst + 4096 <= a) /\ (lst + 4096 <= pa \/ pa + kPtrArrayReserve <= lst) /\ (lst + 4096 <= TH \/ TH + 4096 <= lst) /\ (lst + 4096 <= CTX \/ CTX + 160 <= lst)).
  Hypothesis LSTA : idx = nch - 1 -> lst = a.
  (* [comment removed for export] *)
  Hypothesis DISJ : Forall (fun c => 0 <= c < 2^47 /\ (c <= a + 6128 -> c <= a)) chunks.
  Hypothesis NR : 0 <= n < 2^32.
  (* [comment removed for export] *)
  Hypothesis SEN : SENV tp TSD CTX TH m.
  Hypothesis REN : RENV g b244 m.
  Hypothesis SB32 : rw_cells bsegs m 1220984 [C8 (wz sb)].
  Hypothesis INST64 : rw_cells bsegs m 1221016 [C8 (wz 4096); C8 (wz pa); C8 (wz pa)].
  Hypothesis NRES : rw_cells bsegs m 1221064 [C8 (wz nres); C8 (wz nch); C8 (wz 0)].
  Hypothesis SST : stk bsegs m 1221088 1221632.
  Hypothesis MTX : rw_cells bsegs m 1221632 [C8 (wz 0)].
  Hypothesis GST : stk bsegs m 1221640 1221680.
  Hypothesis PA : u64arr bsegs m pa (wlist chunks).
  Hypothesis HDR : rw_cells bsegs m a [C8 (wz a); C8 (wz msz); C8 (wz sz); C8 (wz idx)].
  Hypothesis LSTC : idx < nch - 1 -> rw_cells bsegs m (lst + 24) [C8 (wz lidx)].
  Hypothesis CHDR : rw_cells bsegs m (a + 6128) [C1 ob0; C1 ob1; C2 (wz 0); C4 (wz n); C8 (wz actx)].
  Hypothesis TST : stk bsegs m (TH + 2800) (TH + 3168).
  Hypothesis SHD : u8arr bsegs m (sh a) sbs. Hypothesis SHDL : Z.of_nat (length sbs) = msz / 8.
  Hypothesis OK : lzok bsegs L S Zr (mkCfg msF mo).
  Hypothesis VISE : restrict L S msF
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz (a + 6128)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x523cc) fc None m (seg_rom bsegs).

  (* [comment removed for export] *)
  Hypothesis NW : entries_nowrap (vm_maps (m_vmmaps mo)). Hypothesis NWA : entries_nowrap (vm_noaccess (m_vmmaps mo)).
  Hypothesis NOV : nooverlap (vm_maps (m_vmmaps mo)).
  (* [comment removed for export] *)
  Hypothesis ZRSH : forall x : word, (sh AHI_LO <= bv_unsigned x < sh aceil \/ sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO) -> in_rangesb x Zr = true.
  Hypothesis HSRF : forall a n : word, (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
                      region_free (vm_reserved (m_vmmaps mo)) a n = true.
  Hypothesis HSMC : forall a n : word, 0 < bv_unsigned n -> (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
                      map_contains (vm_maps (m_vmmaps mo)) a n = true.
  (* [comment removed for export] *)
  Hypothesis HSNA : forall a n : word, (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
                      region_free (vm_noaccess (m_vmmaps mo)) a n = true.
  (* [comment removed for export] *)
  Hypothesis WIN : forall x : word, sh a <= bv_unsigned x < sh a + msz / 8 -> in_rangesb x S = true.
  Hypothesis HAS : map_has (vm_maps (m_vmmaps mo)) (wz a) (wz msz) = true.
  Hypothesis NOL : forall x : word, a <= bv_unsigned x < a + msz -> in_rangesb x L = false.
  Hypothesis NOACC : forall x : word, a <= bv_unsigned x < a + msz -> in_rangesb x (vm_noaccess (m_vmmaps mo)) = false.
  (* [comment removed for export] *)
  Hypothesis ATOP : alloc_top (m_vmmaps mo) = hceil.

  Let ARE : 6832128 <= a /\ a + msz <= aceil. Proof. exact (aapp_env _ _ (proj1 AR) ltac:(lia)). Qed.   (* [comment removed for export] *)
  Let PAE : 6832128 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; lia)). Qed.   (* [comment removed for export] *)
  Let LRE : 6832128 <= lst /\ lst + 4096 <= aceil. Proof. exact (aapp_env _ _ (proj1 LR) ltac:(clear; lia)). Qed.   (* [comment removed for export] *)
  Let POST := recycle_sec_post L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a msz nres nch idx pa lst TSD CTX TH chunks g b244.

  (* [comment removed for export] *)
  Theorem recycle_sec_sreach :
    (forall msF' mo', POST msF' mo' -> sreach bsegs Q (mkCfg msF' mo')) -> sreach bsegs Q (mkCfg msF mo).
  Proof.
    ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(POST); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SReach.sreach); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Scfg.hunspell_scfg); constr:(Q); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.lazy_ranges_okb_nowrap); constr:(L); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazySR.lzok_ranges); constr:(S); constr:(Zr); constr:(msF); constr:(mo); constr:(OK); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyLedger.entries_nowrap); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_SecRecycle1.recycle_sec_head); constr:(HCEIL); constr:(ra); constr:(sp); constr:(gp); constr:(tp); constr:(t0); constr:(t1); constr:(t2); constr:(s0); constr:(s1); constr:(a0); constr:(a2); constr:(a3); constr:(a4); constr:(a5); constr:(a6); constr:(a7); constr:(s2); constr:(s3); constr:(s4); constr:(s5); constr:(s6); constr:(s7); constr:(s8); constr:(s9); constr:(s10); constr:(s11); constr:(t3); constr:(t4); constr:(t5); constr:(t6); constr:(F); constr:(fc); constr:(m); constr:(lo); constr:(a); constr:(msz); constr:(sz); constr:(idx); constr:(pa); constr:(nres); constr:(nch); constr:(lst); constr:(lidx); constr:(TSD); constr:(CTX); constr:(TH); constr:(sb); constr:(n); constr:(actx); constr:(chunks); constr:(ob0); constr:(ob1); constr:(sbs); constr:(g); constr:(b244); constr:(MI); constr:(ST); constr:(LO); constr:(HI); constr:(AR); constr:(SBX); constr:(SBR); constr:(TPR); constr:(RNG); constr:(PLC); constr:(PAR); constr:(NCH); constr:(IDX); constr:(LNTH); constr:(LR); constr:(PLCL); constr:(LSTA); constr:(DISJ); constr:(SEN); constr:(REN); constr:(SB32); constr:(INST64); constr:(NRES); constr:(SST); constr:(MTX); constr:(GST); constr:(PA); constr:(HDR); constr:(LSTC); constr:(CHDR); constr:(TST); constr:(SHD); constr:(SHDL); constr:(VISE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_SecRecycle1.recycle_sec_mid); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_SecRecycle2.recycle_sec_poison); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_SecRecycle2.recycle_sec_mid2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_SecRecycle2.recycle_sec_unmap); constr:(SPA); constr:(NW); constr:(NWA); constr:(NOV); constr:(ZRSH); constr:(HSRF); constr:(HSMC); constr:(HSNA); constr:(WIN); constr:(HAS); constr:(NOL); constr:(NOACC)|] [|@mo'; @msF'; @M4; @mo4; @msF4; @M3; @mo3; @msF3; @NWL; @K|] "##:#+$G#7#$#<#9#:###A#B#C#D#H#I#Q#R#S#T#U#V#W#X#Y#Z#_#`#a#b#c#d#h#i#f#g#j#l#m#n#r#v#w#4#%#2#/#.#u#@#z#{#|$#$$$%$&$'$*$+$,#5#;#=$<#0#1#3#8#6#>$>$@$A$B$C$D$E$F$G$H$I$J$K$L$M#*$?#?#E#F#G#J#K#L#M#N#O#P#[#\#]#^#e#k#o#p#q#s#t#x#y#}#~$($)$-$.$/$0$1$2$3$4$5$6$7$8$9$:$;$=#VSPDHVSLS;DXSQS<SRS:#k##%#k#$S=#k#%S>#VSLSMEZSSS<CFG#SNWSTS<C#USUCi#KSVCFGEIJKLMNOPQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4S5S6S7S?S8S9DHi#JSWCFGEIJKLMNOPQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4S5S6S7S8S9DHi#eSXS@CFGES:IJKLMNOPQRS#S$S%S&S'S(S)S*S+S,S-S.S1S2S/S0S3S4S5S6S7S8S9SASBSYSCSDSESFSGSHSISJSKSZS[S\S]S^S_S`SaSbScSdS;DHSej#&$#j#'S=#j#(S>#i#[SfS@CFGES:IJKLMNOPQRS#S$S%S&S'S(S)S*S+S,S-S.S1S2S/S0S3S4S5S6S7S8S9SASBSCSDSESFSGSHSISJSKS?S;DHSO#j#))#j#*S=#j#+S>#i$)SgS@CFGSMES:IJKLShSiSjMNSkSlSmSnSoSpSqOPQRS#S$S%S&S'S(SrSsStSuS)S*S+S,S-S.SvS1S2S/S0S3SwS4S5S6SxSySzS7S{S|S?S8S9S}S~SASBSCT#T$SDSESFSGSHT%T&SISJSKT'T(T)T*T+T,T-T.T/T0T1T2T3T4T5SOSNT6#l#,/.#j#-3##"). Qed.
End SecRecycle.
