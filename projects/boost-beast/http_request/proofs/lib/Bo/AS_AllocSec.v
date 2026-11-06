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
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AsDepotInv AsDepotHash AsDepotPut AllocWalkKit F_memset.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AW_Leaves AW_PoisonShadow AW_DepotFrame AW_AllocBase AW_LargeAlloc1 AW_SysconfPg SecLazy AS_LargeAlloc AS_CombinedLarge AW_AllocSec1 AW_AllocSec2 AS_AllocSec1 AS_AllocSec2 AllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section AllocSec.
  Context {HCEIL : HeapCeil}.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  (* [comment removed for export] *)
  Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).   (* [comment removed for export] *)
  Variables (x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 : word) (j8 : list byte).
  Variables (lo size needed msz TSD CTX TH sb SO pa nres nch q8 r8 nT id : Z) (chunks T : list Z) (rest : list word) (d : depot).
  Hypothesis DEFS : hidden (needed = round_up (Z.max size 8) 8 + 4096 /\ msz = round_up needed 4096 + 4096 /\ size = 8 * q8 + r8
                            /\ nT = Z.of_nat (length T) /\ id = d_putid d (depot_hash T)).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 768 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0). Hypothesis SPH : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SZ : 64512 < size < 2^32. Hypothesis R8 : 0 <= r8 < 8.
  Hypothesis TPR : hidden (6354696 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (6354608 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis PLC0 : hidden ((CTX + 160 <= TH \/ TH + 4096 <= CTX) /\ (pa + kPtrArrayReserve <= TH \/ TH + 4096 <= pa) /\ (pa + kPtrArrayReserve <= CTX \/ CTX + 160 <= pa)).
  Hypothesis PLCD0 : hidden ((TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 262144 <= TH)
                /\ (CTX + 160 <= d_nb d \/ d_nb d + 16 * 65536 <= CTX) /\ (CTX + 160 <= d_sb d \/ d_sb d + 8 * 262144 <= CTX)
                /\ (pa + kPtrArrayReserve <= d_nb d \/ d_nb d + 16 * 65536 <= pa) /\ (pa + kPtrArrayReserve <= d_sb d \/ d_sb d + 8 * 262144 <= pa)
                /\ aapp (d_nb d) (16 * 65536) /\ aapp (d_sb d) (8 * 262144)).
  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize <= aceil).
  Hypothesis SOR : hidden (bv_unsigned sp <= SO /\ SO + 2064 <= 2^47).
  Hypothesis PAR : aapp pa kPtrArrayReserve /\ pa + kPtrArrayReserve <= aceil /\ pa mod 4096 = 0.
  Hypothesis NCH : 0 <= nch <= nres /\ nres + 16384 <= 2^20. Hypothesis NRQ : exists q, nres = 512 * q.
  Hypothesis LEN : zlen chunks = nch.
  Hypothesis NR : 1 <= nT <= 254. Hypothesis TRNG : Forall (fun x => 0 <= x < 2^64) T.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + nT + 1 <= 262144.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 262144 <= lo.
  (* [comment removed for export] *)
  Hypothesis AEN : AENV tp TSD CTX TH sb SO T rest m.
  Hypothesis SEN : SENV tp TSD CTX TH m.
  Hypothesis FR : aframe sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m j8.
  Hypothesis INST64 : rw_cells bsegs m (AINST + 64) [C8 (wz 4096); C8 (wz pa); C8 (wz pa)].
  Hypothesis NRES : rw_cells bsegs m (AINST + 112) [C8 (wz nres); C8 (wz nch); C8 (wz 0)].
  Hypothesis SST : stk bsegs m (AINST + 136) (AINST + 680).
  Hypothesis MTX : rw_cells bsegs m (AINST + 680) [C8 (wz 0)].
  Hypothesis GST : stk bsegs m (AINST + 688) (AINST + 728).
  Hypothesis TST : stk bsegs m (TH + 2800) (TH + 3168).
  Hypothesis PA : u64arr bsegs m pa (wlist chunks).
  Hypothesis PAJ : stk bsegs m (pa + 8 * nch) (pa + 8 * nres).
  Hypothesis DEP : DEPOT bsegs d m.
  (* [comment removed for export] *)
  Hypothesis NW : entries_nowrap (vm_maps (m_vmmaps mo)). Hypothesis NWA : entries_nowrap (vm_noaccess (m_vmmaps mo)).
  Hypothesis NOV : nooverlap (vm_maps (m_vmmaps mo)).
  Hypothesis BUD : eager_used mo + pages_total S * page_size + msz + (msz / 32768 + 2) * page_size + 0x20000 <= vm_limit (m_vmmaps mo).
  Hypothesis GAP : exists g : word, bv_unsigned g mod page_size = 0 /\ 0 < bv_unsigned g /\ bv_unsigned g + msz <= alloc_top (m_vmmaps mo)
                                    /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) g (wz msz) = true.
  (* [comment removed for export] *)
  Hypothesis IMGR : forall x : word, AIMG_LO <= bv_unsigned x < AIMG_TOP -> in_rangesb x (vm_reserved (m_vmmaps mo)) = true.
  Hypothesis SHLAND : forall x : word, ALOWSH_LO <= bv_unsigned x < AHI_LO -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  (* [comment removed for export] *)
  Hypothesis ATOP : alloc_top (m_vmmaps mo) = hceil.
  Hypothesis ZRSH : forall x : word, (sh AHI_LO <= bv_unsigned x < sh aceil \/ sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO) -> in_rangesb x Zr = true.   (* [comment removed for export] *)
  Hypothesis HSRF : forall a n : word, (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
                      region_free (vm_reserved (m_vmmaps mo)) a n = true.
  Hypothesis HSMC : forall a n : word, 0 < bv_unsigned n -> (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
                      map_contains (vm_maps (m_vmmaps mo)) a n = true.
  Hypothesis SVIS : forall x : word, in_rangesb x S = true -> wview bsegs m x <> None.
  Hypothesis TMAPS : forall x : word, TH <= bv_unsigned x < TH + 4096 -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  Hypothesis CMAPS : forall x : word, CTX <= bv_unsigned x < CTX + 160 -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  Hypothesis PMAPS : forall x : word, pa <= bv_unsigned x < pa + kPtrArrayReserve -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  Hypothesis SBMAPS : forall x : word, sb <= bv_unsigned x < sb + kSpaceSize -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  Hypothesis DNMAPS : forall x : word, d_nb d <= bv_unsigned x < d_nb d + 16 * 65536 -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  Hypothesis DSMAPS : forall x : word, d_sb d <= bv_unsigned x < d_sb d + 8 * 262144 -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  Hypothesis PAMC : nch = nres -> map_contains (vm_maps (m_vmmaps mo)) (wz (pa + 8 * nres)) (wz 0x20000) = true.
  Hypothesis PARF : nch = nres -> region_free (vm_reserved (m_vmmaps mo)) (wz (pa + 8 * nres)) (wz 0x20000) = true.
  Hypothesis PAZR : nch = nres -> forall x : word, pa + 8 * nres <= bv_unsigned x < pa + 8 * nres + 0x20000 -> in_rangesb x Zr = false.
  Hypothesis OK : lzok bsegs L S Zr (mkCfg msF mo).
  Hypothesis VISE : restrict L S msF
    = MS (mkR (wz 0x5035c) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz 0) (wz size) (wz AINST) (wz (TH + 208)) (wz needed) (wz 8) x14 x15 x16 x17
              (wz 8) (wz needed) (wz 2048) (wz size) (wz AINST) (wz SO) (Z_to_bv 64 (-8)) (wz 7) (wz TH) (wz 1) x28 x29 x30 x31)
         F (Z_to_bv 64 0x54814) fc None m (seg_rom bsegs).

  Let PAE : 6832128 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; lia)). Qed.   (* [comment removed for export] *)
  Let POST := alloc_sec_sr_post L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo size needed msz TSD CTX TH sb SO pa nres nch id nT chunks T rest d.
  Let MID := alloc_sec_mid L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo size needed msz TSD CTX TH sb SO pa nres nch q8 r8 id nT chunks T rest d.

  (* [comment removed for export] *)
  Theorem alloc_sec_sreach :
    (forall msF' mo', POST msF' mo' -> sreach bsegs Q (mkCfg msF' mo')) -> sreach bsegs Q (mkCfg msF mo).
  Proof.
    ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(POST); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SReach.sreach); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Scfg.hunspell_scfg); constr:(Q); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_AllocSec1.alloc_sec_head); constr:(HCEIL); constr:(L); constr:(S); constr:(Zr); constr:(msF); constr:(mo); constr:(ra); constr:(sp); constr:(gp); constr:(tp); constr:(F); constr:(fc); constr:(m); constr:(s0); constr:(s1); constr:(s2); constr:(s3); constr:(s4); constr:(s5); constr:(s6); constr:(s7); constr:(s8); constr:(s9); constr:(s10); constr:(s11); constr:(x5); constr:(x6); constr:(x7); constr:(x14); constr:(x15); constr:(x16); constr:(x17); constr:(x28); constr:(x29); constr:(x30); constr:(x31); constr:(j8); constr:(lo); constr:(size); constr:(needed); constr:(msz); constr:(TSD); constr:(CTX); constr:(TH); constr:(sb); constr:(SO); constr:(pa); constr:(nres); constr:(nch); constr:(q8); constr:(r8); constr:(nT); constr:(id); constr:(chunks); constr:(T); constr:(rest); constr:(d); constr:(DEFS); constr:(MI); constr:(ST); constr:(LO); constr:(HI); constr:(SPA); constr:(SPH); constr:(SZ); constr:(R8); constr:(TPR); constr:(RNG); constr:(PLC0); constr:(PLCD0); constr:(SBR); constr:(SOR); constr:(PAR); constr:(NCH); constr:(NRQ); constr:(LEN); constr:(NR); constr:(TRNG); constr:(DCAP); constr:(DLO); constr:(AEN); constr:(SEN); constr:(FR); constr:(INST64); constr:(NRES); constr:(SST); constr:(MTX); constr:(GST); constr:(TST); constr:(PA); constr:(PAJ); constr:(DEP); constr:(NW); constr:(NWA); constr:(NOV); constr:(BUD); constr:(GAP); constr:(IMGR); constr:(SHLAND); constr:(ATOP); constr:(ZRSH); constr:(SVIS); constr:(TMAPS); constr:(CMAPS); constr:(PMAPS); constr:(SBMAPS); constr:(DNMAPS); constr:(DSMAPS); constr:(PAMC); constr:(PARF); constr:(PAZR); constr:(OK); constr:(VISE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_AllocSec1.alloc_sec_mid); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AS_AllocSec2.alloc_sec_small)|] [|@mo'; @msF'; @M3; @mo3; @msF3; @K|] "##0#'$G#$###0#3#4#5#6#8#9#:#;#<#@#A#B#C#D#E#F#G#H#I#J#K#=#>#?#X#Y#Z#[#\#]#^#_#`#a#b#c#d#e#g#f#h#i#j#k#%#+#*#l#o#p#q#r#s#t#u#v#w#x#y#z#{#|#~$&$=$>$?$@$A$B#,#1#-#.#/$H$I#&#2#7#L#M#N#O#P#Q#R#S#T#U#V#W#m#n#}$#$$$%$'$($)$*$+$,$-$.$/$0$1$2$3$4$5$6$7$8$9$:$;$<$C$D$E$F$G#VS\CDVS]SBCXS^S_S`E#k##%#k#$SC#k#%SD#i#QSaFGHIJKLMNOPQRS#S$S%S&S'S(S)S*S+S,S-S.S/S0S1S2S3S4S5S6S7S8S9S:S;S<S=S>S?S@SACDi#kSbFGHIJEKLMNS+S,S-OPQRS#S$S%S&S'S(S)S*S.S/S0S1S2S3S4S5S6S7S8S9S:S;S=S<S>S?S@SASESFSGSHSISJSKSLSMSNSOSPSQSRSSSTSUSVSWSXSYSZS[SBCDScj#&$#j#'SC#j#(SD#i$:SdFGHISeJEKLMNS+S,S-OPQRS#S$S%S&S'S(S)S*SfSgShSiSjSkSlSmSnSoSpSqS.S/S0S1S2S3S4S5S6S7S8S9S:S;S=S<S>S?S@SASESrSsSFSGSHSISJSKSLSMSNSOSPSQSRSSStSTSuSvSwSUSxSySzS{S|S}S~T#T$T%T&T'T(T)T*T+T,T-T.T/T0T1SVSWSXSYSZS[T2T3T4T5T6#j#))##"). Qed.
End AllocSec.
