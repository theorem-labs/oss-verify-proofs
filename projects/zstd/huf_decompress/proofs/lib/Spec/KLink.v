(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad STree Malloc KInv PState.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_KLink () := "C46Stdlib5Lists4List2hdC59OSSVerify5KrLib3Lib5Nodes7vm_onlyC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdI47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic3and00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedI4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00K47Corelib7Numbers7BinNums8positive03C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic2eq01c59OSSVerify5KrLib4Spec5KLink?vm_only_init_spC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topI47Corelib7Numbers7BinNums1Z00C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00i59OSSVerify5KrLib4Spec5KLink2KL00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2lec59OSSVerify5KrLib4Spec5KLink7kl_minvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes>minv_alloc_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_atopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5KLink7kl_atopC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes@alloc_ceiling_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes=alloc_ceilingC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5KLink=KL_atop_rangeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C47Corelib4Init5Logic6eq_indK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib3Lib5NodesAalloc_ceiling_valC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5NodesDalloc_ceiling_lo_valC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope Z_scope.

Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition went (b n : Z) : word * word := (wz b, wz n).
Definition wwZ (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (snd e)).
Definition elo (e : word * word) : Z := bv_unsigned (fst e).
Definition ehi (e : word * word) : Z := bv_unsigned (fst e) + bv_unsigned (snd e).

(* [comment removed for export] *)
Definition wcov (maps : list (word * word)) (lo hi : Z) : Prop :=
  forall x, lo <= x < hi -> exists e, In e maps /\ elo e <= x < ehi e.

(* [comment removed for export] *)
Definition edisj (e1 e2 : word * word) : Prop := ehi e1 <= elo e2 \/ ehi e2 <= elo e1.
Inductive pwdisj : list (word * word) -> Prop :=
| pwdisj_nil : pwdisj []
| pwdisj_cons e l : (forall e', In e' l -> edisj e e') -> pwdisj l -> pwdisj (e :: l).
Definition vmwf (maps : list (word * word)) : Prop :=
  (forall e, In e maps -> elo e < ehi e <= 2^64) /\ pwdisj maps.

(* [comment removed for export] *)
Definition brk_disj (L : mled) (b n : Z) : Prop :=
  forall b0 l0, ld_brkreg L = Some (b0, l0) -> b + n <= b0 + PGSZ \/ b0 + l0 <= b.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record KL (L : mled) (pbrk : Z) (mo : Model) : Prop := mkKL {
  kl_minv : minv mo;
  kl_halt : m_halted mo = None;
  kl_wf : vmwf (vm_maps (m_vmmaps mo));
  kl_resv : ld_resv L = map wwZ (vm_reserved (m_vmmaps mo));
  kl_resv_top : forall e, In e (vm_reserved (m_vmmaps mo)) -> ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo));
  kl_start : 0 < bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) mod PGSZ = 0
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) <= bv_unsigned (vm_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= ld_atop L;
  kl_groups : forall b l, In (b, l) (ld_groups L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= ld_atop L
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l);
  kl_metas : forall b l k, In (b, l, k) (ld_metas L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= ld_atop L
      /\ 0 <= k /\ (1 + k) * PGSZ <= mmap_len l
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l)
      /\ (forall q, 1 + k <= q -> (q + 1) * PGSZ <= mmap_len l ->
            exists e, In e (vm_noaccess (m_vmmaps mo)) /\ elo e <= b + q * PGSZ /\ b + q * PGSZ + PGSZ <= ehi e);
  kl_distinct : List.NoDup (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L));
  kl_brkreg : forall b l, ld_brkreg L = Some (b, l) ->
      0 < b /\ b mod PGSZ = 0 /\ 2 * PGSZ <= l /\ l mod PGSZ = 0 /\ b + l <= ld_atop L
      /\ wcov (vm_maps (m_vmmaps mo)) (b + PGSZ) (b + l);
  kl_phase : match ld_brk L with
      | BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
      | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
      | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
          /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= ld_atop L
          /\ (exists e, In e (vm_maps (m_vmmaps mo)) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
          /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
          /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo)) = b + l /\ pbrk = b + l
      | BPDead => True
      end;
  kl_atop : ld_atop L = alloc_top (m_vmmaps mo)   (* [comment removed for export] *) }.

(* [comment removed for export] *)
Definition frame_ok (G : PState -> Model -> Prop) : Prop :=
  forall s s' mo mo', ps_fa s' = ps_fa s -> ps_so s' = ps_so s -> vm_only mo mo' -> G s mo -> G s' mo'.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ev_step_post (L : mled) (e : ev) (G : PState -> Model -> Prop) (s0 : PState)
  : Z -> PState -> Model -> Prop :=
  fun z s mo => answer_ok L e z = true /\ KL (event_post L e z) (ps_brk s) mo /\ G s mo
                /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vm_only_init_sp : forall m m', vm_only m m' -> vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m).
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) [] "h02H0h11Hh22_Hh33_H0h43_H1h53_H2h63_H3h73_H4h83_H5h91mh:2m'p;2p;1p;3p-1p10000p4p710p8g000Gj2NTg001=j1CTg0020j31Tg002Jj1<Tg003=j19Tg0042j16Tg004gj13Tg005[j12Tg006Pj1=Tg0075j1ITg007Sj1HTg0086j2MTg008Vj1GTg0096j1ETg009VR0j27Tg00:1j1KTg00:hj1JTg00;aj1FTg00<Yj1LTg00=Yf1R1f0R231p=?g00>Q?112p=;%K2#Jp=0f2R3%F1;12p=5%L1=132p=4f3R4%F3;11/72p=:g00?KR5f5R6f4R731A1431/72'7p=8g00@ER8?131/72p=>1712,73p=@A1431/72p=BA1812p=AA1512p=Dg00A>R51N12P0g00B4R8%C1%C331g00BlR9%<1%<3%91%93'?%61%63';%31%33%21%23g00Cd#=#=#=#=#=#=#I#HR:%01%03R;1M::R<#GR=%E<R<753%G:R3%E:R>744R?P=P4P<P?C:[[E83>3@CB%0491:;P2%C4%C7518P9%<7%<6R8%97%96R4'?%67%66R;';%37%36R?%27%26R@P:%07%06R7A5=6<f6R6=43>RAA5=6<RB/7A[[E83>3@CBP0%<69198%96,?4%66,;;%36P@%26P:P7%06R6f7R7=43>R@P=P7P<P@C:[\BE85>?3@%0791:6P2%<7f8R7#<519%97f9R9#9R6'?%67%69R?';%37%39RB%27%29R@P:%07%09R7A5=9<f:R9=43>R;A5=9<R4/7;[[E83>3@P0%99,?6%69,;?%39,ABP@%29P:P7%09R9f;R7=43>R@P=P7P<P@C:[\4E83@%0791:9P2%97f<R7#9'?%67f=R9#6R4';%37%39R@'A%27%29RBP:%07%09R7A5=9<f>R9=43>R?A5=9<R6/7?[[E83@P0%69,;4%39PB%29P:P7%09R9f?R7=43>RBP=P7P<PBC:[\6E85>@%0791:9P2%67f@R7#6';%37fAR9#3R@%27%29R6P:%07%09R7A5=9<fBR9=43>RBA5=9<R4/7B[[E83>P0%39,A@P6%29P:P7%09R9fCR7=43>R6P=P7P<P6C:[\4E8%0791:9P2%37fDR7#3'A%27fER9#2R4P:%07%09R7A5=9<fFR9=43>R6A5=9<R@/76[[E8P0%29,D4P:P7%09R9fGR7=43>R4P=P7P<P4C:[\@CB%0791:9P2%27fHR7#2'DP:%07fIR7#0R9A5=7<fJR7=43>R@A5=7<R4/7@[[CBP0%07R791:9fKR9=43>R0P=P9P<P0C:[\4%09R991:7P2fL#091:9fM=5=<fNR9=43>R>P=P9P<P>C:[[P1W8W1P1P2O2n2001000000120000000W0W7P1P2O2n2001000000121000000W0W6P1P2O2n2001000000121000000W0W5P1P2O2n2011000000121000000W0W4P1P2O2n2011000000121000000W0W3P1P2O2n2011000000121000000W0W2P1P2O2n2011000000121000000W0X:5W9o"). Qed.
Lemma vm_only_alloc_top : forall m m', vm_only m m' -> alloc_top (m_vmmaps m') = alloc_top (m_vmmaps m).
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) [] "h01Hh11bh21mh32m'p;2p;1p;3p;6g000Gj2<Tg006Pj10Tg0075j1;Tg007Sj17Tg00:1j14Tg00:hj13Tg00DIj21Tg00E3j22Tg0020j36Tg00EPj2:Tg00Ejj38Tg00Fij69Tg00GGj15Tg00A>R0f1R1f0R2'<g00Cd#0#0#0#0#0#0#;R3#7R4f2R5#4R6#3R7g00H?R81132g00H]R9'2f3#4#3,13/2936X141137/29,:8%41R9#3A8512E9%59%56568eW0X30W2o"). Qed.
Lemma alloc_top_of_init_sp : forall h h', vm_init_sp h' = vm_init_sp h -> alloc_top h' = alloc_top h.
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) [] "h01Hh11bh21hh32h'p;1p;3p;2p;6g006Pj10Tg0075j19Tg007Sj18Tg00:hj11Tg0020j34Tg00DIj23Tg00E3j22Tg00EPj27Tg00Fij66Tg00GGj15Tg00IZR0g00Cd#0#0#0#0#0#0#9R1#8R2f0R3#1f1R4#1R534P2f2R6#1R7g00H?R81313g00H]R9'2f3#1,31/2934X121317/29,78P5P3E6%54%56548eW0X30W2o"). Qed.

(* [comment removed for export] *)
Lemma KL_atop_range : forall L pbrk mo, KL L pbrk mo -> alloc_ceiling_lo <= ld_atop L <= alloc_ceiling.
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) [] "h02HKh11Lh22moh34pbrkh41zp;3p;1p;2p;4p;6g00JQj39Tg00:1j18Tg00GGj11Tg00KEj20Tg009Vj27Tg00Kaj42Tg00LXj23Tg00MUj14Tg00NKj45Tg00Fij66Tg00OBg00H?R0g00A>f2R1f1R2f0R339P0%82#1g00P7/03g00Q6,03'7X40f3R0P1P2P3C2,32%40P0P1P2P3C5E6W0W2W3W1o"). Qed.
Lemma KL_atop_lt : forall L pbrk mo, KL L pbrk mo -> 0 < ld_atop L < 2^63.
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) [] "h01Hh14__x1h21zh32HKh41Lh57__arithh64__ffh78__varmaph85__with92moh:4pbrkp;3p;4p;1p;2p;6p;8p;7g00JQj3TTg00R2j4STg00MUj15Tg00KEj21Tg009Vj22Tg00Roj13Tg006Pj10Tg00STj1:Tg00T2j6;Tg0096j1RTg008Vj1QTg00TNj2NTg00Tlj1MTg00UJj1LTg00V5j26Tg00VXj2ITg00W;j48Tg00Wfj1FTg0075j1ETg00XHj3DTg00Xkj8GTg00YOj2HTg00EPj2CTg00Z1j2JTg0020j3KTg00Z]j3BTg00[<j4ATg00[nj2?Tg00\Jj2@Tg00\gj7OTg00]Kj7PTf0R0#3#3#3#3p=4%00#0p==%00#0#0#0p=>%00#0#0#0#0#0#0#0p=9f1R1g00]oR2g00^NR3P3g00^nR4P0g00_NFOp=7f2R5P2P3P3P4P1P0FPp=<g00OBg00H?R6g00A>AT510f3R7P5P1P0CSg00P7R8%57R7'1g00Q6R9,17'2P6P9f5#5R9,181190'2X26P0g00CdR7#3#4R:#3#4#4R;#3#4#4#0#=#>#9#9#:R<g00_nE;f4#5R=,1811=<'2P6P8f6#5R8,10118<'2X26P0%0;#4#4#0#=#>#9#9#:R;g00`nE;11;9119<'2g00b1R9#R%Q91N61%M6%L6R9P2P3P3P4P6166;g00b]R21I67R8C8,79P6P8P2166<C8,795<9%F3P6g00cDR3,66g00cbR2P8C8,79P6P8P2%07#:R7,66%E:5D6C8,795<9GG1H94P0P5g00dIR9g00diR4'C1J05=K94dAB631CAb6b7b8X1611;0110<'21?31%::,@7,?1'2[^16P0f7#5P1O2b5b0b0b0W3W9W:W4o"). Qed.
