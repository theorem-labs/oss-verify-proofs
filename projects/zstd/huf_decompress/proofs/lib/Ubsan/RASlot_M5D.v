(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (3 recorded proofs replaced by written proofs (rconc_meta_stable', rmalloc_fp_widen, rregion_byte_raw)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_I ASlot_M0 ASlot_M5D.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RASlot_W2 RASlot_W4 RASlot_M0 RASlot_M2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require MallocFacts_inv4.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RASlot_M5D () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib6Malloc:MallocTree7leaf_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5Ubsan:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc9Malloc_fp4mrel00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableI35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rregions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep9rmrep_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep=rmrep_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rmrep_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep8rstaticsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C59OSSVerify5KrLib6Malloc9Malloc_fp<mrel_regionsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;conc_regionC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC56Stdlib6ZArith6BinInt1Z6moduloC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableC59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib5Ubsan:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib5Ubsan:RMalloc_fp:rmalloc_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree9ralloc_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp<new_reg_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp>free_slot_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp<grp_hdr_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree:fresh_addrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib5Ubsan:RMalloc_fp?rmalloc_fp_monoC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib5Ubsan:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRepArmrep_shadow_readC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMalloc_fp=rregion_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr01C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;memory_readC47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImgDref_memory_read_noneC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indK46Stdlib9micromega5Tauto8GFormula06I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep4RATPC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma rconc_meta_stable' st stE m q : rmrep st m -> mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof.
  intros MR REL (ar & arr & kk & Ha & Hk & ->). pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & WA & _).
  destruct (WA ar arr Ha) as (r & Hr & _). destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _).
  unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

Lemma rmalloc_fp_widen st0 stA stB lo sp sp' a :
  sp' <= sp ->
  (forall rid r, (s_regions stA) !! rid = Some r ->
     exists r', (s_regions stB) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  rmalloc_fp st0 stA lo sp' a -> rmalloc_fp st0 stB lo sp a.
Proof.
  intros LE HR H. apply (rmalloc_fp_mono st0 stA stB lo sp a HR).
  destruct H as [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

(* [comment removed for export] *)
Lemma rregion_byte_raw st m rid r off v :
  rmrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
  cell_read (get_shadow st rid) off = Known v -> m (wa (r_base r + off)) = Some (b8 v).
Proof.
  intros MR Hr Hk Ho Hc.
  destruct (rmrep_shadow_read st m rid r off v MR Hr Hk Ho Hc) as [RD _].
  destruct (rregion_facts st m rid r MR Hr) as (R4 & RAL & RC & RI1 & RI2). atop_facts.
  specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
  cbn [ov_read_bytes] in RD.
  destruct (m (wa (r_base r + off))) as [b|] eqn:E.
  - cbn in RD. inversion RD. reflexivity.
  - rewrite ref_memory_read_none in RD; [discriminate| cbn; lia|]. rewrite wa_unsigned by lia. cbn. lia.
Qed.

Lemma rerrno_lit5 (tp : word) : tp = Z_to_bv 64 RATP -> errno_addr tp = 0x3b7fc.
Proof.
ltac2:(KReplay.run1 (kr_t_RASlot_M5D ()) ["CANSEC1"] "h02tph11Hh27__arithh34__ffh48__varmaph55__with61zp;1p;2p;3p;4p;7p;6g004lj14Tg005Qj1JTg005oj1ATg01>Vj2=Tg00K7j35Tg01?<j27Tg00ZTj10Tg00Qij1CTg00Hhj29Tg00FXj16Tg00^Rj2>Tg00Unj1RTg00Vnj1QTg00XJj1PTg00Xhj1OTg00YFj1NTg01L?j28Tg00[9j4;Tg01WZj3ITg01A_j7HTg00^0j2DTg00^lj2ETg00_Xj3FTg00`7j4GTg00OPj2BTg01X=j2KTg00;Vj2LTg00Olj2@Tg01_9j2MTg000ej6<Tg00ecj7?Tf0R0#4#4p=1%00#4p=2%00#0p=3f1R1g00mkR2g00nJR3P3g00njR4P0g00oJF?p=:g010cR5#4R6#4#1#1R7#JR8#AR9g01`5,=8R:9590P9P:g00iOR;1780%06#1#0#1#CR<'9%05#2#0#2#0#3#3#3#3#1#6R=35X09P;%05#2#3#2#1#2#2#1#1#6R5190<=5;=X6;1>;=1=85,78g015oR>#R%Q>%P;%O;%N;R>P2P3P3P4P;g00g>R3,8;g01C=18;5R2C;,:>P;P2g01Cd%66R6,8;=I;8C;,:>FH1D>4P0f2R>g013mR4g015OR2'>1E0>=542dAF;31CGb3b4b51B35%67,K6,L5'@P0b2,M5E<178:/9<=5;=eP1P0E<W1X09P0O1X09P0O1W0o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk usegs m lo (bv_unsigned sp).
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells usegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv usegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.
(* [comment removed for export] *)
Definition rnest_regs (st2 : mstate) (mm : aptr) (cnt1 : Z) (a0v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) :=
  mkR (Z_to_bv 64 0x22d50) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) (Z_to_bv 64 (conc st2 mm))
      a0v a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (ncls sc cnt1)) (wz cnt1)
      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc))
      (wz (size_class sc * UNIT)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3' t4' t5' t6'.

(* [comment removed for export] *)
Definition rnest_ctx (st1 st2 : mstate) (mm : aptr) (cnt1 : Z) (st3 : mstate) (idx : Z)
    (m4 m'' : mem) (s' s'' : PState) (errv'' : word) (junk : list byte) (oo o3 : mem) : Prop :=
  ta_fail sc st st1 /\ ta_rel sc st st1 /\ active st1 sc = None /\
  leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) /\
  IST st0 st2 /\ ENTRY_REL st0 st2 /\ ALLC st2 /\
  am_rel st1 st2 (Some mm) /\ get_meta_rec st2 mm = meta0 /\ meta_slot st2 mm /\
  1 <= cnt1 <= 32 /\ size_class sc * UNIT * cnt1 + UNIT <= 2048 /\
  leaf_of o3 (alloc_slot full_lay f st2 (ncls sc cnt1) (nreq sc cnt1) kS bS) (Some (st3, idx)) /\
  mem_inv usegs m'' /\ stk usegs m'' lo (bv_unsigned sp - 144) /\
  rw_cells usegs m'' (errno_addr tp) [C4 errv''] /\ rauxv_ok m'' (bv_unsigned sp - 144) /\
  rmrep st3 m'' /\ ticks_ok st3 /\ unk_agree st3 o m'' /\
  rpres_except (rmalloc_fp st0 st3 lo (bv_unsigned sp - 144)) m4 m'' /\
  mrel st2 st3 /\ brk_link_ps st3 s'' /\ ps_m s'' = ps_m s /\ ps_fa s'' = ps_fa s /\ ps_so s'' = ps_so s /\
  as_inv2 st0 st2 st3 (ncls sc cnt1) idx /\ 0 <= c_mmap_counter (ctx st3) < 2^32 /\
  rw_cells usegs m'' (bv_unsigned sp - 144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk) /\
  rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m4 /\ rmrep st2 m4.

Definition rNFAIL_stmt : Prop :=
  forall st1 st2 mm cnt1 st3 m4 m'' s' s'' errv'' junk oo o3 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  rnest_ctx st1 st2 mm cnt1 st3 (-1) m4 m'' s' s'' errv'' junk oo o3 ->
  rimplT o (free_meta mm st3 (fun st4 => as_kq sc k bail st4 None) bail) s'' Q
    (MS (rnest_regs st2 mm cnt1 (Z_to_bv 64 (-1)) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6')
        F (Z_to_bv 64 0x22dc8) fc None m'' (seg_rom usegs)).

Definition rNSUCC_stmt : Prop :=
  forall st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' junk oo o3 g3 b3 r3 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  rnest_ctx st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' junk oo o3 ->
  0 <= idx -> active st3 (ncls sc cnt1) = Some g3 -> slot_ok st3 g3 b3 r3 idx (nreq sc cnt1) ->
  (forall a, r_base r3 + snd b3 + 16 + get_stride (get_meta_rec st3 g3) * idx - 4 <= a
             < r_base r3 + snd b3 + 16 + get_stride (get_meta_rec st3 g3) * idx + get_stride (get_meta_rec st3 g3) - 4 ->
     rmalloc_fp st0 st3 lo (bv_unsigned sp - 144) a) ->
  (s_regions st0 = ∅ -> rdv pans_mem o st3 (fst b3, snd b3 + (16 + get_stride (get_meta_rec st3 g3) * idx) + -3) = 0) ->
  rimplT o (ag_tail full_lay (upd_meta mm (m_set_maplen 0) (nest_layout st3 g3 idx (ncls sc cnt1) (UNIT * size_class sc) cnt1))
              sc mm (slot_of st3 g3 idx) cnt1 (cnt1 - 1) (as_kq sc k bail)) s'' Q
    (MS (rnest_regs st2 mm cnt1 (Z_to_bv 64 idx) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6')
        F (Z_to_bv 64 0x22d54) fc None m'' (seg_rom usegs)).
End LEVEL.
End CANSEC1.
