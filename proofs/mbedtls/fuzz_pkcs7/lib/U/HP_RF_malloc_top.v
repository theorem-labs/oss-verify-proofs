(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import VirginDefs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocBlocks MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp F_malloc_enf F_malloc_join F_malloc_small F_malloc_entry F_malloc_core F_malloc_top.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_A HP_RMalloc_fp HP_RF_enframe HP_RF_malloc_enf HP_RAllocSlot_iface HP_RF_malloc_entry HP_RF_malloc_join HP_RF_malloc_small HP_RF_malloc_core HP_RMalloc_iface HP_RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require MallocFacts_inv2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RKitE4.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RF_malloc_top () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Heap.MallocFacts_A.MFACTS_g"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.ref_reserved"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.mrel"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.U.HP_RMalloc_fp.rmalloc_fp"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "RocqVerifyHarness.AgentSubmission.U.HP_RMalloc_iface.rheap_pres"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "stdpp.base.lookup"; "Corelib.Numbers.BinNums.N"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "Corelib.Init.Datatypes.fst"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.block"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.AREACH_from"; "Stdlib.NArith.BinNat.N.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_tick"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.size_class"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.set_tick"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.FUEL"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.active"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_mem"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.Heap.VirginDefs.under_virgin"].

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Section RP_1. Context {hRP : run_params}.
#[using="hRP"] Lemma rmembed_strel_follow {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : Malloc.M R1) (t2 : Malloc.M R2) :
  strel RR t1 t2 ->
  forall s (Q1 : R1 -> PState -> machine_state -> Prop) ms,
  implM rsegs (membed t1) s Q1 ms ->
  implM rsegs (membed t2) s
        (fun r2 s' ms' => exists r1 ans, follow t1 ans = Some r1 /\ follow t2 ans = Some r2 /\ RR r1 r2 /\ Q1 r1 s' ms') ms.
Proof. rceilb.
  induction 1 as [r1 r2 Hr | e k1 k2 Hk IH]; intros s Q1 ms H.
  - cbn [membed] in *. unfold implM, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' H1.
    dexists r1, []. cbn. auto.
  - cbn [membed] in *. unfold implM, mbind in *. unfold ebind in *.
    assert (UNR : forall A B (f : exc A -> itree node (exc B)) Qx msx,
              impl rsegs (at_node rsegs) (ITree.bind _ (Ret Unr) f) Qx msx = impl rsegs (at_node rsegs) (f Unr) Qx msx) by reflexivity.
    destruct e as [addr|addr len prot flags|addr len|addr len prot|p c h|w].
    5:{ cbn [ev_step] in *. unfold munr in *. cbn [ITree.bind] in *. exact H. }
    5:{ cbn [ev_step] in *. unfold munr in *. cbn [ITree.bind] in *. exact H. }
    all: eapply rimpl_bind_mono; [exact H|]; intros [|[z s']] ms' H1; cbn in H1 |- *; [exact H1|];
         eapply impl_epost_mono; [eapply IH; exact H1|];
         intros [r2' s2] ms2; cbn; (intros dd_H; ddestruct dd_H as (r1' & ans & F1 & F2 & HR & HQ));
         dexists r1', (z :: ans); cbn; auto.
Qed.


(* [comment removed for export] *)
#[using="hRP"] Lemma rimplT_silent {R} o (t : Malloc.M R) o' (x : R) s Q ms :
  mrun o t = SRet (o', x) -> rimplT o t s Q ms -> evt rsegs (Q x s) ms.
Proof. rceilb. intros E H. unfold rimplT in H. rewrite E in H. cbn [membed] in H. unfold implM, mret in H. cbn in H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L42613422559.22L47026689936.48L59308517873.48L59308579027.55L59308579027.58L59308579027.61L59308647913.57L59314873579.21L59314873579.54L59315137787.49L59321160778.6200000500600c01Q02602[03603P04=04U058S1a1HSS3hRP2lo2sp3CLO1a3blk4Hblk1H1r3HIB2RC3LOB3RI1S1a3blk4Hblk2rx3Hax1r3LOB2r12B13LR12H03HIB3RL1S1a3blk4Hblk2r'3Har1r3LOB2LR2H03HIB1HS1a3blk4Hblk2r'3Har1r3LOB2LR2H03HIB1HS1a3blk4Hblk2b'2r'3Has1E2DJS2lo2sp1a3Hsp1H3hRP3CLO2LSS1a3blk4Hblk2rx3Hax1r3LOB2r12B13LR11H3HIB3RL1S1a3blk4Hblk1r3LOB3HIB1XS2st1a3blk4Hblk2g'2b'2r'1i3Has1E2DJ". (* [comment removed for export] *)
#[using="Type"] Lemma rheap_pres_of_fp st st' LB lo sp m m' : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_top ()) "P,(0.$1.O7.O5.)P,(2.VhRP,O7.O2.)P,(2.VhRP,O6.O1.)P,(3.O7.O6.)P,(4.(5.VhRP,O7.O6.O4.O3.)O2.O1.)P,(6.(7.VhRP,)O4.)P,(6.O4.O3.)(8.O5.O3.O2.O1.)")
(* [comment removed for export] *).
Proof. rceilb.
  intros MF MR MR' REL PE CLO LS a Ha Hc. apply PE; [exact Ha|]. intros Hfp.
  destruct Hc as [Hsp | [[Himg Hns] | (blk & Hin & Hblk)]].
  - destruct (rmalloc_fp_cases st st' lo sp m m' a MR MR' Hfp); rceilb; lia.
  - destruct (rmalloc_fp_image st st' lo sp m m' a MR MR' Hfp CLO Himg); apply Hns; unfold ralloc_static, RERRNO, RATP, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP in *; lia.
  - ddestruct (rblock_inside st LB m blk MF MR Hin) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
    rceilb.
    pose proof MR' as (WF' & _). dpose WF' as (_ & WR' & DISJ' & _).
    pose proof MR as (WF & _). dpose WF as (_ & WR & DISJ & _).
    destruct REL as [RREG _ _]. destruct (RREG _ _ Hr) as (r1 & Hr1 & K1 & B1 & L1).
    pose proof (round_up_pg_mono _ _ L1) as RL1.
    pose proof (lr_lo_group r1 ltac:(rewrite K1; exact Hk)) as LR1. pose proof (lr_lo_group r Hk) as LR.
    destruct Hfp as [[H|[H|[H|(rid & rx & Hrx & Hkx & Hax)]]]|[(rid & rx & Hrx & Hn & Hax)|[(g' & b' & r' & i & Hm' & Hr' & Hk' & I0 & TB & Har & Has)|[(b' & gh & r' & Hg' & Hr' & Hk' & Har & Has)|FRESH]]]].
    + lia.
    + rewrite unsigned_lit in H by lia. lia.
    + unfold RCTX in H. lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr1 in Hrx; inversion Hrx; subst; congruence|].
      destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr in Hn; discriminate|].
      pose proof (lr_lo_ge rx). destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
      * destruct (mf_free_clear _ _ MF g' b' i Hm' I0 TB) as [_ HB].
        ddestruct (HB blk Hin (eq_sym E)) as (r'' & Hr'' & DJ). change (s_regions (strip st)) with (s_regions st) in Hr''.
        rewrite Hr' in Hr''. inversion Hr''; subst r''. change (get_meta_rec (strip st) g') with (get_meta_rec st g') in DJ. lia.
      * pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
      * pose proof (mf_hdr_clear _ _ MF b' gh blk r' Hg' Hin (eq_sym E) Hr') as DJ. lia.
      * pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
    + (* [comment removed for export] *)
      exfalso. pose proof (rfresh_live_region st a _ r FRESH Hr) as X. rewrite LR in X. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L20787318184.19L2431345234.23 L27371154578.20L44406688068.1900000800C00V00`S1p1r2P0S1n2N02bs1LS1p1r1n2P02PN2N02RIS1p1r1n2PN". (* [comment removed for export] *)
#[using="Type"] Lemma ruser_chunk st' m' (p : aptr) r n : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_top ()) "P,(2.VhRP,O5.O4.)P,(9.(:.$;.)(<.$=.$;.(>.$=.$?.$10.$;.)(11.$=.$?.$10.$;.)(12.$=.$13.O3.)(14.O5.))(15.$;.O2.))P,(9.$16.(17.O2.)$18.)P,(6.+10.(19.$=.$13.O3.))P,(6.(1:.(19.$=.$13.O3.)O1.)(1;.(1<.O2.)))P,(6.=O1.)(1=.(1>.(1?.&8.))Ljunk,(1>.(1?.&8.))(20.$21.O4.(22.O5.O3.)(23.$24.(25.(26.O1.)R1.)(27.$24.))))")
(* [comment removed for export] *).
Proof. rceilb.
  intros MR Hr Hk P0 PN N0.
  dpose MR as (WF & _ & _ & _ & _ & SH). destruct (SH (fst p) r Hr Hk) as [HW _].
  dpose (rregion_addr_facts st' m' (fst p) r MR Hr) as (R4 & _ & RC & RI). rceilb.
  rewrite (conc_region' st' p r Hr).
  assert (W : wr_at rsegs m' (r_base r + snd p) n) by (eapply wr_at_sub; [exact HW| lia| lia]).
  ddestruct (rwr_at_bytes_exist m' (r_base r + snd p) n W N0 ltac:(lia)) as (bs & L & B).
  exists bs. apply rw_cells_of_bytes; cbn; [| rewrite app_nil_r; exact B| rewrite Nat.add_0_r, Z2Nat.id by lia; exact W].
  split; [exact L| exact I].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_top ()) "Pst,$28.PLB,(1>.$29.)Pt,$=.Psc,$13.Pn,$13.P,(2:.$1.R5.R4.)P,(0.$1.R6.R5.)P,(2;.(2<.R7.)R5.)P,(2=.(6.=R5.)(2>.R5.+30.))P,(2=.(6.=R5.)(2>.R5.(2?.+2.+20.)))P,(6.(1:.R6.+4.)(30.+10.(31.R7.)))A5.Vas_pre,R;.(32.R9.R;.)R8.R7.$33.")
(* [comment removed for export] *).
Hypothesis AS_UV : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_top ()) "Pst0,$28.Pst,$28.Pst1,$28.Psc,$13.Pidx,$13.Pg,$34.Pb,$34.P,A5.Vas_inv,R7.R6.R5.R4.R3.P,(6.=R4.)P,(9.$35.(36.R7.R6.)(15.$34.R4.))P,(9.$35.(37.(38.R8.R5.))(15.$34.R4.))(39.R9.R6.R5.R7.)")
(* [comment removed for export] *).
Hypothesis RBIG : rbig_stmt.

(* [comment removed for export] *)
Definition rmidQ (o : mem) (st : mstate) (LB : list block) (s : PState)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
    (res : mstate * option cptr) (s' : PState) (ms' : machine_state) : Prop :=
  exists st2 r ans o1,
    fst res = strip st2
    /\ snd res = match r with Some (g, idx) => Some (slot_of st2 g idx) | None => None end
    /\ follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
    /\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
    /\ rcoreQ o o st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo (st2, r) s' ms'.

Local Ltac2 Set LiaOrc.tbl := fun () => "00M0@L1382125590.196 L14482897614.205L14495252695.202L17342775793.190L17420676655.199L2427054902.105 L2427085283.195 L2427169401.196 L26890170266.105L26890170266.201L28689910578.200L28691712593.104L28828785109.60 L29526439204.151L30153890386.70 L34772417402.202L3501531155.204 L40113305819.151L40661647848.195L42561211726.70 L43341390949.146L47028902922.198L59315137787.199L61937467957.200L63834722191.145L63836834993.146L8339798885.201 L8532415048.201 L8532582301.145 00001B02302]03G05305805k06^06b07V08P08Z09109^09b0:L0;@0;o0=40=>0=U0>F0?]0@W0@j0A=0BA0C60CMS1m1n3st21g3idx1b2rg6stride4lo_s4hi_s2B03S162NS2R42SK3st'1p1A3off4OFF03FIT4Eoff2EnS1n3st21g3idx1b2rg6stride4lo_s4hi_s2B03st'1p1A2EnS1n3st21g3idx1b2rg4lo_s4hi_s2B03st'1p1A2EnS1n3st21g3idx1b2rg4lo_s4hi_s2B03st'3off2EnS3hRP3RCB1m1n1N3st21g3idx1b2rg6stride2B03B164SPAN3S164SMOD2R43RAL2RC3RI12SK3SKL3st'1p1A3off4OFF03FIT4Eoff2EnS1n1NS1n1N3st21g3idx1b2rg6stride4lo_s4hi_s2B03st'1p1A2EnS1n1N3st21g3idx1b2rg6stride4lo_s4hi_s2B03st'1p1A2EnS2spS2sp1n3st21g3idx1b2rg6stride4lo_s4hi_s2B03st'1p1A2EnS2sp1n2lo2LO3st21g3idx1b2rg6stride4lo_s4hi_s2B03st'1p1A2EnS2sp2lo2LOS3hRP2sp2lo1B2SB3CLO2LOS2sp2lo2LO3st21g3idx1b2rg6stride4lo_s4hi_s2B0S2stS1n3st21g3idx1b2rg4lo_s4hi_s2B03st'1p1A2EnS1n3st21g3idx1b2rg6stride4lo_s4hi_s2B03st'1p1A2En2r1S3hRP2lo3CLO3st21g3idx1b2rg6stride4lo_s4hi_s2B0S1n3st21g3idx1b2rg4lo_s4hi_s2B04SPAN3S162NS2R43SKL3st'1p1A3off3FIT2EnS2sp2lo2LOS3st21g3idx1b2rg2B03IDXS1n3st21g3idx1b2rg6stride4lo_s4hi_s2B03st'1p1A2EnS3hRP3RCB2sp1n2lo3CLO3st21g1b2rg6stride2B03S162R43st'1p1A2En1a2Ha1X3idx4SPAN3RI12SK3SKLS1n3st21g3idx1b2rg6stride2B04SPAN3S162R42SK3SKL3st'1p1A2EnS3st21g1b2rg2B03S16S3st21g1b2rg2B03S16S1n3st21g3idx1b2rg6stride4lo_s4hi_s2B03S162R42SK3st'1p1A3off4OFF02EnS1n3st21g3idx1b2rg6stride4lo_s4hi_s2B03IDX3st'1p1A2EnS3st21g3idx1b2rg2B03IDX". (* [comment removed for export] *)
#[using="as_pre as_inv RAS AS_PRE AS_UV RBIG"] Theorem rmalloc_spec_proof : rmalloc_stmt.
Proof. rceilb.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
  intros HEAP AUXB SB ST CLO LO ERR MI TP HA N. unfold RMALLOC_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0.
  assert (AUX : rauxv_ok m (bv_unsigned sp)) by (eapply rauxv_ok_weaken; [exact AUXB| rceilb; lia]).
  ddestruct HEAP as (st & LB0 & HPERM & Hst & MR & [BLK AR]). rename LB into LBc. rename LB0 into LB.
  pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (HIN : forall b, In b LBc -> In b LB) by (intros b Hb; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HPERM| exact Hb]).
  pose proof (proj2 (brk_link_ps_iff st s) BLK) as BL.
  (* [comment removed for export] *)
  eapply (implM_evt rsegs _ _ _ (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                   F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs))).
  { unfold RMALLOC_SYM. step. apply evt_done. reflexivity. }
  intros ms' ->.
  unfold raw_malloc.
  eapply (implM_bind rsegs _ _ _ (fun a sa msa => a = s /\ sa = s /\ msa = _)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  (intros s0' s1' ms1 dd_H; ddestruct dd_H as (-> & -> & ->)). cbv beta.
  eapply (implM_bind rsegs _ _ _ (rmidQ m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)).
  { rewrite <- Hst. unfold cmalloc.
    eapply (rimplM_membed_sbind _ _ s (fun x s' ms' => exists st2 r ans o1,
              x = (strip st2, r)
              /\ follow (mrun m (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
              /\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
              /\ rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo (st2, r) s' ms')).
    - eapply implM_mono.
      + eapply (rmembed_strel_follow CREL).
        * pose proof (malloc_core_ctrl pans_mem pupd_mem n m (set_tick (N.succ (s_tick st)) st) (strip st)) as X.
          unfold mrun. apply X. rewrite strip_set_tick. reflexivity.
        * unfold rimplT in |- *.
          pose proof (rmalloc_core_implT as_pre as_inv RAS AS_PRE AS_UV RBIG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                        m st LB s n lo errv (N.succ (s_tick st)) AR MF MR BL AUX ST CLO ltac:(lia) ERR MI TP HA N ltac:(lia)) as X.
          unfold rimplT in X. exact X.
      + (intros [cst2 r'] s' ms'' dd_H; ddestruct dd_H as ([o1 [st2 r]] & ans & F1 & F2 & HC & CQ)). unfold CREL in HC. cbn in HC, CQ. destruct HC as [Hs Hr]. subst cst2 r'.
        dexists st2, r, ans, o1. split; [reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ].
    - (intros [cst2 r'] s' ms'' dd_H; ddestruct dd_H as (st2 & r & ans & o1 & E & F1 & F2 & CQ)). inversion E; subst. clear E.
      apply implM_ret. apply evt_done. unfold rmidQ. dexists st2, r, ans, o1. cbn [fst snd].
      split; [reflexivity|]. split; [destruct r as [[g idx]|]; reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ]. }
  intros [cs c] s' ms'' MQ. cbv beta iota.
  ddestruct MQ as (st2 & r & ans & o1 & Ecs & Ec & F1 & F2 & CQ). cbn [fst snd] in Ecs, Ec. subst cs c.
  pose proof (mrun_fst _ _ _ _ _ F1) as Eo1. subst o1.
  eapply (implM_bind rsegs _ _ _ (fun _ sx msx => sx = set_m (strip st2) s' /\ msx = ms'')).
  { apply implM_upd. apply evt_done. split; reflexivity. }
  intros [] sx msx [-> ->]. apply implM_ret.
  (* [comment removed for export] *)
  assert (FC : forall y, (forall ans', follow ((fun '(st1, r0) => ret (strip st1, match r0 with
                                   | Some (g, idx) => Some (slot_of st1 g idx) | None => @None aptr end)) (strip st2, r)) ans' = Some y) ->
               follow (cmalloc (strip st) n) ans = Some y).
  { intros y Hy. unfold cmalloc. eapply follow_sbind; [exact F2| exact Hy]. }
  destruct r as [[g idx]|].
  - (* [comment removed for export] *)
    cbn [rcoreQ] in CQ.
    ddestruct CQ as (b & rg & m1 & errv1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & s4' & u3 & u4 & u5 & u6 & ra' & -> &
                    MR2 & TK2 & UA2 & MI2 & ST2 & FR2 & ERR2 & AUX2 & PE2 & SPANFP & CTR2 & SO & UV2 & EXPO & MREL & BL2 & PSM & PSF & PSO).
    pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
    dpose (rregion_addr_facts st2 m1 (fst b) rg MR2 Hr) as (R4 & RAL & RC & RI1).
    assert (SK : 0 <= get_stride (get_meta_rec st2 g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
    assert (SKL : get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) <= get_stride (get_meta_rec st2 g) * (m_last_idx (get_meta_rec st2 g) + 1)).
    { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
    set (stride := get_stride (get_meta_rec st2 g)) in *.
    set (lo_s := r_base rg + snd b + 16 + stride * idx - 4) in *.
    set (hi_s := r_base rg + snd b + 16 + stride * idx + stride - 4) in *.
    set (Cf := fun a => lo <= a < bv_unsigned sp \/ lo_s <= a < hi_s).
    rceilb. unfold RMALLOC_STACK in LO.
    pose proof (renf_implT sp gp tp u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra' ra s0 s1 s2 s3 s4 F fc m m1 m1 s' st2 g b rg idx n lo Cf
                  MR2 TK2 UA2 MI2 ST2 ltac:(rceilb; lia) ltac:(lia) FR2 (rpres_except_refl _ _)
                  ltac:(intros a Ha; left; exact Ha) ltac:(intros a Ha; right; subst lo_s hi_s stride; exact Ha) CTR2 SO UV2) as ENF.
    pose proof (mrun_enframe_full m st2 g b idx n (c_mmap_counter (ctx st2)) Hmem) as RUN. cbv zeta in RUN.
    pose proof (rimplT_silent _ _ _ _ _ _ _ RUN ENF) as EV. clear ENF. cbv beta in EV.
    eapply evt_mono; [exact EV|]. clear EV.
    intros msf [_ EP]. unfold renf_post in EP.
    ddestruct EP as (st' & p & w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & ER & -> & MI' & ST' & MR' & TK' & PE' & ZB & LEAF).
    ddestruct LEAF as (off & OFF0 & FIT & Ep & Est' & Ep2 & Eoff).
    assert (SE : strip st' = strip st2) by (rewrite Est', strip_havoc, strip_enframe_at; reflexivity).
    pose proof (strip_eq_proj _ _ SE) as (Ec & Er & En & Em & _ & _ & Esl & Es).
    assert (HrS : (s_regions st') !! (fst p) = Some rg) by (rewrite Er, Ep; cbn [fst]; exact Hr).
    assert (EA : conc st' p = r_base rg + snd b + 16 + stride * idx + 16 * off).
    { rewrite (conc_region' st' p rg HrS). rewrite Ep. cbn [snd]. subst stride. lia. }
    set (A := conc st' p) in *.
    (* [comment removed for export] *)
    assert (FF : follow (mrun m (malloc st n)) ans = Some (m, (st', Some p))).
    { unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
      eapply follow_sbind; [exact F1|]. intros ans'. cbn [fst snd]. unfold mrun, prun in RUN. rewrite RUN. cbn. rewrite ER. reflexivity. }
    pose proof (FC (strip st2, Some (slot_of st2 g idx)) ltac:(intros ans'; cbn; rewrite strip_strip; reflexivity)) as FC1.
    pose proof (areach_malloc_some st LB n m m ans st' p (strip st2) (slot_of st2 g idx) AR ltac:(lia) FF FC1) as AR'.
    destruct (ruser_chunk st' m' p rg n MR' HrS Hk ltac:(rewrite Ep; cbn [snd]; lia) ltac:(rewrite Ep; cbn [snd]; subst stride; lia) ltac:(lia)) as (ujunk & UCH).
    fold A in UCH.
    unfold rmalloc_post. deexists 15. dexists m', errv1.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE'| exact ERR2|]. rewrite TP. unfold RATP. rewrite unsigned_lit by lia.
             change (Z.of_nat (cells_size [C4 errv1])) with 4. intros a Ha [X|X]; subst lo_s hi_s.
             - lia.
             - lia. }
    assert (MRELf : mrel st st') by (eapply mrel_trans; [exact MREL|]; apply mrel_same; assumption).
    assert (PEf : rpres_except (rmalloc_fp st st' lo (bv_unsigned sp)) m m').
    { eapply rpres_except_mono.
      + eapply rpres_except_trans; [exact PE2|].
        eapply rpres_except_mono; [exact PE'|]. intros a [X|X]; [left; left; exact X| apply SPANFP; subst lo_s hi_s stride; exact X].
      + intros a Ha. eapply rmalloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. rewrite Er. repeat split; auto; lia. }
    pose proof (rheap_pres_of_fp st st' LB lo (bv_unsigned sp) m m' MF MR MR' MRELf PEf CLO ltac:(lia)) as HPf.
    split. { eapply (rauxv_ok_malloc_fp st st' lo (bv_unsigned sp) m m' m m' B); [exact MR| exact MR'| exact AUXB| exact PEf| exact CLO| exact SB]. }
    split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
    split; [exact PSF|]. split; [exact PSO|].
    dexists A, ujunk.
    split; [reflexivity|].
    split. { rceilb; unfold rblock_range. rewrite EA.
             split; [lia|]. split; [apply mod16_slot; [exact RAL| exact B16| exact SMOD| lia]|]. subst lo_s hi_s.
             specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)). lia. }
    split. { exists st'. eexists. split; [apply Permutation.perm_skip; exact HPERM|]. split; [exact SE|]. split; [exact MR'|]. split.
             - apply (proj1 (brk_link_ps_iff st' _)). cbn. unfold brk_link_ps in *. unfold ctx in *. rewrite Ec. unfold conc, get_region. rewrite Er. exact BL2.
             - exact AR'. }
    split; [exact UCH|].
    split.
    2:{ (* [comment removed for export] *)
        intros g' i' SL' UND'. cbn [ps_m set_m fst] in SL', UND'.
        change (s_slots (strip st2)) with (s_slots st2) in SL'. change (get_meta_rec (strip st2) g') with (get_meta_rec st2 g') in UND'.
        unfold slot_of, slot_start' in SL'. rewrite Hmem in SL'. cbn [default from_option id] in SL'. unfold aadd in SL'. cbn [fst snd] in SL'.
        replace (snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) with (snd b + 16 + get_stride (get_meta_rec st2 g) * idx) in SL' by (unfold UNIT; lia).
        rewrite SSL in SL'. injection SL' as <- <-.
        pose proof (ZB UND') as BZ.
        destruct UCH as [[WFu BAu] _]. cbn [cells_wf cell_wf cells_bytes cbytes] in WFu, BAu. rewrite app_nil_r in BAu.
        apply (bytes_at_inj m' A); [exact BAu| exact BZ| rewrite repeat_length; destruct WFu as [WFu _]; exact WFu]. }
    (* [comment removed for export] *)
    intros AE. unfold ptr_addr. cbn [ps_m set_m fst snd].
    assert (X0 : rdv pans_mem m st2 (fst b, snd b + (16 + stride * idx) + -3) = 0).
    { apply EXPO. destruct AE as [AE|AE]; [left; exact AE| right].
      pose proof (f_equal s_regions Hst) as E0. rewrite AE in E0. cbn in E0. exact E0. }
    unfold slot_of, slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd. cbn [fst snd].
    match goal with |- context [conc (strip st2) ?q] => change (conc (strip st2) q) with (conc st2 q) end.
    rewrite (conc_region' st2 (fst b, snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) rg Hr). cbn [snd].
    unfold fresh_off. cbn [s_slots strip].
    replace (snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) with (snd b + 16 + stride * idx) by (subst stride; unfold UNIT; lia).
    rewrite SSL. change (c_mmap_counter (s_ctx (strip st2))) with (c_mmap_counter (ctx st2)).
    rewrite EA, Eoff. unfold enf_off0. rewrite X0. cbn [Z.eqb]. subst stride. unfold IB, UNIT.
    change (get_meta_rec (strip st2) g) with (get_meta_rec st2 g). lia.
  - (* [comment removed for export] *)
    cbn [rcoreQ] in CQ.
    ddestruct CQ as (m1 & errv1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> &
                    MR2 & TK2 & MI2 & ST2 & ERR2 & AUX2 & PE2 & MREL & BL2 & PSM & PSF & PSO).
    apply evt_done. unfold rmalloc_post. deexists 15. dexists m1, errv1.
    pose proof (rheap_pres_of_fp st st2 LB lo (bv_unsigned sp) m m1 MF MR MR2 MREL PE2 CLO ltac:(lia)) as HPf.
    split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|].
    split. { eapply (rauxv_ok_malloc_fp st st2 lo (bv_unsigned sp) m m1 m m1 B); [exact MR| exact MR2| exact AUXB| exact PE2| exact CLO| exact SB]. }
    split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
    split; [exact PSF|]. split; [exact PSO|].
    split; [reflexivity|].
    dexists st2, LB. split; [exact HPERM|]. split; [reflexivity|]. split; [exact MR2|].
    split.
    + apply (proj1 (brk_link_ps_iff st2 _)). cbn. exact BL2.
    + eapply (areach_malloc_none st LB n m m ans st2 AR ltac:(lia)).
      unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
      eapply follow_sbind; [exact F1|]. intros ans'. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End TOPLEVEL.


End RP_1.
