(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk Scfg ShapeAlg SpinAlg Hoare AgentLib MmapSim AllocSim RefNodes HeapIface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP MState Mem Cells Step Frame Exec ITree Nodes Decode Image Tac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import Prelim STree Malloc MallocCtrl Monad Prog KInv KStep MI_Kit MI_Inv MI_Sim MI_Ledger MI_Contracts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocHINV MallocBlocks Malloc_iface MallocFacts_A MallocFacts_inv2 F_free F_free_spec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import F_syscalls RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP RF_malloc_top RF_malloc_spec RF_free_spec RF_aligned RF_aligned_spec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge Require Import BrRegs BrBase BrXfer BrMem KLink BrRes Embed.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Bridge_HeapInst0 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocBlocks."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.BrRegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.BrRes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.Embed."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.HeapInst0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.HeapInst0.LAYOUT."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.HeapInst0.LAYOUT.INST2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Decode."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RF_aligned_spec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMalloc_iface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.KInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Prog."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.Bool.Bool."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.decidable."; "stdpp.list_basics.list."], [["0A"; "1None"; "1Some"; "1bool"; "1cons"; "1false"; "1fst"; "1list"; "1negb"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2and"]; ["2eq"; "2ex"; "2iff"; "2not"; "3Forall"; "3map"; "4Z"; "0H"; "0LB"; "0LBb"; "0LBb'"; "5wview"; "6VmMaps"; "6reserved_top"; "7bvmap"; "0M"]; ["0PA"; "0R"; "0R'"; "0RUNp"; "8lbrm"; "9blk_addr"; "9blk_size"; "9blk_slot"; "9block"; ":wz"; ";mem"; "<regs_eqv"; "=AMC"; "=CALLB"; "=elen_ok"; "=is_fixed"]; [">NMAX"; "?BOV"; "?IMG_HI"; "?IMG_LO"; "@HI0"; "AframeW"; "@L0"; "@blk_iv"; "@init_statics0"; "?POTMAX"; "?RESV"; "BC4"; "Bcell"; "Cmmap_len"; "Divl"; "DmkR"]; ["Doutside"; "Dstk"; "Eret_pc"; "Fmrd"; "Fro_addr"; "Fwa"; "Galloc_ceiling"; "Hrw_cells"; "Irsegs"; "JRALIGNED_STACK"; "KRCTX"; "KRERRNO"; "LRHEAP"; "Lrclient_write_ok"; "Lrdeep_pres"; "Lrheap_pres"]; ["Lrimg_pres"; "Map_remove"; "NEMmap"; "Naptr"; "Naptr_eqb"; "Ncptr"; "Nsize_overflows"; "OPState"; "Obptr"; "Paligned_alloc16_spec"; "Palloc_private"; "Pfree_null_spec"; "Pfree_spec"; "Pheap_blocks_wf"; "Pheap_frame"; "Pheap_iface_ok"]; ["Pheap_perm"; "Pheap_pres_core"; "Phi_heap"; "Phl_B0"; "Phl_K0"; "Pinit_vm"; "Plb_remove"; "Pmalloc_spec"; "Pregs_preserved"; "Pstack_ok"; "Qret_ok"; "Rgetr"; "Rjalr_tgt"; "0SCFG"; "SIs_true"; "TIn"]; ["TNoDup"; "Tfilter"; "Uadd"; "Ueqb"; "Ule"; "Ult"; "Upow"; "Usub"; "0VM"; "0W"; "0a"; "0a0"; "0a1"; "0a2"; "0a3"; "0a4"]; ["0a5"; "0a6"; "0a7"; "0b"; "0b'"; "0blk"; "0c"; "0flags"; "0i"; "0iv"; "0k"; "0l"; "0len"; "0lim"; "0m"; "0m'"]; ["0n"; "0p"; "0prot"; "0ra"; "0s"; "0sp"; "0sptop"; "Vfilter"; "WBV"; "WBvWf"; "WZ_to_bv"; "Wbv"; "Wbv_unsigned"; "XIs_true_dec"; "Ylist_filter"; "0t0"]; ["0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0v"; "0x"; "0y"; "0z"]]).
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Definition KPM : Z := Z.of_nat EVM.
Definition NCMAX : Z := 1000.
Definition K0 : Z := KPM * NCMAX.
Definition POTMAX : Z := POT0 + AMC * NCMAX.
Definition LNMAX : Z := (2 * PGSZ * (POTMAX + AMC)) / NSLOTS.
Definition BOV : Z := GMAX + IB + UNIT + PGSZ + LNMAX + 2 * PGSZ.
Definition B0 : Z := 2^33.
Definition NSEG : Z := 4.
Definition IMG_LO : Z := 0x10000.
Definition IMG_HI : Z := 0xe9000.
Definition RESV : list (word * word) := segments_reserved rsegs.
Lemma RESV_eq : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "Q7'@'7'<'TKyR0%211%4211%611&QJ(4(;&TJ+RPP0%2291+T\P0%42;1%64;;31+V\P0%72>1+_`P0%92@1%;4@@31+elP0%<2C1+hP0%>2E1%@4EE31+fdP0%A2H1+V`P0%C2J1%E4JJ31(9%11K%I3L31%J3M91%K3N?1%L3OE1%Q63ON1").
Proof. vm_compute. reflexivity. Qed.
Lemma CALLB_le : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "H'F&SDzr2%3221&SB&QI&Q<%3221%8261'?&Q=r4r3%3221%>2=1&QA%<251%A241%9241p0;1p0A1pR2F1pY2G1").
Proof.
intros n PA Hn HPA. unfold CALLB, BOV, LNMAX.
pose proof (mmap_len_ge (n + IB + UNIT) ltac:(unfold IB, UNIT; lia)) as H1. unfold mmap_len in H1. rewrite <- round_up_pg_eq in H1.
assert (2 * PGSZ * PA / NSLOTS <= 2 * PGSZ * (POTMAX + AMC) / NSLOTS).
{ apply Z.div_le_mono; [reflexivity|]. unfold PGSZ. lia. }
assert (0 <= 2 * PGSZ * (POTMAX + AMC) / NSLOTS) by (apply Z.div_pos; [unfold PGSZ, POTMAX, POT0, AMC, NCMAX, NSLOTS; lia| reflexivity]).
unfold GMAX, IB, UNIT, PGSZ in *. lia.
Qed.
Section LAYOUT.
Variable sptop : Z.
Definition L0 : heap_layout := {|
hl_segs := rsegs;
hl_malloc := RMALLOC_SYM;
hl_free := RFREE_SYM;
hl_aligned_alloc := RAA_SYM;
hl_tp := RATP;
hl_errno := RERRNO;
hl_img_lo := IMG_LO;
hl_img_hi := IMG_HI;
hl_alloc_static := fun a => RMLOCK <= a < RCTX + 928;
hl_alloc_ro := fun a =>
(IMG_LO <= a < 0xaf000)
\/ (RLIBC <= a < RMLOCK)
\/ (RCTX + 928 <= a < RCTX + 936)
\/ (RGOT_SSP <= a < RGOT_SSP + 8)
\/ (RSSP_GUARD <= a < RSSP_GUARD + 8)
\/ (RVMLOCKC <= a < RVMLOCKC + 4)
\/ (sptop <= a);
hl_stack := RALIGNED_STACK;
hl_sptop := sptop;
hl_k_per_malloc := KPM;
hl_b_overhead := BOV;
hl_K0 := K0;
hl_B0 := B0 |}.
Definition blk_iv (b : block) : Z * Z := (blk_addr b, blk_size b).
Definition hi_heap0 (LB : list (Z * Z)) (cr : credit) (M : word -> option byte) (VM : VmMaps) : Prop :=
exists (RUNp : RunP) (s : PState) (L : mled) (LBb : list block) (ncalls : Z),
alloc_ceiling = sptop - 2 ^ 23
/\ LB = map blk_iv LBb
/\ RHEAP s LBb M
/\ creach (ps_m s) L
/\ Permutation (ld_live L) (map blk_slot LBb)
/\ KL2 RESV IMG_HI L (ps_brk s) VM
/\ mem_inv rsegs M
/\ rauxv_ok M sptop
/\ (forall a : word, RCTX + 928 <= bv_unsigned a < RCTX + 936 -> M a = None)
/\ Forall (fun b => 0 < blk_size b /\ forall i, 0 <= i < blk_size b -> M (wa (blk_addr b + i)) <> None) LBb
/\ 0 <= ncalls /\ KPM * ncalls + fst cr <= K0 /\ 0 <= fst cr /\ 0 <= snd cr
/\ pot (ps_m s) <= POT0 + AMC * ncalls
/\ Z.of_nat (length (vm_reserved VM ++ vm_maps VM)) + fst cr <= K0 + NSEG
/\ Forall (fun p => bv_unsigned (snd p) <= NMAX) (vm_reserved VM ++ vm_maps VM)
/\ live_bytes (vm_maps VM) + snd cr <= B0
/\ B0 <= vm_limit VM.
Definition HI0 : heap_iface := {| hi_heap := hi_heap0 |}.
Definition init_statics0 (M : word -> option byte) : Prop :=
(forall a : word, 0xe8068 <= bv_unsigned a < 0xe8418 -> M a = None)
/\ (forall a : word, RVMLOCKC <= bv_unsigned a < RVMLOCKC + 4 -> M a = None)
/\ rw_cells rsegs M 0xe7ef3 [C1 (Z_to_bv 8 0)]
/\ rw_cells rsegs M 0xe7f20 [C8 (Z_to_bv 64 4096)]
/\ rw_cells rsegs M 0xb4ec8 [C8 (Z_to_bv 64 0xe7ed0)]
/\ (exists canary : Z, 0 <= canary < 2 ^ 64 /\ rw_cells rsegs M 0xe7ed0 [C8 (Z_to_bv 64 canary)])
/\ (exists (av x3 x4 x5 hw x6 x11 x12 x23 rnd secret : Z),
rw_cells rsegs M 0xe7ef8 [C8 (Z_to_bv 64 av)]
/\ bytes_at rsegs M av (u64s (map (Z_to_bv 64) [3; x3; 4; x4; 5; x5; 16; hw; 6; x6; 11; x11; 12; x12; 23; x23; 25; rnd; 0; 0]))
/\ bytes_at rsegs M (rnd + 8) (le8 (Z_to_bv 64 secret))
/\ sptop <= av /\ av + 160 <= 2 ^ 64 /\ sptop <= rnd + 8 /\ rnd + 16 <= 2 ^ 64
/\ 0 <= x3 < 2 ^ 64 /\ 0 <= x4 < 2 ^ 64 /\ 0 <= x5 < 2 ^ 64 /\ 0 <= hw < 2 ^ 64 /\ 0 <= x6 < 2 ^ 64
/\ 0 <= x11 < 2 ^ 64 /\ 0 <= x12 < 2 ^ 64 /\ 0 <= x23 < 2 ^ 64 /\ 0 <= rnd < 2 ^ 64 /\ 0 <= secret < 2 ^ 64)
/\ mem_inv rsegs M.
Section INST.
Context {RUNp : RunP}.
Hypothesis HCEIL : alloc_ceiling = sptop - 2 ^ 23.
Section SE.
Local Abbreviation SEC_T_stack_ok_stk := (ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "Q<'TKyR0%211':y8%511%311p051'F&S9&QFr2r1%43321'?&R1&R8r3&SG&R9%2291%64541:&SD&R6vQ3%211%4216vTF%62A1z%821C&SE&SF+2+QO%3221%52I1%G271%H2:1%I2=1%J2C1p0L1pY<Q21pR0Q41")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_stack_ok_stk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_stack_ok_stk) 1%nat 0%nat).
Lemma stack_ok_stk : ltac:(sec_stmt2 constr:(SEC_T_stack_ok_stk) 2%nat 0%nat).
Proof.
intros (Hal & Hlo & Hhi & Htop & Hst).
cbn [hl_stack hl_sptop hl_segs L0] in *.
rewrite HCEIL. unfold RALIGNED_STACK, RMALLOC_STACK in *.
split; [| lia]. split; [lia|]. split; [lia|].
intros a Ha.
assert (Hwa : bv_unsigned (wa a) = a) by (unfold wa; apply u64_lit; lia).
pose proof (Hst (a - (sp - (8192 + 32))) 1%nat ltac:(lia) ltac:(cbn; lia)) as S1.
replace (sp - (8192 + 32) + (a - (sp - (8192 + 32)))) with a in S1 by lia.
pose proof (store_ok_all rsegs M 1 (wa a) ltac:(rewrite Hwa; cbn; lia) S1 (wa a) ltac:(rewrite Hwa; cbn; lia)) as W.
split; [exact W|].
rewrite ref_wview_overlay in W by (rewrite Hwa; lia). rewrite ref_mrd_overlay by (rewrite Hwa; lia).
destruct (M (wa a)) as [b|]; [exists b; reflexivity| congruence].
Qed.
End SE.
Lemma block_ge_4096 : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "H'RG'7&Q8%211&Q:&R<vQ3r4r3r2%544321&S?%13:35&SD+TP0&Q5%118%4231p061p091pX8B1pR0A1pQDC1pY:G1").
Proof.
intros s LBb M b (st & LB0 & HP & Hst & MR & [HI1 AR]) Hin.
pose proof (areach_facts_proof _ _ AR) as MF.
assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hin]).
destruct (rblock_inside st LB0 M b MF MR IN0) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
lia.
Qed.
Lemma NoDup_map_transfer : forall {A B C} (f : A -> B) (g : A -> C) (l : list A),
List.NoDup (map f l) -> (forall x y, In x l -> In y l -> f x <> f y -> g x <> g y) -> List.NoDup (map g l).
Proof.
intros A B C f g l. induction l as [|a l IH]; intros Hnd Hfg; cbn in *; [constructor|].
inversion Hnd as [|? ? Hni Hnd']; subst. constructor.
- intros Hin. apply in_map_iff in Hin as (y & Ey & Hy).
apply (Hfg a y (or_introl eq_refl) (or_intror Hy)); [| symmetry; exact Ey].
intros Ef. apply Hni. rewrite Ef. apply in_map. exact Hy.
- apply IH; [exact Hnd'|]. intros x y Hx Hy. apply Hfg; right; assumption.
Qed.
Lemma lb_remove_filter : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "Q6'F'7'<%1233%311'S@&E&6%1288r1%447:21%62;1&S?(;r4r3%34@@21r2%63?21'@&S6r5%2217&SA&8&SC%C3JJAr6%3221%511qX8K1%83L1@%=3L:1p0?1p0G1pQBO1pY2Q41p2Q51").
Proof.
intros A n LB. induction LB as [|b LB IH]; intros Hnd Hin; [destruct Hin|]. cbn.
cbn in Hnd. inversion Hnd as [|? ? Hni Hnd']; subst.
destruct (Z.eqb_spec (fst b) A) as [E|NE]; cbn [negb].
- symmetry. apply List.forallb_filter_id. apply forallb_forall. intros x Hx.
destruct (Z.eqb_spec (fst x) A) as [Ex|Nx]; [|reflexivity]. exfalso. apply Hni. rewrite E, <- Ex. apply in_map. exact Hx.
- f_equal. apply IH; [exact Hnd'|]. destruct Hin as [->|Hin]; [cbn in NE; congruence| exact Hin].
Qed.
Lemma hi0_nodup_addr : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "QJ'RG'7&Q8%211&Q:&R<vQ3r3r2r1%544321'D'?&SEz&Q6%117%4231'F&SD%126;%61=%92=1%;231&C'@':'TKy8%211%411r5&R5&SB&Q5%11L%321L%511%711(1%11;%@3;31%B11p0D1pXBJ1%Q12L1qX8Q<1%Q43Q=1Q8'S@&Er4%24QAQ1A1%42Q21p061p0Q<1pR0QC1pQDQE1pY:QI1").
Proof.
intros s LBb M HR BLK. apply (NoDup_map_transfer blk_id blk_addr LBb (RHEAP_blocks_nodup_proof s LBb M HR)).
intros x y Hx Hy Hne Ea.
pose proof (RHEAP_blocks_disjoint_proof s LBb M x y HR Hx Hy Hne) as D.
pose proof (proj1 (List.Forall_forall _ _) BLK x Hx) as [Sx _]. pose proof (proj1 (List.Forall_forall _ _) BLK y Hy) as [Sy _]. lia.
Qed.
Lemma map_fst_blk_iv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "C'7&Q8%211'@'F%511&E'<%1244&6%1266&QGr1%74<521%846:41&Q5%:4?<14%>3<31pQD@1").
Proof. intros. rewrite map_map. reflexivity. Qed.
End INST.
Lemma HI0_wf : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "4&RM&QF&QD%3221").
Proof.
intros LB cr M VM (RUNp & s & L & LBb & nc & HCEIL & ELB & HR & CR & PL & HK & MI & AUX & REPL & BLK & Hnc & Hk & Hfst & Hsnd & POT & LEN & FA & LIVE & LIM).
pose proof (hi0_nodup_addr s LBb M HR BLK) as ND. rewrite <- map_fst_blk_iv, <- ELB in ND.
split; [| split; [apply NoDup_ListNoDup; exact ND| split; [exact Hfst| exact Hsnd]]].
intros b Hb. pose proof Hb as Hb0. rewrite ELB in Hb. apply in_map_iff in Hb as (bb & <- & Hbb). cbn [fst snd blk_iv].
pose proof (proj1 (List.Forall_forall _ _) BLK bb Hbb) as [Sz Def].
pose proof (RHEAP_block_range_proof s LBb M bb HR Hbb) as (R1 & R2 & R3 & R4 & R5).
split; [| split].
- unfold HeapIface.block_range. cbn [hl_img_lo hl_img_hi hl_sptop L0]. splits.
+ exact (block_ge_4096 s LBb M bb HR Hbb).
+ unfold IMG_LO, IMG_HI. exact R5.
+ exact R2.
+ exact Sz.
+ rewrite <- HCEIL. exact R4.
- intros i Hi. exact (Def i Hi).
- intros b' Hb'. rewrite (lb_remove_filter (blk_addr bb) (blk_size bb) LB ND Hb0) in Hb'.
apply filter_In in Hb' as [Hb' Hne]. rewrite ELB in Hb'. apply in_map_iff in Hb' as (bb' & <- & Hbb'). cbn [fst snd blk_iv] in *.
destruct (Z.eqb_spec (blk_addr bb') (blk_addr bb)) as [E|NE]; [discriminate|].
assert (Hid : blk_id bb <> blk_id bb').
{ intros Eid. apply NE. symmetry. f_equal. exact (nodup_map_inj blk_id LBb bb bb' (RHEAP_blocks_nodup_proof s LBb M HR) Hbb Hbb' Eid). }
pose proof (RHEAP_blocks_disjoint_proof s LBb M bb bb' HR Hbb Hbb' Hid). lia.
Qed.
Lemma HI0_perm : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "3&S0&QD%211").
Proof.
intros LB LB' cr M VM (RUNp & s & L & LBb & nc & HCEIL & ELB & HR & CR & PL & HK & MI & AUX & REPL & BLK & REST) Hiff Hnd'.
pose proof (hi0_nodup_addr s LBb M HR BLK) as ND. rewrite <- map_fst_blk_iv, <- ELB in ND.
apply NoDup_ListNoDup in Hnd'.
assert (HP : Permutation LB LB').
{ apply Permutation.NoDup_Permutation; [eapply List.NoDup_map_inv; exact ND| eapply List.NoDup_map_inv; exact Hnd'| exact Hiff]. }
rewrite ELB in HP. apply Permutation_sym in HP.
destruct (Permutation_map_inv _ _ HP) as (LBb' & -> & HPb).
exists RUNp, s, L, LBb', nc. splits; try (apply REST).
- exact HCEIL.
- reflexivity.
- eapply RHEAP_perm; [exact HR| exact HPb].
- exact CR.
- eapply Permutation_trans; [exact PL|]. apply Permutation_map. exact HPb.
- exact HK.
- exact MI.
- exact AUX.
- exact REPL.
- apply List.Forall_forall. intros b Hb. apply (proj1 (List.Forall_forall _ _) BLK).
eapply Permutation_in; [apply Permutation_sym; exact HPb| exact Hb].
Qed.
Section INST2.
Context {RUNp : RunP}.
Hypothesis HCEIL : alloc_ceiling = sptop - 2 ^ 23.
Lemma errno_byte : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "QA'TKyR0%211':y8%511%311p051'F'?&SDzr1%3221&SE+4%2241%8241'A'@&R3&R8r4&R5&SB&R;r3%3221%511%93871(2%12JC%=3J31qX8L1%@2M1&C&Kr2%>2=1%@11%43C>1(1%11Q5%H3Q531%911%Q42;1p0M1pXBQ71pXNQ91").
Proof.
intros m i Hi.
assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
unfold mrd, wview, RERRNO.
destruct E as [-> |[-> |[-> | ->]]]; cbn [Z.add];
(destruct (m (wa _)) as [b|]; [split; [exists b; reflexivity| discriminate]|]);
(split; [eexists; vm_compute; reflexivity| vm_compute; discriminate]).
Qed.
Lemma errno_cell_any : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "I'TKyR0%211':y8%511%311p051'A&R7&R8r2&R;(4'QL(QKr1%211(9%115%73631%<4;:91qZ>D1%?2E1pXNA1").
Proof.
intros m.
destruct (proj1 (errno_byte m 0 ltac:(lia))) as [b0 E0]. destruct (proj1 (errno_byte m 1 ltac:(lia))) as [b1 E1].
destruct (proj1 (errno_byte m 2 ltac:(lia))) as [b2 E2]. destruct (proj1 (errno_byte m 3 ltac:(lia))) as [b3 E3].
destruct (le4_of_bytes b0 b1 b2 b3) as [v Ev]. exists v.
split; [split; [exact (conj I I)|]|].
- cbn [cells_bytes cbytes]. rewrite Ev. cbn [app]. split; [unfold RERRNO; lia|]. split; [unfold RERRNO; cbn; lia|].
intros i Hi. cbn [length] in Hi.
destruct i as [|[|[|[|i]]]]; cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ]; try lia.
+ rewrite Z.add_0_r in E0 |- *. rewrite <- (Z.add_0_r RERRNO). exact E0.
+ exact E1. + exact E2. + exact E3.
- split; [unfold RERRNO; lia|]. split; [unfold RERRNO; cbn; lia|]. intros i Hi. apply (proj2 (errno_byte m i ltac:(cbn in Hi; lia))).
Qed.
Section SE.
Variables (x : word).
Lemma ref_ro_addr_true : ro_addr rsegs x = true -> IMG_LO <= bv_unsigned x < 0xaf000.
Proof.
intros H.
unfold ro_addr in H. unfold IMG_LO.
pose proof (bv_unsigned_in_range 64 x) as R.
set (z := bv_unsigned x) in *.
unfold rsegs, Plain.Plain_loaded_segments in H. cbn [find_segment] in H.
replace (Z.of_N (seg_base Plain_segment_000)) with 65536%Z in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Plain_segment_000)) with 143360%Z in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Plain_segment_001)) with 208896%Z in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Plain_segment_001)) with 507904%Z in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Plain_segment_002)) with 716800%Z in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Plain_segment_002)) with 24576%Z in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Plain_segment_003)) with 741376%Z in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Plain_segment_003)) with 212992%Z in H by (vm_compute; reflexivity).
destruct (Z.leb_spec0 65536 z); destruct (Z.leb_spec0 (z + 1) (65536 + 143360)); cbn [andb] in H; try lia.
all: destruct (Z.leb_spec0 208896 z); destruct (Z.leb_spec0 (z + 1) (208896 + 507904)); cbn [andb] in H; try lia.
all: destruct (Z.leb_spec0 716800 z); destruct (Z.leb_spec0 (z + 1) (716800 + 24576)); cbn [andb] in H; try lia.
all: try (replace (seg_writable Plain_segment_002) with true in H by (vm_compute; reflexivity); discriminate).
all: destruct (Z.leb_spec0 741376 z); destruct (Z.leb_spec0 (z + 1) (741376 + 212992)); cbn [andb] in H; try lia.
all: try (replace (seg_writable Plain_segment_003) with true in H by (vm_compute; reflexivity); discriminate).
all: try discriminate.
Qed.
End SE.
Lemma outside_iff : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "M'7&QN%211'F&B&R0r2r1%3221&S?r3%23:41&C'?&SD&6%13==:%3217&SE&=%13AA>%32;1%9251%;11p0=1pXDH1%F2B1pZDH1pWDJ1").
Proof.
induction W as [|[lo hi] W IH]; intros z; cbn [outside].
- split; [intros _ iv []| intros; exact I].
- rewrite IH. split.
+ intros [H1 H2] iv [<-|Hin]; [exact H1| apply H2; exact Hin].
+ intros H. split; [apply (H (lo, hi)); left; reflexivity| intros iv Hin; apply H; right; exact Hin].
Qed.
Definition client_img_ivs : list ivl := [(0xaf000, 0xb4ec8); (0xb4ed0, 0xe7ed0); (0xe7ed8, 0xe7ef0); (0xe8418, RVMLOCKC); (RVMLOCKC + 4, 0xe9000)].
Definition frameW (LBb : list block) : list ivl :=
(alloc_ceiling, sptop) :: client_img_ivs ++ map (fun b => (blk_addr b, blk_addr b + blk_size b)) LBb.
Section SE.
Local Abbreviation SEC_T_outside_frameW_private := (ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "M'7&Q8%211'F&SD&R6vQ3%211vTF%5221&R0&QEr3%211r2%5221&RJ&QF&E'<%12AA&QGr4%54F321%8371<p0:1p0A1pZDH1pQDJ1")) (only parsing).
Variable LBb : ltac:(sec_ty2 constr:(SEC_T_outside_frameW_private) 0%nat 0%nat).
Variable z : ltac:(sec_ty2 constr:(SEC_T_outside_frameW_private) 1%nat 0%nat).
Lemma outside_frameW_private : ltac:(sec_stmt2 constr:(SEC_T_outside_frameW_private) 2%nat 0%nat).
Proof.
intros Hsp H0.
pose proof (proj1 (outside_iff _ _) H0) as H. clear H0.
assert (O1 : ~ (alloc_ceiling <= z < sptop)) by (apply (H (alloc_ceiling, sptop)); left; reflexivity).
assert (O2 : ~ (0xaf000 <= z < 0xb4ec8)) by (apply (H (0xaf000, 0xb4ec8)); right; left; reflexivity).
assert (O3 : ~ (0xb4ed0 <= z < 0xe7ed0)) by (apply (H (0xb4ed0, 0xe7ed0)); do 2 right; left; reflexivity).
assert (O4 : ~ (0xe7ed8 <= z < 0xe7ef0)) by (apply (H (0xe7ed8, 0xe7ef0)); do 3 right; left; reflexivity).
assert (O5 : ~ (0xe8418 <= z < RVMLOCKC)) by (apply (H (0xe8418, RVMLOCKC)); do 4 right; left; reflexivity).
assert (O6 : ~ (RVMLOCKC + 4 <= z < 0xe9000)) by (apply (H (RVMLOCKC + 4, 0xe9000)); do 5 right; left; reflexivity).
assert (OB : forall b, In b LBb -> ~ (blk_addr b <= z < blk_addr b + blk_size b)).
{ intros b Hb. apply (H (blk_addr b, blk_addr b + blk_size b)). do 6 right. apply in_map_iff. exists b. auto. }
unfold alloc_private. cbn [hl_alloc_ro hl_img_lo hl_img_hi hl_alloc_static hl_sptop L0].
unfold IMG_LO, IMG_HI, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD in *. rewrite HCEIL in *.
destruct (Z_le_gt_dec sptop z) as [Hs|Hs]; [right; lia|].
destruct (Z_le_gt_dec 0x10000 z) as [I1|I1]; [destruct (Z_lt_ge_dec z 0xaf000) as [I2|I2]; [right; lia|]|].
all: destruct (Z_le_gt_dec 0xe7ef0 z) as [J1|J1]; [destruct (Z_lt_ge_dec z 0xe8068) as [J2|J2]; [right; lia|]|].
all: destruct (Z_le_gt_dec 0xe8410 z) as [K1|K1]; [destruct (Z_lt_ge_dec z 0xe8418) as [K2|K2]; [right; lia|]|].
all: destruct (Z_le_gt_dec 0xb4ec8 z) as [G1|G1]; [destruct (Z_lt_ge_dec z 0xb4ed0) as [G2|G2]; [right; lia|]|].
all: destruct (Z_le_gt_dec 0xe7ed0 z) as [U1|U1]; [destruct (Z_lt_ge_dec z 0xe7ed8) as [U2|U2]; [right; lia|]|].
all: destruct (Z_le_gt_dec RVMLOCKC z) as [V1|V1]; [destruct (Z_lt_ge_dec z (RVMLOCKC + 4)) as [V2|V2]; [right; lia|]|].
all: left; split; [lia|]; split; [intros (b & Hb & Hr); apply in_map_iff in Hb as (bb & <- & Hbb); cbn [fst snd blk_iv] in Hr; exact (OB bb Hbb Hr)| lia].
Qed.
End SE.
Lemma frameW_client : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "?'7&Q8%211'D'<'F%2211&R=vQ3r1%3221&QE%113%:3731pQD<1").
Proof.
intros LBb. unfold frameW. constructor; [left; cbn; lia|]. apply Forall_app. split.
- unfold client_img_ivs, rclient_write_ok, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP.
repeat (apply Forall_cons; [cbn [fst snd]; right; left; lia|]). apply Forall_nil.
- apply List.Forall_forall. intros iv Hin. apply in_map_iff in Hin as (b & <- & Hb). right; right. exists b. cbn [fst snd]. split; [exact Hb| lia].
Qed.
End INST2.
Lemma HI0_frame : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "4&RN&QF&QD%3221").
Proof.
intros LB cr M M' VM (RUNp & s & L & LBb & nc & HCEIL & ELB & HR & CR & PL & HK & MI & AUX & REPL & BLK & REST) Hpriv Hmono.
pose proof AUX as (av & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & rnd & CELL & BY1 & BY2 & Bc & Bav & Hav & Brnd & Hrnd & X3 & X4 & X5 & XHW & X6 & X11 & X12 & X23 & Xr).
assert (WM : wmono rsegs M M') by (apply wmono_of_grows; exact Hmono).
assert (AG : forall a, 0 <= a < 2^64 -> alloc_private L0 LB a -> M' (wa a) = M (wa a)).
{ intros a Ha Hp. unfold wa. apply Hpriv; assumption. }
assert (MU : munch (frameW LBb) M M').
{ intros x Hout. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
rewrite <- (Z_to_bv_bv_unsigned x). apply Hpriv; [lia|]. rewrite ELB. apply outside_frameW_private; [exact HCEIL| exact Bc| exact Hout]. }
exists RUNp, s, L, LBb, nc. splits; try (apply REST).
- exact HCEIL.
- exact ELB.
- eapply RHEAP_frame_proof; [exact HR| exact MU| exact WM| apply frameW_client].
- exact CR.
- exact PL.
- exact HK.
- intros a b Ha. destruct (ro_addr rsegs a) eqn:E; [|reflexivity]. exfalso.
pose proof (ref_ro_addr_true a E) as Hro. pose proof (bv_unsigned_in_range 64 a) as R. unfold bv_modulus in R.
rewrite <- (Z_to_bv_bv_unsigned a) in Ha. rewrite Hpriv in Ha; [| lia| right; cbn; left; exact Hro].
rewrite Z_to_bv_bv_unsigned in Ha. pose proof (MI a b Ha). congruence.
- exists av, x3, x4, x5, hw, x6, x11, x12, x23, rnd. splits; try assumption; try lia.
+ eapply rw_cells_agree; [exact CELL| | exact WM]. intros a Ha. cbn in Ha. apply AG; [unfold RAUXV_CELL in Ha; lia|].
right. cbn. unfold RAUXV_CELL, RLIBC, RMLOCK in *. lia.
+ eapply bytes_at_agree; [exact BY1|]. intros a Ha. pose proof (bytes_at_bound _ _ _ _ BY1). apply AG; [lia|]. right. cbn. lia.
+ eapply bytes_at_agree; [exact BY2|]. intros a Ha. pose proof (bytes_at_bound _ _ _ _ BY2). apply AG; [lia|]. right. cbn. lia.
- intros a Ha. pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra.
rewrite <- (Z_to_bv_bv_unsigned a). rewrite Hpriv; [| lia| right; cbn; unfold RCTX in *; lia].
rewrite Z_to_bv_bv_unsigned. apply REPL. exact Ha.
- apply List.Forall_forall. intros b Hb. pose proof (proj1 (List.Forall_forall _ _) BLK b Hb) as [Sz Def].
split; [exact Sz|]. intros i Hi. apply Hmono. apply Def. exact Hi.
Qed.
Section INST3.
Context {RUNp : RunP}.
Hypothesis HCEIL : alloc_ceiling = sptop - 2 ^ 23.
Lemma RHEAP_slots_nodup : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "E'RG'7&Q8%211&Q:&R<vQ3r3r2r1%544321'S@&RE&E&Q7%24=318%5241p071pXN>1pQB@1pY:D1").
Proof.
intros s LB m (st & LB0 & HP & _ & _ & [_ AR]). eapply NoDup_map_perm; [exact HP|].
exact (mf_nodup _ _ (areach_facts_proof _ _ AR)).
Qed.
Lemma map_blk_iv_lbrm : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "Q>'7&Q8%211'F&S?r1r4%33621'@'3&RD&Q7r2%211%318%5221&SC&Q5%116r3%4221%=3<61p0?1pX:F1'<%12FF%J11&E&QG&Q4%12H;%44N631&SA&8&6%13Q0Q0N%D21A%411qX8=1%<4Q6>;Q1%83?21%Q13?:1p0C1p2Q81pX<Q;1pQDQ;1").
Proof.
induction LBb as [|b l IH]; intros blk A HE; [reflexivity|].
unfold lbrm. rewrite filter_cons. fold (lbrm l blk). cbn [map List.filter fst blk_iv].
rewrite <- (HE b (or_introl eq_refl)).
destruct (decide _) as [Y|N].
- destruct (aptr_eqb (blk_slot b) (blk_slot blk)); [destruct Y|]. cbn [negb map]. f_equal. apply IH. intros b' Hb'. apply HE. right. exact Hb'.
- destruct (aptr_eqb (blk_slot b) (blk_slot blk)); [| exfalso; apply N; exact I]. cbn [negb]. apply IH. intros b' Hb'. apply HE. right. exact Hb'.
Qed.
Lemma lb_remove_corr : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "Q?'7&Q8%211&RH'F'S@&RE&E&Q7r4%349421%6251&Q5r5%74=:21%:2;1&S?'<%12?>%221?(;%14BA8<r3%345C21r6%93621'@%:2GG%L11&S6&QGr7%I4O521%42D1&Q4%?4Q0O;F%@4BQ01K%3261%O4Q5;81%=3;61p0?1p0J1p0O1pY2Q71p2Q81pY4Q:1pQDQ<1").
Proof.
intros LBb p A n NDs NDa Hin.
rewrite (lb_remove_filter A n (map blk_iv LBb)); [| rewrite map_fst_blk_iv; exact NDa| apply in_map_iff; exists (p, A, n); split; [reflexivity| exact Hin]].
symmetry. apply map_blk_iv_lbrm. intros b' Hb'. change (blk_slot (p, A, n)) with (fst p).
destruct (aptr_eqb_spec (blk_slot b') (fst p)) as [E|NE]; destruct (Z.eqb_spec (blk_addr b') A) as [E'|NE']; try reflexivity; exfalso.
- apply NE'. pose proof (nodup_map_inj blk_slot LBb b' (p, A, n) NDs Hb' Hin E) as ->. reflexivity.
- apply NE. pose proof (nodup_map_inj blk_addr LBb b' (p, A, n) NDa Hb' Hin E') as ->. reflexivity.
Qed.
Lemma ret_pc_jalr : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "<'TKyR0%211'@&R2r1%211&S<z%2241%73841pY891").
Proof.
intros ra. apply bv_eq. unfold ret_pc, jalr_tgt, jalr_tgtZ.
rewrite bv_and_unsigned, bv_not_unsigned, !Z_to_bv_unsigned.
change (bv_wrap 64 1) with 1%Z. change (Z.lnot 1) with (-2)%Z. rewrite Z.add_0_r.
rewrite <- (bv_wrap_small 64 (bv_unsigned ra)) at 1 by apply bv_unsigned_in_range. apply Z_land_m2_wrap.
Qed.
Lemma ret_pc_ok : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "='TKyR0%211&S:r1%211'@&R2r2%211%43812p061pY8:1").
Proof. intros ra H. rewrite ret_pc_jalr. exact H. Qed.
Lemma regs_preserved_canon : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "S2&Ny5'TKyR0%211%5241&Q;&QO&S;rA&TJ+1%22;1%5241+2%52>1%8271+3%82A1%;2:1+4%;2D1%>2=1r?r>r=+8%A2J1%D2C1+9%D2M1%G2F1r<r;r:r9r8r7r6r5+B%O2Q81%Q22Q11+C%Q22Q;1%Q52Q41+D%Q52Q>1%Q82Q71+E%Q82QA1%Q;2Q:1+F%Q;2QD1%Q>2Q=1+G%Q>2QG1%QA2Q@1+H%QA2QJ1%QD2QC1+I%QD2QM1%QG2QF1+J%QG2R01%QJ2QI1+K%QJ2R31%QM2QL1r4r3r2r1%R3OQMQJQGQDQCQBQAQ>Q;Q:Q9Q8Q7Q6Q5Q4Q3Q0MJGDA>;854321r@%R6221&S8rB%221R6p041pZ<R=1pZ:R>1pZ8R?1pZ6R@1pX6RA1pX4RB1pX2RC1pX0RD1pWNRE1pWLRF1pWJRG1pWHRH1pZ4RI1pZ2RJ1pZ0RK1pR6RK1pR4RL1").
Proof.
intros R R' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HE r Hr.
rewrite <- (getr_eqv _ _ r HE).
unfold callee_saved_idx in Hr.
assert (Er : exists k, In k callee_saved_idx /\ r = Z_to_bv 5 k).
{ exists (bv_unsigned r). split; [exact Hr| symmetry; apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range]. }
destruct Er as (k & Hk & ->). unfold callee_saved_idx in Hk. cbn [In] in Hk.
repeat (destruct Hk as [<-|Hk]; [unfold getr; cbn; reflexivity|]). destruct Hk.
Qed.
Lemma heap_pres_core_of_cj : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "QA'7&Q8%211'F&Q:&R?r4r3r2r1%544321&R>vQ3&SG&R9%2291%544198&R@%12<;&R1&R8r6%9218%443A12&SD&R6%11>r7%?21>%5231&S1&QF&E'<%12OO&QGr9%54Q4321r8%95821<Bp0;1p0B1p0H1p0K1p0Q21pY0Q91pXNQ:1pY<Q<1pQFQ>1").
Proof.
intros LBb' sp m m' HP HD HI ST LO. pose_ceil. unfold RALIGNED_STACK, RMALLOC_STACK in *. rewrite HCEIL in LO.
split; cbn [hl_stack hl_img_lo hl_img_hi hl_alloc_static hl_errno hl_sptop L0]; unfold RALIGNED_STACK, RMALLOC_STACK.
- intros a Ha CA NE. change (Z_to_bv 64 a) with (wa a).
destruct CA as [(b & Hb & Hr)|[[Hhi Hns]|[Himg Hnst]]].
+ apply in_map_iff in Hb as (bb & <- & Hbb). cbn [fst snd blk_iv] in Hr.
apply (proj1 (HP a Ha ltac:(right; right; exists bb; split; [exact Hbb| exact Hr]))).
+ cbn [hl_sptop L0] in Hhi. destruct (Z_le_gt_dec sp a) as [Hs|Hs].
* apply (proj1 (HP a Ha ltac:(left; exact Hs))).
* apply HD. rewrite HCEIL. lia.
+ unfold in_errno in NE. cbn [hl_errno L0] in NE. unfold IMG_LO, IMG_HI, RMLOCK, RCTX, RERRNO in *.
apply HI; [exact Himg| intros X; apply Hnst; cbn [hl_alloc_static L0]; unfold RMLOCK, RCTX in *; lia| unfold RERRNO; exact NE].
- intros a Ha. destruct ST as (_ & Hsp & S). destruct (S a ltac:(lia)) as [W _].
rewrite ref_wview_overlay in W by (unfold wa; rewrite u64_lit; lia). exact W.
Qed.
Lemma map_blk_slot_lbrm : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "Q1'7&Q8%211'@&RE%511&E&Q7&Q4r2r1%3221%64;851&TG&RC&TN%11<&S>&8&RD%=1;%22;1%411%611qX>:1&TM%114qZ@=1%F4KHEC%@6?H=521%K3IB1pX<N1pQDN1").
Proof.
induction LBb as [|b l IH]; intros blk; [reflexivity|].
unfold lbrm. cbn [map]. rewrite !filter_cons. fold (lbrm l blk).
destruct (decide _) as [Y|N]; [cbn [map]; f_equal; apply IH| apply IH].
Qed.
Lemma filter_keep_all : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "M&RC'7%112&C&S?r2r1%33721%511'@&TG&TN%11<&S>&8&RDr4%22;1%411%611qZBD1&TM%114qZ@G1%>6HF<41C%@3G1Dp0B1pXHI1pX>L1").
Proof.
intros c l. induction l as [|z l IH]; intros Hni; [reflexivity|]. rewrite filter_cons.
destruct (aptr_eqb_spec z c) as [->|NE]; [exfalso; apply Hni; left; reflexivity|].
destruct (decide _) as [Y|N]; [| exfalso; apply N; exact I].
f_equal. apply IH. intros H; apply Hni; right; exact H.
Qed.
Lemma ap_remove_filter : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "Q2&RC'7%112'S@r1%2251&S?r3r2%33921'@&RAr4%2216&TG&TN%11@&S>&8&RDr5%22A1%411%611qZBH1&TM%114qZ@K1%>6LJ<41E%C3K@1p0E1p0J1pXHN1pX>Q11").
Proof.
intros c l. induction l as [|y l IH]; intros ND Hin; [destruct Hin|]. cbn [ap_remove]. rewrite filter_cons.
inversion ND as [|? ? Hni ND']; subst.
destruct (aptr_eqb_spec y c) as [->|NE].
- destruct (decide _) as [Y|N]; [destruct Y|]. symmetry. apply filter_keep_all. exact Hni.
- destruct (decide _) as [Y|N]; [| exfalso; apply N; exact I].
f_equal. apply IH; [exact ND'|]. destruct Hin as [->|Hin]; [congruence| exact Hin].
Qed.
Lemma bv5_lit : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "J'F'?&SDzr1%3221&SE+Q0%2241%8241&TIy5r2%3221'@'TK%115&TJr3%2281(TH%13:3A%83631pQ@:1p0?1pXFI1").
Proof. intros k Hk H. apply bv_eq. rewrite Z_to_bv_unsigned. cbn [bv_unsigned]. unfold bv_wrap, bv_modulus. rewrite Z.mod_small; [reflexivity|]. cbn. lia. Qed.
Lemma implM_mupd_only_inv : forall {St} (f : St -> St) (s : St) (Q : unit -> St -> machine_state -> Prop) ms,
implM rsegs (mupd f) s Q ms -> evt rsegs (Q tt (f s)) ms.
Proof. intros St f s Q ms H. exact H. Qed.
End INST3.
Section DELIVERABLES.
Variable SCFG : SpuriousCfg.
Hypothesis HALLOC : sc_alloc SCFG = false.
Hypothesis MBND : forall R : RunP, @model_bounds R.
Lemma HI0_free : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "5&RL&QFvS=&QD%43321").
Proof.
intros fx R M model LB cr A n K HH Hh Hl Hm HinLB R10 R4 RET SOK HK0 CONT.
cbn [hi_heap HI0 hl_tp hl_free hl_segs L0] in *.
rewrite <- (bv5_lit 10 ltac:(lia)) in R10. rewrite <- (bv5_lit 4 ltac:(lia)) in R4. rewrite <- (bv5_lit 1 ltac:(lia)) in RET, CONT.
rewrite <- (bv5_lit 2 ltac:(lia)) in SOK, CONT.
destruct HH as (RUNp & s & L & LBb & nc & HCEIL & ELB & HR & CR & PL & HKL & MI & AUX & REPL & BLK & Hnc & Hk & Hfst & Hsnd & POT & LEN & FA & LIVE & LIM).
pose proof (hi0_nodup_addr s LBb M HR BLK) as NDa. pose proof (RHEAP_slots_nodup s LBb M HR) as NDs.
rewrite ELB in HinLB. apply in_map_iff in HinLB as (bb & Ebb & Hbb).
destruct bb as [[p A'] n']. unfold blk_iv, blk_addr, blk_size in Ebb. cbn [fst snd] in Ebb. injection Ebb as -> ->.
destruct (stack_ok_stk HCEIL M _ SOK) as (STK & LO & SPT & SPR). set (sp := bv_unsigned (getr R (Z_to_bv 5 2))) in *.
destruct (errno_cell_any M) as [errv ERR].
assert (ERR' : rw_cells rsegs M (bv_unsigned (getr R (Z_to_bv 5 4)) + -164) [C4 errv]).
{ rewrite R4. replace (bv_unsigned (Z_to_bv 64 RATP) + -164) with RERRNO by (vm_compute; reflexivity). exact ERR. }
pose proof (rfree_spec_proof (getr R (Z_to_bv 5 1)) (getr R (Z_to_bv 5 2)) (getr R (Z_to_bv 5 3)) (getr R (Z_to_bv 5 4))
(getr R (Z_to_bv 5 5)) (getr R (Z_to_bv 5 6)) (getr R (Z_to_bv 5 7)) (getr R (Z_to_bv 5 8)) (getr R (Z_to_bv 5 9))
(getr R (Z_to_bv 5 10)) (getr R (Z_to_bv 5 11)) (getr R (Z_to_bv 5 12)) (getr R (Z_to_bv 5 13)) (getr R (Z_to_bv 5 14))
(getr R (Z_to_bv 5 15)) (getr R (Z_to_bv 5 16)) (getr R (Z_to_bv 5 17)) (getr R (Z_to_bv 5 18)) (getr R (Z_to_bv 5 19))
(getr R (Z_to_bv 5 20)) (getr R (Z_to_bv 5 21)) (getr R (Z_to_bv 5 22)) (getr R (Z_to_bv 5 23)) (getr R (Z_to_bv 5 24))
(getr R (Z_to_bv 5 25)) (getr R (Z_to_bv 5 26)) (getr R (Z_to_bv 5 27)) (getr R (Z_to_bv 5 28)) (getr R (Z_to_bv 5 29))
(getr R (Z_to_bv 5 30)) (getr R (Z_to_bv 5 31))
fp_regs fp_csr M s LBb p A n (sp - RALIGNED_STACK) sptop errv
HR Hbb AUX SPT STK LO ltac:(unfold RFREE_STACK, RALIGNED_STACK, RMALLOC_STACK; lia)
ERR' MI R4 R10) as IMPL.
change (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with (canon_regs R) in IMPL.
apply (implM_eqv_transfer rsegs _ _ _ _ (mkst R (Z_to_bv 64 RFREE_SYM) M (seg_rom rsegs))) in IMPL; [| apply mkst_eqv_canon].
unfold raw_free in IMPL. apply implM_mget_inv, implM_bind_inv in IMPL.
assert (LIVEp : In (fst p) (ld_live L)).
{ eapply Permutation_in; [apply Permutation_sym; exact PL|]. apply in_map_iff. exists (p, A, n). split; [reflexivity| exact Hbb]. }
eapply (embed_free rsegs SCFG RESV IMG_HI _ _ _ _ _ _ s _ _ model model (m_vmmaps model) K
(cfree_contract_proof _ _ _ CR LIVEp) (mb_free (MBND RUNp) _ _ _ CR LIVEp) IMPL HKL).
- symmetry. apply with_vmmaps_eta.
- exact Hh. - exact Hl. - exact Hm.
- apply vm_shrunk_refl.
-
intros cs' s' ms' mo' L' HQ HCP _ HPOT HK' Emo' HS E1 E2 E3.
cbv beta in HQ. apply implM_mupd_only_inv in HQ. destruct HQ as (ms2 & Hms2 & (ms1 & POST & EQV)).
destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Ems1 &
MI' & STK' & ERR2 & AUX' & HPRES & HDEEP & HIMG & _ & _ & HR').
subst ms1. destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems2 REQ].
assert (Hh' : m_halted mo' = None) by (rewrite Emo', with_vmmaps_halted; exact Hh).
assert (Hl' : m_vm_lazy mo' = []) by (rewrite Emo', with_vmmaps_lazy'; exact Hl).
eapply srz_msteps; [exact Hh'| exact Hl'| apply cj_msteps_cat; exact Hms2|].
rewrite Ems2, (ret_pc_ok _ RET). change (MS ?R' fp_regs ?pc fp_csr None ?mm ?ro) with (mkst R' pc mm ro).
pose proof (lb_remove_corr LBb p A n NDs NDa Hbb) as ELB'. rewrite <- ELB in ELB'.
rewrite (lb_remove_lbrm LBb p A n NDs Hbb) in HPRES, HR'.
assert (SUB : forall b, In b (lbrm LBb (p, A, n)) -> In b LBb).
{ intros b Hb. unfold lbrm in Hb. apply list_elem_of_In, list_elem_of_filter in Hb. apply list_elem_of_In. tauto. }
apply CONT.
+ eapply regs_preserved_canon. exact REQ.
+ split.
* rewrite ELB'. apply heap_pres_core_of_cj; assumption.
* cbn [hl_segs hl_errno L0]. change (Z_to_bv 64 RERRNO) with (wa (RERRNO + Z.of_nat 0)).
pose proof ERR as [[_ B1] _]. pose proof ERR2 as [[_ B2] _].
rewrite R4 in B2. replace (bv_unsigned (Z_to_bv 64 RATP) + -164) with RERRNO in B2 by (vm_compute; reflexivity).
rewrite (bytes_at_rdn rsegs m' RERRNO _ 0 4 B2) by (cbn; lia). rewrite (bytes_at_rdn rsegs M RERRNO _ 0 4 B1) by (cbn; lia). reflexivity.
+ exact Emo'.
+ rewrite ELB'. exists RUNp, (set_m cs' s'), (set_live (ap_remove (fst p) (ld_live L')) L'), (lbrm LBb (p, A, n)), nc.
destruct HS as (S1 & S2 & S3 & S4 & S5 & S6).
splits; try assumption.
* reflexivity.
* cbn [ps_m set_m]. eapply creach_free; [exact CR| exact LIVEp| exact HCP].
* cbn [ld_live set_live]. assert (EL : ld_live L' = ld_live L) by (eapply cpath_live; exact HCP). rewrite EL, map_blk_slot_lbrm. change (blk_slot (p, A, n)) with (fst p).
rewrite ap_remove_filter; [| eapply Permutation.Permutation_NoDup; [apply Permutation_sym; exact PL| exact NDs]| exact LIVEp].
apply filter_Permutation. exact PL.
* cbn [ps_brk set_m]. apply KL2_set_live. exact HK'.
* intros a Ha. pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra.
rewrite <- (Z_to_bv_bv_unsigned a). change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)).
rewrite HIMG; [| unfold RCTX in *; lia| unfold RCTX in *; lia| unfold RCTX, RERRNO in *; lia].
unfold wa. rewrite Z_to_bv_bv_unsigned. apply REPL. exact Ha.
* apply List.Forall_forall. intros b Hb. pose proof (SUB b Hb) as HbL.
pose proof (proj1 (List.Forall_forall _ _) BLK b HbL) as [Sz Def]. split; [exact Sz|].
intros i Hi. pose proof (RHEAP_block_range_proof s LBb M b HR HbL) as (Q1 & _ & _ & Q4 & _). pose proof alloc_ceiling_lt.
rewrite (proj1 (HPRES (blk_addr b + i) ltac:(lia) ltac:(right; right; exists b; split; [exact Hb| lia]))). apply Def. exact Hi.
* cbn [ps_m set_m]. lia.
* rewrite S1, length_app. rewrite length_app in LEN. lia.
* rewrite S1. apply Forall_app in FA as [FA1 FA2]. apply Forall_app. split; [exact FA1| apply S4; exact FA2].
* lia.
* rewrite S5. exact LIM.
Qed.
Lemma size_overflows_small : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "A'F&SDr1&SF+2+K%3221%6251'@'3&RFr2%211(5%63521p081pY2@1").
Proof. intros n Hn. unfold size_overflows. apply Z.leb_gt. lia. Qed.
Lemma elen_ok_NMAX : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "Q?'F'?&SEzr6%3221&SD&SF+2+K%3221%5271%;271&SB&QI&Q<%3221%;2=1&Q>r8r7(RBr5r4r3%44E321%83761'@'3&Q?%117(5%53421&QM%11>&Q@%N221p051p0<1p0F1p0L1pX@Q91pY6Q:1pXJQ;1pWFQ<1pR2Q=1pY2Q>1").
Proof.
intros n PA a len prot flags Hn HPA HE Hf. cbn [elen_ok] in HE.
assert (ML : forall l, mmap_len l <= l + 4095).
{ intros l. unfold mmap_len, page_round_up_Z, page_size. pose proof (Z.mul_div_le (l + (4096 - 1)) 4096 ltac:(lia)). lia. }
replace NMAX with 134283264 by reflexivity. replace (2^27) with 134217728 in Hn by reflexivity.
unfold POTMAX, POT0, AMC, NCMAX, NSLOTS in HPA.
destruct HE as [HE|[[_ HE]|[_ HE]]]; [congruence| |].
- pose proof (ML len). unfold NSLOTS, PGSZ in HE. lia.
- pose proof (ML (n + IB + UNIT)) as H2. unfold mmap_len in H2. rewrite <- round_up_pg_eq in H2.
unfold GMAX, IB, UNIT in *. replace (2^20) with 1048576 in HE by reflexivity. lia.
Qed.
Lemma HI0_malloc : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "5&S7&QFvS=&QD%43321").
Proof.
intros fx R M model LB cr n K HH Hh Hl Hm R10 Hn HCR R4 RET SOK HK0 CONT.
cbn [hi_heap HI0 hl_tp hl_malloc hl_segs L0] in *.
rewrite <- (bv5_lit 10 ltac:(lia)) in R10, CONT. rewrite <- (bv5_lit 4 ltac:(lia)) in R4. rewrite <- (bv5_lit 1 ltac:(lia)) in RET, CONT.
rewrite <- (bv5_lit 2 ltac:(lia)) in SOK, CONT.
destruct HCR as [CRK CRB]. cbn [hl_k_per_malloc hl_b_overhead L0 fst snd] in CRK, CRB.
destruct HH as (RUNp & s & L & LBb & nc & HCEIL & ELB & HR & CR & PL & HKL & MI & AUX & REPL & BLK & Hnc & Hk & Hfst & Hsnd & POT & LEN & FA & LIVE & LIM).
pose proof (hi0_nodup_addr s LBb M HR BLK) as NDa. pose proof (RHEAP_slots_nodup s LBb M HR) as NDs.
destruct (stack_ok_stk HCEIL M _ SOK) as (STK & LO & SPT & SPR). set (sp := bv_unsigned (getr R (Z_to_bv 5 2))) in *.
destruct (errno_cell_any M) as [errv ERR].
assert (ERR' : rw_cells rsegs M (bv_unsigned (getr R (Z_to_bv 5 4)) + -164) [C4 errv]).
{ rewrite R4. replace (bv_unsigned (Z_to_bv 64 RATP) + -164) with RERRNO by (vm_compute; reflexivity). exact ERR. }
pose proof (rmalloc_spec (getr R (Z_to_bv 5 1)) (getr R (Z_to_bv 5 2)) (getr R (Z_to_bv 5 3)) (getr R (Z_to_bv 5 4))
(getr R (Z_to_bv 5 5)) (getr R (Z_to_bv 5 6)) (getr R (Z_to_bv 5 7)) (getr R (Z_to_bv 5 8)) (getr R (Z_to_bv 5 9))
(getr R (Z_to_bv 5 10)) (getr R (Z_to_bv 5 11)) (getr R (Z_to_bv 5 12)) (getr R (Z_to_bv 5 13)) (getr R (Z_to_bv 5 14))
(getr R (Z_to_bv 5 15)) (getr R (Z_to_bv 5 16)) (getr R (Z_to_bv 5 17)) (getr R (Z_to_bv 5 18)) (getr R (Z_to_bv 5 19))
(getr R (Z_to_bv 5 20)) (getr R (Z_to_bv 5 21)) (getr R (Z_to_bv 5 22)) (getr R (Z_to_bv 5 23)) (getr R (Z_to_bv 5 24))
(getr R (Z_to_bv 5 25)) (getr R (Z_to_bv 5 26)) (getr R (Z_to_bv 5 27)) (getr R (Z_to_bv 5 28)) (getr R (Z_to_bv 5 29))
(getr R (Z_to_bv 5 30)) (getr R (Z_to_bv 5 31))
fp_regs fp_csr M s LBb n (sp - RALIGNED_STACK) sptop errv
HR AUX SPT STK LO ltac:(unfold RALIGNED_STACK, RMALLOC_STACK; lia) ERR' MI R4 R10 ltac:(lia)) as IMPL.
change (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with (canon_regs R) in IMPL.
apply (implM_eqv_transfer rsegs _ _ _ _ (mkst R (Z_to_bv 64 RMALLOC_SYM) M (seg_rom rsegs))) in IMPL; [| apply mkst_eqv_canon].
unfold raw_malloc in IMPL. apply implM_mget_inv, implM_bind_inv in IMPL.
set (cs := ps_m s) in *. set (PA := pot cs + AMC).
assert (HPA : PA <= POTMAX + AMC).
{ subst PA. unfold POTMAX, POT0, AMC, NCMAX, NSLOTS in *. unfold K0, KPM, NCMAX in Hk. unfold KPM in CRK. change (Z.of_nat EVM) with 8 in Hk, CRK. lia. }
pose proof (CALLB_le n PA ltac:(lia) HPA) as [CB0 CB1].
set (CAPK := K0 + NSEG - fst cr + KPM). set (CAPB := B0 - snd cr + (n + BOV)).
assert (HCAPK : CAPK <= CAPKMAX) by (subst CAPK; unfold K0, NSEG, KPM, NCMAX, CAPKMAX; change (Z.of_nat EVM) with 8; lia).
assert (HCAPB : CAPB <= CAPBMAX) by (subst CAPB; unfold CAPBMAX, B0 in *; lia).
eapply (embed rsegs SCFG HALLOC RESV IMG_HI CAPK CAPB HCAPK HCAPB (cmalloc cs n) L _ (elen_ok n PA) EVM (CALLB n PA) _ s _ _ model model K
(cmalloc_contract_proof cs L n CR ltac:(lia))
(mb_malloc (MBND RUNp) cs L n CR ltac:(lia) (size_overflows_small n ltac:(lia)))
(fun a len prot flags HE Hf => elen_ok_NMAX n PA a len prot flags Hn HPA HE Hf)
IMPL HKL).
- symmetry. apply with_vmmaps_eta.
- exact Hh. - exact Hl. - exact Hm.
-
unfold RI. splits.
+ subst CAPK. unfold KPM. change (Z.of_nat EVM) with 8 in *. lia.
+ exact FA.
+ subst CAPB. lia.
+ exact CB0.
+ unfold CAPBMAX. exact LIM.
+ exact (KL2_init_sp_window _ _ _ _ _ HKL).
-
intros [cs' rc] s' ms' mo' L' HQ HCP HPOST [HSOME HPOT] HK' Emo' HRI' E1 E2 E3. cbn [fst snd] in HSOME, HPOT, HPOST.
destruct rc as [c|]; [| exfalso; apply HSOME; reflexivity]. clear HSOME.
cbv beta iota in HQ. apply implM_mupd_inv, implM_ret_inv in HQ. destruct HQ as (ms2 & Hms2 & (ms1 & POST & EQV)).
destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & Ems1 &
MI' & STK' & ERR2 & AUX' & HPRES & HDEEP & HIMG & _ & _ & (A & junk & EA0 & RBR & HR' & UCH & _)).
subst ms1. destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems2 REQ].
assert (Hh' : m_halted mo' = None) by (rewrite Emo', with_vmmaps_halted; exact Hh).
assert (Hl' : m_vm_lazy mo' = []) by (rewrite Emo', with_vmmaps_lazy'; exact Hl).
eapply srz_msteps; [exact Hh'| exact Hl'| apply cj_msteps_cat; exact Hms2|].
rewrite Ems2, (ret_pc_ok _ RET). change (MS ?R' fp_regs ?pc fp_csr None ?mm ?ro) with (mkst R' pc mm ro).
set (pb := (c, fresh_off cs' c n)) in *.
set (LBb' := (pb, A, n) :: LBb) in *.
assert (CR' : creach cs' (set_live (c :: ld_live L') L')).
{ exact (creach_malloc cs L n L' cs' (Some c) CR ltac:(lia) HCP). }
assert (HK'' : KL2 RESV IMG_HI (set_live (c :: ld_live L') L') (ps_brk (set_m cs' s')) (m_vmmaps mo')).
{ cbn [ps_brk set_m]. apply KL2_set_live. exact HK'. }
assert (HA4 : 4096 <= A).
{ change A with (blk_addr (pb, A, n)). apply (block_ge_4096 (set_m cs' s') LBb' m' (pb, A, n) HR'). left. reflexivity. }
pose proof RBR as (B1 & B2 & B3 & B4 & B5). pose proof alloc_ceiling_lt as ACL.
assert (DEF : forall i, 0 <= i < n -> m' (wa (A + i)) <> None).
{ intros i Hi. destruct UCH as [[WF BA] _]. cbn [cells_wf cell_wf] in WF. destruct WF as [Hlen _].
destruct BA as (_ & _ & BA). cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
specialize (BA (Z.to_nat i) ltac:(rewrite Hlen; lia)). rewrite Z2Nat.id in BA by lia.
rewrite ref_mrd_overlay in BA by (unfold wa; rewrite u64_lit by lia; clear - B5 Hi; lia).
rewrite BA. destruct (nth_error _ _) eqn:En; [discriminate|]. exfalso. apply nth_error_None in En. cbn in En. lia. }
apply (CONT (ms_regs ms2) m' mo' A).
+ rewrite <- (getr_eqv _ _ _ REQ). unfold getr. cbn. exact EA0.
+ eapply regs_preserved_canon. exact REQ.
+ unfold HeapIface.block_range. cbn [hl_img_lo hl_img_hi hl_sptop L0]. unfold IMG_LO, IMG_HI. splits; [exact HA4| exact B5| exact B2| lia| rewrite HCEIL in B4; lia].
+ intros b Hb. rewrite ELB in Hb. apply in_map_iff in Hb as (bb & <- & Hbb). cbn [fst snd blk_iv].
assert (Hid : blk_id (pb, A, n) <> blk_id bb).
{ pose proof (RHEAP_blocks_nodup_proof _ _ _ HR') as ND'. cbn [map] in ND'. inversion ND' as [|? ? Hni _]; subst.
intros E. apply Hni. rewrite E. apply in_map. exact Hbb. }
pose proof (RHEAP_blocks_disjoint_proof _ _ _ (pb, A, n) bb HR' ltac:(left; reflexivity) ltac:(right; exact Hbb) Hid) as D.
cbn [blk_addr blk_size fst snd] in D. lia.
+ intros i Hi. change (Z_to_bv 64 (A + i)) with (wa (A + i)). apply DEF. exact Hi.
+ rewrite ELB. apply heap_pres_core_of_cj; assumption.
+ exact Emo'.
+ exists RUNp, (set_m cs' s'), (set_live (c :: ld_live L') L'), LBb', (nc + 1).
destruct HRI' as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
unfold debit. cbn [fst snd hl_k_per_malloc hl_b_overhead L0].
splits; try assumption.
* rewrite ELB. reflexivity.
* cbn [ld_live set_live]. assert (EL : ld_live L' = ld_live L) by (eapply cpath_live; exact HCP). rewrite EL.
subst LBb' pb. cbn [map blk_slot fst]. apply perm_skip. exact PL.
* intros a Ha. pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra.
rewrite <- (Z_to_bv_bv_unsigned a). change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)).
rewrite HIMG; [| unfold RCTX in *; lia| unfold RCTX in *; lia| unfold RCTX, RERRNO in *; lia].
unfold wa. rewrite Z_to_bv_bv_unsigned. apply REPL. exact Ha.
* subst LBb'. constructor.
-- split; [cbn; lia| cbn [blk_addr blk_size fst snd]; exact DEF].
-- apply List.Forall_forall. intros b Hb. pose proof (proj1 (List.Forall_forall _ _) BLK b Hb) as [Sz Def]. split; [exact Sz|].
intros i Hi. pose proof (RHEAP_block_range_proof s LBb M b HR Hb) as (W1 & _ & _ & W4 & _).
rewrite (proj1 (HPRES (blk_addr b + i) ltac:(lia) ltac:(right; right; exists b; split; [exact Hb| lia]))). apply Def. exact Hi.
* lia.
* unfold KPM in *. change (Z.of_nat EVM) with 8 in *. lia.
* unfold KPM in *. change (Z.of_nat EVM) with 8 in *. lia.
* lia.
* cbn [ps_m set_m]. lia.
* subst CAPK. unfold KPM in *. change (Z.of_nat EVM) with 8 in *. cbn [Z.of_nat] in Q1. lia.
* subst CAPB. lia.
Qed.
Section SE.
Variables (M : word -> option byte).
Lemma repl_cells : (forall a : word, RCTX + 928 <= bv_unsigned a < RCTX + 936 -> M a = None) ->
rw_cells rsegs M (RCTX + 928) [C4 (wz 0); C4 (wz 0)].
Proof.
intros HN.
assert (HN' : forall i, 0 <= i < 8 -> M (wa (RCTX + 928 + i)) = None).
{ intros i Hi. apply HN. unfold wa, RCTX in *. rewrite u64_lit by lia. lia. }
pose proof I as RCTXv. unfold RCTX in HN.
split; [split; [cbn; repeat split; reflexivity|]|].
- split; [unfold RCTX; lia|]. split; [cbn; unfold RCTX; lia|]. intros i Hi. cbn in Hi. unfold mrd. rewrite HN' by lia.
do 8 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
- split; [unfold RCTX; lia|]. split; [cbn; unfold RCTX; lia|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros i Hi. unfold wview. rewrite HN' by lia.
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; discriminate.
Qed.
End SE.
Lemma HI0_aligned : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "5&RI&QFvS=&QD%43321").
Proof.
intros fx R M model LB cr n K HH Hh Hl Hm R10 R11 Hn HCR R4 RET SOK HK0 CONT.
cbn [hi_heap HI0 hl_tp hl_aligned_alloc hl_segs L0] in *.
rewrite <- (bv5_lit 10 ltac:(lia)) in R10, CONT. rewrite <- (bv5_lit 11 ltac:(lia)) in R11. rewrite <- (bv5_lit 4 ltac:(lia)) in R4. rewrite <- (bv5_lit 1 ltac:(lia)) in RET, CONT.
rewrite <- (bv5_lit 2 ltac:(lia)) in SOK, CONT.
destruct HCR as [CRK CRB]. cbn [hl_k_per_malloc hl_b_overhead L0 fst snd] in CRK, CRB.
destruct HH as (RUNp & s & L & LBb & nc & HCEIL & ELB & HR & CR & PL & HKL & MI & AUX & REPL & BLK & Hnc & Hk & Hfst & Hsnd & POT & LEN & FA & LIVE & LIM).
pose proof (hi0_nodup_addr s LBb M HR BLK) as NDa. pose proof (RHEAP_slots_nodup s LBb M HR) as NDs.
destruct (stack_ok_stk HCEIL M _ SOK) as (STK & LO & SPT & SPR). set (sp := bv_unsigned (getr R (Z_to_bv 5 2))) in *.
destruct (errno_cell_any M) as [errv ERR].
assert (ERR' : rw_cells rsegs M (bv_unsigned (getr R (Z_to_bv 5 4)) + -164) [C4 errv]).
{ rewrite R4. replace (bv_unsigned (Z_to_bv 64 RATP) + -164) with RERRNO by (vm_compute; reflexivity). exact ERR. }
pose proof (repl_cells M REPL) as REPL'.
pose proof (raligned_spec (getr R (Z_to_bv 5 1)) (getr R (Z_to_bv 5 2)) (getr R (Z_to_bv 5 3)) (getr R (Z_to_bv 5 4))
(getr R (Z_to_bv 5 5)) (getr R (Z_to_bv 5 6)) (getr R (Z_to_bv 5 7)) (getr R (Z_to_bv 5 8)) (getr R (Z_to_bv 5 9))
(getr R (Z_to_bv 5 10)) (getr R (Z_to_bv 5 11)) (getr R (Z_to_bv 5 12)) (getr R (Z_to_bv 5 13)) (getr R (Z_to_bv 5 14))
(getr R (Z_to_bv 5 15)) (getr R (Z_to_bv 5 16)) (getr R (Z_to_bv 5 17)) (getr R (Z_to_bv 5 18)) (getr R (Z_to_bv 5 19))
(getr R (Z_to_bv 5 20)) (getr R (Z_to_bv 5 21)) (getr R (Z_to_bv 5 22)) (getr R (Z_to_bv 5 23)) (getr R (Z_to_bv 5 24))
(getr R (Z_to_bv 5 25)) (getr R (Z_to_bv 5 26)) (getr R (Z_to_bv 5 27)) (getr R (Z_to_bv 5 28)) (getr R (Z_to_bv 5 29))
(getr R (Z_to_bv 5 30)) (getr R (Z_to_bv 5 31))
fp_regs fp_csr M s LBb n (sp - RALIGNED_STACK) sptop errv
HR AUX SPT STK LO ltac:(lia) ERR' MI R4 REPL' R10 R11 ltac:(lia)) as IMPL.
change (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with (canon_regs R) in IMPL.
apply (implM_eqv_transfer rsegs _ _ _ _ (mkst R (Z_to_bv 64 RAA_SYM) M (seg_rom rsegs))) in IMPL; [| apply mkst_eqv_canon].
unfold raw_malloc in IMPL. apply implM_mget_inv, implM_bind_inv in IMPL.
set (cs := ps_m s) in *. set (PA := pot cs + AMC).
assert (HPA : PA <= POTMAX + AMC).
{ subst PA. unfold POTMAX, POT0, AMC, NCMAX, NSLOTS in *. unfold K0, KPM, NCMAX in Hk. unfold KPM in CRK. change (Z.of_nat EVM) with 8 in Hk, CRK. lia. }
pose proof (CALLB_le n PA ltac:(lia) HPA) as [CB0 CB1].
set (CAPK := K0 + NSEG - fst cr + KPM). set (CAPB := B0 - snd cr + (n + BOV)).
assert (HCAPK : CAPK <= CAPKMAX) by (subst CAPK; unfold K0, NSEG, KPM, NCMAX, CAPKMAX; change (Z.of_nat EVM) with 8; lia).
assert (HCAPB : CAPB <= CAPBMAX) by (subst CAPB; unfold CAPBMAX, B0 in *; lia).
eapply (embed rsegs SCFG HALLOC RESV IMG_HI CAPK CAPB HCAPK HCAPB (cmalloc cs n) L _ (elen_ok n PA) EVM (CALLB n PA) _ s _ _ model model K
(cmalloc_contract_proof cs L n CR ltac:(lia))
(mb_malloc (MBND RUNp) cs L n CR ltac:(lia) (size_overflows_small n ltac:(lia)))
(fun a len prot flags HE Hf => elen_ok_NMAX n PA a len prot flags Hn HPA HE Hf)
IMPL HKL).
- symmetry. apply with_vmmaps_eta.
- exact Hh. - exact Hl. - exact Hm.
-
unfold RI. splits.
+ subst CAPK. unfold KPM. change (Z.of_nat EVM) with 8 in *. lia.
+ exact FA.
+ subst CAPB. lia.
+ exact CB0.
+ unfold CAPBMAX. exact LIM.
+ exact (KL2_init_sp_window _ _ _ _ _ HKL).
-
intros [cs' rc] s' ms' mo' L' HQ HCP HPOST [HSOME HPOT] HK' Emo' HRI' E1 E2 E3. cbn [fst snd] in HSOME, HPOT, HPOST.
destruct rc as [c|]; [| exfalso; apply HSOME; reflexivity]. clear HSOME.
cbv beta iota in HQ. apply implM_mupd_inv, implM_ret_inv in HQ. destruct HQ as (ms2 & Hms2 & (ms1 & [POST _] & EQV)).
destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & Ems1 &
MI' & STK' & ERR2 & AUX' & HPRES & HDEEP & HIMG & _ & _ & (A & junk & EA0 & RBR & HR' & UCH & _)).
subst ms1. destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems2 REQ].
assert (Hh' : m_halted mo' = None) by (rewrite Emo', with_vmmaps_halted; exact Hh).
assert (Hl' : m_vm_lazy mo' = []) by (rewrite Emo', with_vmmaps_lazy'; exact Hl).
eapply srz_msteps; [exact Hh'| exact Hl'| apply cj_msteps_cat; exact Hms2|].
rewrite Ems2, (ret_pc_ok _ RET). change (MS ?R' fp_regs ?pc fp_csr None ?mm ?ro) with (mkst R' pc mm ro).
set (pb := (c, fresh_off cs' c n)) in *.
set (LBb' := (pb, A, n) :: LBb) in *.
assert (CR' : creach cs' (set_live (c :: ld_live L') L')).
{ exact (creach_malloc cs L n L' cs' (Some c) CR ltac:(lia) HCP). }
assert (HK'' : KL2 RESV IMG_HI (set_live (c :: ld_live L') L') (ps_brk (set_m cs' s')) (m_vmmaps mo')).
{ cbn [ps_brk set_m]. apply KL2_set_live. exact HK'. }
assert (HA4 : 4096 <= A).
{ change A with (blk_addr (pb, A, n)). apply (block_ge_4096 (set_m cs' s') LBb' m' (pb, A, n) HR'). left. reflexivity. }
pose proof RBR as (B1 & B2 & B3 & B4 & B5). pose proof alloc_ceiling_lt as ACL.
assert (DEF : forall i, 0 <= i < n -> m' (wa (A + i)) <> None).
{ intros i Hi. destruct UCH as [[WF BA] _]. cbn [cells_wf cell_wf] in WF. destruct WF as [Hlen _].
destruct BA as (_ & _ & BA). cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
specialize (BA (Z.to_nat i) ltac:(rewrite Hlen; lia)). rewrite Z2Nat.id in BA by lia.
rewrite ref_mrd_overlay in BA by (unfold wa; rewrite u64_lit by lia; clear - B5 Hi; lia).
rewrite BA. destruct (nth_error _ _) eqn:En; [discriminate|]. exfalso. apply nth_error_None in En. cbn in En. lia. }
apply (CONT (ms_regs ms2) m' mo' A).
+ rewrite <- (getr_eqv _ _ _ REQ). unfold getr. cbn. exact EA0.
+ eapply regs_preserved_canon. exact REQ.
+ unfold HeapIface.block_range. cbn [hl_img_lo hl_img_hi hl_sptop L0]. unfold IMG_LO, IMG_HI. splits; [exact HA4| exact B5| exact B2| lia| rewrite HCEIL in B4; lia].
+ intros b Hb. rewrite ELB in Hb. apply in_map_iff in Hb as (bb & <- & Hbb). cbn [fst snd blk_iv].
assert (Hid : blk_id (pb, A, n) <> blk_id bb).
{ pose proof (RHEAP_blocks_nodup_proof _ _ _ HR') as ND'. cbn [map] in ND'. inversion ND' as [|? ? Hni _]; subst.
intros E. apply Hni. rewrite E. apply in_map. exact Hbb. }
pose proof (RHEAP_blocks_disjoint_proof _ _ _ (pb, A, n) bb HR' ltac:(left; reflexivity) ltac:(right; exact Hbb) Hid) as D.
cbn [blk_addr blk_size fst snd] in D. lia.
+ intros i Hi. change (Z_to_bv 64 (A + i)) with (wa (A + i)). apply DEF. exact Hi.
+ rewrite ELB. apply heap_pres_core_of_cj; assumption.
+ exact Emo'.
+ exists RUNp, (set_m cs' s'), (set_live (c :: ld_live L') L'), LBb', (nc + 1).
destruct HRI' as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
unfold debit. cbn [fst snd hl_k_per_malloc hl_b_overhead L0].
splits; try assumption.
* rewrite ELB. reflexivity.
* cbn [ld_live set_live]. assert (EL : ld_live L' = ld_live L) by (eapply cpath_live; exact HCP). rewrite EL.
subst LBb' pb. cbn [map blk_slot fst]. apply perm_skip. exact PL.
* intros a Ha. pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra.
rewrite <- (Z_to_bv_bv_unsigned a). change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)).
rewrite HIMG; [| unfold RCTX in *; lia| unfold RCTX in *; lia| unfold RCTX, RERRNO in *; lia].
unfold wa. rewrite Z_to_bv_bv_unsigned. apply REPL. exact Ha.
* subst LBb'. constructor.
-- split; [cbn; lia| cbn [blk_addr blk_size fst snd]; exact DEF].
-- apply List.Forall_forall. intros b Hb. pose proof (proj1 (List.Forall_forall _ _) BLK b Hb) as [Sz Def]. split; [exact Sz|].
intros i Hi. pose proof (RHEAP_block_range_proof s LBb M b HR Hb) as (W1 & _ & _ & W4 & _).
rewrite (proj1 (HPRES (blk_addr b + i) ltac:(lia) ltac:(right; right; exists b; split; [exact Hb| lia]))). apply Def. exact Hi.
* lia.
* unfold KPM in *. change (Z.of_nat EVM) with 8 in *. lia.
* unfold KPM in *. change (Z.of_nat EVM) with 8 in *. lia.
* lia.
* cbn [ps_m set_m]. lia.
* subst CAPK. unfold KPM in *. change (Z.of_nat EVM) with 8 in *. cbn [Z.of_nat] in Q1. lia.
* subst CAPB. lia.
Qed.
Lemma HI0_free_null : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "4&RK&QFvS=%3221").
Proof.
intros fx R M model K Hh Hl R10 RET HK0 CONT. cbn [hl_free hl_segs L0] in *.
rewrite <- (bv5_lit 10 ltac:(lia)) in R10. rewrite <- (bv5_lit 1 ltac:(lia)) in RET, CONT.
pose proof (rfree_null_spec (getr R (Z_to_bv 5 1)) (getr R (Z_to_bv 5 2)) (getr R (Z_to_bv 5 3)) (getr R (Z_to_bv 5 4))
(getr R (Z_to_bv 5 5)) (getr R (Z_to_bv 5 6)) (getr R (Z_to_bv 5 7)) (getr R (Z_to_bv 5 8)) (getr R (Z_to_bv 5 9))
(getr R (Z_to_bv 5 10)) (getr R (Z_to_bv 5 11)) (getr R (Z_to_bv 5 12)) (getr R (Z_to_bv 5 13)) (getr R (Z_to_bv 5 14))
(getr R (Z_to_bv 5 15)) (getr R (Z_to_bv 5 16)) (getr R (Z_to_bv 5 17)) (getr R (Z_to_bv 5 18)) (getr R (Z_to_bv 5 19))
(getr R (Z_to_bv 5 20)) (getr R (Z_to_bv 5 21)) (getr R (Z_to_bv 5 22)) (getr R (Z_to_bv 5 23)) (getr R (Z_to_bv 5 24))
(getr R (Z_to_bv 5 25)) (getr R (Z_to_bv 5 26)) (getr R (Z_to_bv 5 27)) (getr R (Z_to_bv 5 28)) (getr R (Z_to_bv 5 29))
(getr R (Z_to_bv 5 30)) (getr R (Z_to_bv 5 31))
fp_regs fp_csr M R10) as EVT.
change (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with (canon_regs R) in EVT at 2.
destruct (evt_eqv_transfer rsegs _ _ (mkst R (Z_to_bv 64 RFREE_SYM) M (seg_rom rsegs)) (mkst_eqv_canon R _ M _) EVT)
as (ms1 & ms1' & -> & EQV & Hms).
eapply srz_msteps; [exact Hh| exact Hl| exact Hms|].
destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [-> REQ].
rewrite (ret_pc_ok _ RET). change (MS ?R' fp_regs ?pc fp_csr None ?mm ?ro) with (mkst R' pc mm ro).
apply CONT. eapply regs_preserved_canon. exact REQ.
Qed.
Theorem HI0_ok : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "5'RO&QFvS=&QD%43321").
Proof.
constructor.
- exact HI0_malloc.
- exact HI0_aligned.
- exact HI0_free.
- exact HI0_free_null.
- exact HI0_frame.
- exact HI0_wf.
- exact HI0_perm.
Qed.
End DELIVERABLES.
Lemma reserved_top_RESV : ltac2:(TCodec.tc2 tcn__CJ_Bridge_HeapInst0 "7'@'F&M&QJ%211&QB%63521").
Proof. vm_compute. reflexivity. Qed.
Section SE.
Variables (M : word -> option byte).
Variables (lim : Z).
Variables (VM : VmMaps).
Theorem HI0_init : init_statics0 M -> init_vm L0 lim VM -> hi_heap HI0 [] (hl_K0 L0, hl_B0 L0) M VM.
Proof.
intros (NONE & NONEV & NL & PS & GOT & (canary & Hcan & GUARD)
& (av & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & rnd & secret & AUXC & AVL & RND & Bav & Hav & Brnd & Hrnd
& X3 & X4 & X5 & XHW & X6 & X11 & X12 & X23 & Xr & Xs) & MI)
(brk0 & mbase & isp & -> & VB & VMB & VSP & Hisp & Hlim).
cbn [hi_heap HI0 hl_K0 hl_B0 hl_segs hl_sptop L0] in *.
destruct VB as (VB1 & VB2 & VB3). fold RESV in VB1, VB2 |- *. rewrite reserved_top_RESV in VB1, VB2.
destruct VSP as (SP1 & SP2 & SP3). rewrite Hisp in SP1, SP2, SP3. unfold sp_window_lo in SP1. unfold sp_window_hi in SP2.
assert (Hrange : CEIL_LO <= sptop - 2 ^ 23 <= CEIL_HI) by (unfold CEIL_LO, CEIL_HI; lia).
set (R0 := mkRunP (sptop - 2 ^ 23) Hrange secret Xs canary Hcan).
assert (HCEIL : @alloc_ceiling R0 = sptop - 2 ^ 23) by reflexivity.
exists R0.
destruct (@RHEAP_init_proof R0 M (Z_to_bv 64 av) ltac:(intros a Ha; apply NONE; lia) NONEV NL AUXC PS GOT GUARD MI) as [HR _].
exists (ps_init (reservedZ rsegs)), (led_init (reservedZ rsegs)), [], 0.
assert (ER : reservedZ rsegs = map wwZ RESV) by reflexivity.
splits.
- exact HCEIL.
- reflexivity.
- exact HR.
- apply creach_init.
- apply Permutation_refl.
- unfold ps_init; cbn [ps_brk].
constructor; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live led_init].
+ split; [intros e []| constructor].
+ intros e [].
+ exact ER.
+ reflexivity.
+ intros e He. enough (ehi e <= IMG_HI) by lia.
rewrite RESV_eq in He. unfold ehi.
destruct He as [<-|[<-|[<-|[<-|[]]]]]; vm_compute; discriminate.
+ rewrite HCEIL. unfold brk_aslr_max, IMG_HI, page_size, PGSZ, CEIL_LO in *. splits; first [lia| exact VB3].
+ intros b l [].
+ intros b l k [].
+ constructor.
+ intros b l H. discriminate.
+ split; reflexivity.
+ rewrite HCEIL, Hisp. lia.
- exact MI.
-
exists av, x3, x4, x5, hw, x6, x11, x12, x23, rnd. unfold RAUXV_CELL, auxv_list, wz. rewrite HCEIL.
change (@secret_val R0) with secret. splits; first [exact AUXC| exact AVL| exact RND| lia].
- intros a Ha. apply NONE. unfold RCTX in Ha. lia.
- constructor.
- lia.
- cbn [fst snd]. unfold K0, KPM, NCMAX. change (Z.of_nat EVM) with 8. lia.
- cbn [fst snd]. unfold K0, KPM, NCMAX. change (Z.of_nat EVM) with 8. lia.
- cbn [fst snd]. unfold B0. lia.
- unfold ps_init; cbn [ps_m]. rewrite pot_init. lia.
- cbn [vm_reserved vm_maps fst snd]. rewrite app_nil_r, RESV_eq. cbn [length]. unfold NSEG. lia.
- cbn [vm_reserved vm_maps]. rewrite app_nil_r, RESV_eq. unfold NMAX.
repeat (apply Forall_cons; [cbn [snd]; vm_compute; discriminate|]). apply Forall_nil.
- cbn [vm_maps live_bytes fst snd]. lia.
- cbn [vm_limit]. unfold B0. lia.
Qed.
End SE.
End LAYOUT.
