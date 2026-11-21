(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (vm_room restated in plain text as RoomS's vm_roomS, a bound on the count of ledger entries in place of the ledger discipline; vm_room_mono, vm_room_init, vm_room_init_P and vm_room_init_U restated for it, with reserved_count_P and reserved_count_U added). *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "prod"; "bool"; "nil"; "pair"; "cons"; "true"; "app"; "andb"; "snd"; "fst"; "length"; "nat"; "orb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "add"; "leb"; "lt"; "sub"; "of_nat"; "mul"; "eqb"; "ltb"; "max"; "modulo"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "vm_limit"; "m_vm_materialized"; "vm_reserved"; "vm_maps"; "alloc_top"; "sp_window_lo"; "vm_init_sp"; "VmMaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sstate"; "rw"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_blocks"; "MA_init"; "run_init"; "ma_L"; "ma_s"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv.WithSegs.Contracts"; "vm_room"; "drvN"; "JLi_null"; "initedT"; "JLi_ok"; "JLd_ok"; "DRV_OPS"; "JLd_free"; "init_cost"; "malloc_cost"; "pairwiseb"; "reserved_okb"; "JLd_big_ok"; "J_big_ex"; "J_free_drv"; "J_init_ex"; "J_init_pre"; "J_payload_ex"; "Post_big_ex"; "Post_init_ex"; "Post_payload_ex"; "Posts_malloc_init"; "drv_reach"; "entry_okb"; "payload_cost"; "vm_pot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsP"; "segsU"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "MInvR"; "mem_kept"; "EC_P"; "EC_U"; "L_malloc_null"; "L_malloc_ok"; "Pre_malloc"; "top_var"; "vm_insensitive"; "V_RES"; "tp_ok"; "JL_free"; "JL_malloc_null"; "JL_malloc_ok"; "J_free_pre"; "L_free"; "Pre_free"; "ok_sideK"; "top_kept"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeGap"; "total"; "zpair"; "ledger_disciplined"; "F"; "PG"; "disjoint"; "pairwise"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "C_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "free_drv_ex"; "malloc_big_ex"; "malloc_init_contract"; "malloc_init_ex"; "malloc_payload_ex"; "reserved_okb"; "vm_room"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "auxv_init"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "MMAP_THRESHOLD"; "PGSZ"; "st_init_done"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine"; "pristine_req"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymFrame SymSummary SymCall SymComplete ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocFooter MallocCalloc MallocIface Contract ContractI Pristine FreeGap.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Plain.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Ubsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.
Section Contracts.
Variable C : mconsts.
Variable E : entry_consts.

Definition J_init_pre (brk0 : run_init) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|1|
S29S4S1fA1S1eS0S81Vsegs;VC;Vbrk0;R3R1A5S0S16S35Q40S2bR3PcA2A2S7eA2S0VKc;R2R1A2S0S7dVsegs;VC;S31S2fVC;Vbrk0;A2M0A1R3A4S5bG0R3A2A2A2A2A2Lmd;Ltr;Lrho;").

Definition initedT (A A' : MA) : Prop := ltac2:(tb__ "0|0|
S0S1S6S80S32VA';A1A1SaA3S66VA;VA';A2A2").

Definition JLi_null (A : MA) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|0|
S29S29S4S1fA1S1eS2S2dS2dS0S54Vsegs;VC;R1R4R2A5S0S3aVA;R1A2S0S1S4S5S3S3A2A1S2eR1A1S2eVA;A1A3S0S55Vsegs;VC;VA;R1S2cR5A1S2cR4A1A6VKc;R3R2A2A2A2A2A2LA';A2Lmd;Ltr;Lrho';Lrho0;").

Definition JLi_ok (A : MA) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|3|
S29S29S4S1fA1S1eS2S2dS2dS2S4S5S3S3A2M0A1M1G1S2G1G1S0S54Vsegs;VC;R3R6R4A5S0S3aVA;R3A2S0S1G1S2eR3A1SbG0R2S9G0S8S3S3S35Q40M2S2bR6S5dA2A2S35G2S2bR7PcA2A2A4R1A3A3A3S0S1G1S2eVA;A1SbG0R2R1A3A3S0S55Vsegs;VC;VA;R3S2cR7A1S2cR6A1A6VKc;R5R4A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2Lmd;Ltr;Lrho';Lrho0;").

Definition Posts_malloc_init (brk0 : run_init) (Kc : list event -> Model -> Prop) : list (sstate * jpost) := ltac2:(tb__ "0|2|
S9S5S2aS33A2M0S8S2aS33S58VE;A1S39S2fVC;Vbrk0;A2M1VKc;A2A4S9G0S8S2aS33S59VE;A1S3bG1VKc;A2A4S7G0A1A3A3").

Definition malloc_init_contract : Prop := ltac2:(tb__ "0|0|
S75OF_;S30S4S1fA1S1eOF_;F_;S29S65Vsegs;R4R2A3S74Vsegs;R5S69Vsegs;S47R4R3A2S5aVE;A1R2A4S34Vsegs;S53R2S4cR4R3A2A4A4F_;Frho;FKc;Fbrk0;Fok;").

Lemma JLi_null_JL : ltac2:(tb__ "0|1|
S2dS4S1fA1M0S1eOF_;F_;S29S29G0S1eS39R6R5R4R3R2R1A6S60Vsegs;VC;R7R6R5R4R3R2A8F_;Fmd;Ftr;Frho';Frho0;FKc;FA;").
Proof using .
  intros A Kc rho0 rho' tr md (A' & HM & Hi & HB & HK & HKc). exists A'.
  split; [exact HM|]. split; [exact HB|]. split; [exact HK|]. split; [exact (conj (fun _ => proj1 Hi) (proj2 Hi))|exact HKc].
Qed.

Lemma JLi_ok_JL : ltac2:(tb__ "0|1|
S2dS4S1fA1M0S1eOF_;F_;S29S29G0S1eS3bR6R5R4R3R2R1A6S61Vsegs;VC;R7R6R5R4R3R2A8F_;Fmd;Ftr;Frho';Frho0;FKc;FA;").
Proof using .
  intros A Kc rho0 rho' tr md (A' & l1 & l2 & HM & Hi & HB' & HB & HK & HKc). exists A', l1, l2.
  split; [exact HM|]. split; [exact HB'|]. split; [exact HB|]. split; [exact HK|]. split; [exact (conj (fun _ => proj1 Hi) (proj2 Hi))|exact HKc].
Qed.

Lemma JLi_ok_init : ltac2:(tb__ "0|4|
S30S4S1fA1M0S1eOF_;F_;S29S29G0S1eS3bS2fVC;R6A2R5R4R3R2R1A6S2S2dS2dS0S54Vsegs;VC;R1R5R3A5S0S3aS2fVC;R8A2M1R1A2S0S1S4S5S3S3A2M2A1S2eR1A1S9G2S8S3S3S35Q40M3S2bR5S5dA2A2S35G3S2bR6PcA2A2A4S7G2A1A3A3S0S55Vsegs;VC;G1R1S2cR6A1S2cR5A1A6R7R4R3A2A2A2A2A2LA';A2F_;Fmd;Ftr;Frho';Frho0;FKc;Fbrk0;").
Proof using .
  intros brk0 Kc rho0 rho' tr md (A' & l1 & l2 & HM & Hi & HB' & HB & HK & HKc). exists A'.
  rewrite MA_init_blocks in HB. symmetry in HB. apply app_eq_nil in HB as [-> ->].
  split; [exact HM|]. split; [exact Hi|]. split; [exact HB'|]. split; [exact HK|exact HKc].
Qed.

Lemma JLi_null_init : ltac2:(tb__ "0|3|
S30S4S1fA1M0S1eOF_;F_;S29S29G0S1eS39S2fVC;R6A2R5R4R3R2R1A6S2S2dS2dS0S54Vsegs;VC;R1R5R3A5S0S3aS2fVC;R8A2M1R1A2S0S1S4S5S3S3A2M2A1S2eR1A1S7G2A1A3S0S55Vsegs;VC;G1R1S2cR6A1S2cR5A1A6R7R4R3A2A2A2A2A2LA';A2F_;Fmd;Ftr;Frho';Frho0;FKc;Fbrk0;").
Proof using .
  intros brk0 Kc rho0 rho' tr md (A' & HM & Hi & HB & HK & HKc). exists A'.
  rewrite MA_init_blocks in HB. split; [exact HM|]. split; [exact Hi|]. split; [exact HB|]. split; [exact HK|exact HKc].
Qed.

Definition vm_pot (md : Model) : Z := ltac2:(tb__ "0|3|
S14S6aS68S5S36Q40A1M0G0A2M1S5S3S3A2S6bSbG1S23S20Vmd;A1M2A1S24G2A1A3A4A1S19S18SfG0S22Vmd;A1A2A1S7fA2A2").

(* LPS 727298f3: the room is Malloc/RoomS.v's [vm_roomS], conjunct for conjunct, with the count
   bound first (in the place [FreeGap.ledger_disciplined] held).  Linux places an anonymous map
   top-down from the mmap base and the start-up ledger holds the vDSO pair near the top, so no
   ledger of this model keeps every entry below [FreeGap.F]; a bound on the NUMBER of entries is
   what lets RoomS.v find a free gap (and with it a non-refusable request) for any hint.
   Malloc/RoomK.v's [vm_room_S] states the equivalence. *)
Definition vm_room (md : Model) (X : Z) : Prop :=
  PGSZ * Z.of_nat (length (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md))) + X <= 2 ^ 29
  /\ 0 <= X
  /\ vm_pot md + X <= vm_limit (m_vmmaps md)
  /\ vm_limit (m_vmmaps md) <= 2 ^ 40
  /\ 140735332483072 <= alloc_top (m_vmmaps md).

Definition init_cost : Z := 2 ^ 25.
Definition malloc_cost (n : Z) : Z := n + 2 ^ 21.
Definition payload_cost (n : Z) : Z := n + 2 ^ 27.

Lemma vm_room_mono : ltac2:(tb__ "0|0|
S1eS3S3S0S12Z0R1A2S12R1R2A2A2S37R4R3A2S37R5R3A2F_;F_;FX';FX;Fmd;").
Proof using . intros md X X' HX (D & H0 & HP & HL). unfold vm_room. unfold PGSZ in *. split; [lia|]. split; [lia|]. split; [lia|exact HL]. Qed.

Lemma vm_room_frame : ltac2:(tb__ "0|0|
S1eS1eS3S1S28S20R2A1S20R3A1A3S1S4S36Q40A1A1S22R3A1S22R4A1A3S37R5R3A2S37R5R4A2F_;F_;F_;FX;Fmd';Fmd;").
Proof using .
  intros md md' X Hv Hm H. unfold vm_room, vm_pot in *. rewrite Hv, Hm. exact H.
Qed.

Lemma vm_room_nonneg : ltac2:(tb__ "0|0|
S1eS3S37R2R1A2S12Z0R2A2F_;FX;Fmd;").
Proof using . intros md X (_ & H & _). exact H. Qed.

Definition entry_okb (e : Z * Z) : bool := ltac2:(tb__ "0|3|
ScScScScS15Z0M0SeS3S3Ve;A3M1A2S15S14G1SdS3S3Ve;A3M2A2S6dA2A2S1bG0G2A2A2S1aS1dG2S6eA2G0A2A2S15G2S13Z2Z20A2A2A2").
Definition disjointb (a b : Z * Z) : bool := ltac2:(tb__ "0|2|
S11S15S14SeS3S3Va;A3M0SdS3S3Va;A3A2SeS3S3Vb;A3M1A2S15S14G1SdS3S3Vb;A3A2G0A2A2").
Fixpoint pairwiseb (l : list (Z * Z)) : bool :=
  match l with
  | [] => true
  | e :: t => forallb (disjointb e) t && pairwiseb t
  end.
Definition reserved_okb (res : list (word * word)) : bool := ltac2:(tb__ "0|3|
ScS82S5S3S3A2M0S4eS68S5S36Q40A1M1G1A2G0S6bVres;A4M2A3S41G2A1A2").

Lemma pairwiseb_sound : ltac2:(tb__ "0|1|
S4S5S3S3A2M0A1S1S6S41R1A1SaA3S70G0S6fR2A3F_;Fl;").
Proof using .
  induction l as [|e t IH]; cbn; intros H; [exact I|].
  apply andb_prop in H as [H1 H2]. split; [|apply IH; exact H2].
  intros y Hy. rewrite forallb_forall in H1. specialize (H1 y Hy).
  unfold disjointb in H1. unfold FreeGap.disjoint. apply Bool.orb_prop in H1.
  destruct H1 as [H1|H1]; apply Z.leb_le in H1; lia.
Qed.

Lemma reserved_okb_sound : ltac2:(tb__ "0|1|
S4S5S36Q40A1M0G0A2A1S1S6S42R1A1SaA3S6cR2A1F_;Fres;").
Proof using .
  intros res H. apply andb_prop in H as [H1 H2]. split.
  - intros e He. rewrite forallb_forall in H1. specialize (H1 (zpair e) ltac:(apply in_map; exact He)).
    unfold entry_okb in H1. rewrite !Bool.andb_true_iff in H1. destruct H1 as ((((A1 & A2) & A3) & A4) & A5).
    apply Z.leb_le in A1. apply Z.leb_le in A2. apply Z.ltb_lt in A3. apply Z.eqb_eq in A4. apply Z.leb_le in A5.
    unfold entry_ok, below_F, page_len. repeat split; auto.
  - apply pairwiseb_sound. exact H2.
Qed.

Lemma total_le_bound : ltac2:(tb__ "0|4|
S4S5S3S3A2M0A1S3S1S6S82G0G0ScS15Z0M1SdS3S3R1A3M2A2S15G2R2A2A2Le;R2A3SaA3S0S12G1S6aR3A1M3A2S12G3S19S18SfG0R3A2A1S1cG1R2A2A2A2A2F_;FB;Fl;").
Proof using .
  induction l as [|e t IH]; cbn; intros B H; [unfold FreeGap.total; cbn; lia|].
  apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [H0 H1]. apply Z.leb_le in H0. apply Z.leb_le in H1.
  specialize (IH B H2). unfold FreeGap.total in *. cbn. lia.
Qed.

(* LPS 727298f3: the room's count bound replaces the reserved-entry discipline: at most eight
   reserved entries and room below [2 ^ 29] (Malloc/RoomS.v's [vm_roomS_init] premises). *)
Lemma vm_room_init : forall (md : Model) (X : Z),
  vm_maps (m_vmmaps md) = [] -> m_vm_materialized md = [] ->
  (length (vm_reserved (m_vmmaps md)) <= 8)%nat ->
  FreeGap.total (map zpair (vm_reserved (m_vmmaps md))) <= 2 ^ 20 ->
  0 <= X -> X + 2 ^ 20 <= vm_limit (m_vmmaps md) -> vm_limit (m_vmmaps md) <= 2 ^ 40 ->
  X + 2 ^ 16 <= 2 ^ 29 ->
  140735332483072 <= alloc_top (m_vmmaps md) ->
  vm_room md X.
Proof using .
  intros md X Hmaps Hmat Hres Htot HX Hlim Hlim' HXC Htop.
  unfold vm_room, vm_pot. rewrite Hmaps, Hmat, app_nil_r. cbn [length Z.of_nat].
  apply Nat2Z.inj_le in Hres. unfold PGSZ.
  split; [lia|]. split; [exact HX|]. split; [|split; [exact Hlim'|exact Htop]]. lia.
Qed.

Inductive drv_reach : nat -> MA -> Prop :=
| DR_init : forall (brk0 : run_init) tr p A',
    malloc_rel (MA_init C brk0) 65536 tr p A' -> p <> 0 -> drv_reach 0 A'
| DR_malloc : forall j A n tr p A',
    drv_reach j A -> MMAP_THRESHOLD <= n <= 2 ^ 26 -> malloc_rel A n tr p A' -> drv_reach (Datatypes.S j) A'
| DR_free : forall j A b tr A',
    drv_reach j A -> free_rel A b tr A' -> drv_reach (Datatypes.S j) A'.

Definition DRV_OPS : Z := 40.

Definition drvN (k : Z) (A : MA) : Prop := ltac2:(tb__ "0|0|
S2S10S10S0S4dR1VA;A2S0S12Z0Vk;A2S12S14S18R1A1Vk;A2S3dA2A2A2Lj;A2").

Lemma drvN_le : ltac2:(tb__ "0|0|
S3S3S2dS0S12Z0R2A2S12R2R3A2A2S38R4R2A2S38R4R3A2F_;F_;FA;Fk';Fk;").
Proof using . intros k k' A Hk (j & Hr & H0 & Hj). exists j. repeat split; auto; lia. Qed.

Lemma drvN_nonneg : ltac2:(tb__ "0|0|
S3S2dS38R2R1A2S12Z0R3A2F_;FA;Fk;").
Proof using . intros k A (j & _ & H & _). exact H. Qed.

Definition JLd_ok (A : MA) (k X : Z) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|3|
S29S29S4S1fA1S1eS2S2dS2dS2S4S5S3S3A2M0A1M1G1S2G1G1S0S54Vsegs;VC;R3R6R4A5S0S3aVA;R3A2S0S38Vk;R3A2S0S37R4VX;A2S0S1G1S2eR3A1SbG0R2S9G0S8S3S3S35Q40M2S2bR6S5dA2A2S35G2S2bR7PcA2A2A4R1A3A3A3S0S1G1S2eVA;A1SbG0R2R1A3A3S0S55Vsegs;VC;VA;R3S2cR7A1S2cR6A1A6VKc;R5R4A2A2A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2Lmd;Ltr;Lrho';Lrho0;").

Lemma JLd_ok_JLi : ltac2:(tb__ "0|1|
S2dS3S3S4S1fA1M0S1eOF_;F_;S29S29G0S1eS3cR8R7R6R5R4R3R2R1A8S3bR9R6R5R4R3R2A6F_;Fmd;Ftr;Frho';Frho0;FKc;FX;Fk;FA;").
Proof using .
  intros A k X Kc rho0 rho' tr md (A' & l1 & l2 & HM & Hi & _ & _ & HB' & HB & HK & HKc).
  exists A', l1, l2. split; [exact HM|]. split; [exact Hi|]. split; [exact HB'|]. split; [exact HB|]. split; [exact HK|exact HKc].
Qed.

Definition J_init_ex (b : bool) (brk0 : run_init) (X : Z) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|1|
S29S4S1fA1S1eS0S81Vsegs;VC;Vbrk0;R3R1A5S0S1S3S35Q40S2bR3PcA2A2Z10000A3S0VKc;R2R1A2S0S1S6Vb;SaA3S0S37R2VX;A2S12S3fVX;A2A2F_;S0S7dVsegs;VC;S31S2fVC;Vbrk0;A2M0A1R3A4S5bG0R3A2A2A2A2A2A2Lmd;Ltr;Lrho;").

Definition Post_init_ex (b : bool) (brk0 : run_init) (X : Z) (Kc : list event -> Model -> Prop) : sstate * jpost := ltac2:(tb__ "0|1|
S6S5S2aS33A2Lb;Vb;S8S2aS33S59VE;A1S3cS2fVC;Vbrk0;A2M0S3dS17VX;S3fA2VKc;A4A4S8S2aS33S58VE;A1S39G0VKc;A2A4X6x2").

Definition malloc_init_ex (b : bool) : Prop := ltac2:(tb__ "0|1|
S30S3S4S1fA1S1eOF_;F_;S29S5cR2A1S73Vsegs;S69Vsegs;S46Vb;R5R4R3A4S5aVE;A1R2A4S34Vsegs;S53R2S9S5S2aS33A2M0S4aVb;R5R4R3A4S7G0A1A3A4A3F_;Frho;FKc;FX;Fbrk0;").

Definition J_big_ex (b : bool) (A : MA) (k X : Z) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|3|
S29S4S1fA1S1eS0S54Vsegs;VC;VA;R3R1A5S0S38Vk;VA;A2S0S16Z0Vk;A2S0S0S12S7eS35Q40M0S2bR3PcM1A2A2M2A2S12G2S13Z2Z1aA2A2A2S0VKc;R2R1A2S0S1S6Vb;SaA3S0S37R2VX;A2S12S40S35G0S2bR4G1A2A2A1VX;A2A2F_;S0S5eVC;R3A2S5bVA;R3A2A2A2A2A2A2A2A2Lmd;Ltr;Lrho;").

Definition JLd_big_ok (A : MA) (k X : Z) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|0|
S29S29S4S1fA1S1eS3cVA;S17Vk;Z1A2S17VX;S40S35Q40S2bR4PcA2A2A1A2VKc;R4R3R2R1A8Lmd;Ltr;Lrho';Lrho0;").

Definition Post_big_ex (b : bool) (A : MA) (k X : Z) (Kc : list event -> Model -> Prop) : sstate * jpost := ltac2:(tb__ "0|0|
S6S5S2aS33A2Lb;Vb;S8S2aS33S59VE;A1S43VA;Vk;VX;VKc;A4A4S8S2aS33S58VE;A1S39VA;VKc;A2A4X6x2").

Definition malloc_big_ex (b : bool) : Prop := ltac2:(tb__ "0|1|
S2dS3S3S4S1fA1S1eOF_;F_;S29S5cR2A1S73Vsegs;S69Vsegs;S44Vb;R6R5R4R3A5S5aVE;A1R2A4S34Vsegs;S53R2S9S5S2aS33A2M0S49Vb;R6R5R4R3A5S7G0A1A3A4A3F_;Frho;FKc;FX;Fk;FA;").

Definition J_free_drv (A : MA) (k X : Z) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|0|
S29S4S1fA1S1eS0S62Vsegs;VC;VA;VKc;R3R2R1A7S0S38Vk;VA;A2S0S16Z0Vk;A2S37R1VX;A2A2A2A2Lmd;Ltr;Lrho;").

Definition JLd_free (A : MA) (k X : Z) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|3|
S29S29S4S1fA1S1eS2S2dS2dS2S4S5S3S3A2M0A1M1G1S2G1G1S0S54Vsegs;VC;R3R6R4A5S0S3aVA;R3A2S0S38Vk;R3A2S0S37R4VX;A2S0S1G1S2eVA;A1SbG0R2S9G0S8S3S3S35Q40M2S2bR7PcA2A2S35G2S2bR7PdA2A2A4R1A3A3A3S0S1G1S2eR3A1SbG0R2R1A3A3S0S55Vsegs;VC;VA;R3S2cR7A1S2cR6A1A6VKc;R5R4A2A2A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2Lmd;Ltr;Lrho';Lrho0;").

Definition free_drv_ex : Prop := ltac2:(tb__ "0|1|
S2dS3S3S4S1fA1S1eOF_;F_;S29S5cR2A1S73Vsegs;S69Vsegs;S45R6R5R4R3A4S64VE;A1R2A4S34Vsegs;S53R2S9S5S2aS33A2M0S8S2aS33S63VE;A1S3eR6S17R5Z1A2R4R3A4A4S7G0A1A3A4A3F_;Frho;FKc;FX;Fk;FA;").

Lemma JLd_free_JL : ltac2:(tb__ "0|1|
S2dS3S3S4S1fA1M0S1eOF_;F_;S29S29G0S1eS3eR8R7R6R5R4R3R2R1A8S5fVsegs;VC;R9R6R5R4R3R2A8F_;Fmd;Ftr;Frho';Frho0;FKc;FX;Fk;FA;").
Proof using .
  intros A k X Kc rho0 rho' tr md (A' & l1 & l2 & HM & Hi & _ & _ & HB & HB' & HK & HKc).
  exists A', l1, l2. split; [exact HM|]. split; [exact HB|]. split; [exact HB'|]. split; [exact HK|]. split; [exact (conj (fun _ => proj1 Hi) (proj2 Hi))|exact HKc].
Qed.

Definition J_payload_ex (b : bool) (A : MA) (k X : Z) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|3|
S29S4S1fA1S1eS0S54Vsegs;VC;VA;R3R1A5S0S38Vk;VA;A2S0S0S16Z0S35Q40M0S2bR3PcM1A2A2M2A2S12G2S13Z2Z1aA2A2A2S0VKc;R2R1A2S0S1S6Vb;SaA3S0S37R2VX;A2S12S4fS35G0S2bR4G1A2A2A1VX;A2A2F_;S0S5eVC;R3A2S5bVA;R3A2A2A2A2A2A2A2Lmd;Ltr;Lrho;").

Definition Post_payload_ex (b : bool) (A : MA) (Kc : list event -> Model -> Prop) : sstate * jpost := ltac2:(tb__ "0|0|
S6S5S2aS33A2Lb;Vb;S8S2aS33S59VE;A1S3bVA;VKc;A2A4S8S2aS33S58VE;A1S39VA;VKc;A2A4X6x2").

Definition malloc_payload_ex (b : bool) : Prop := ltac2:(tb__ "0|1|
S2dS3S3S4S1fA1S1eOF_;F_;S29S5cR2A1S73Vsegs;S69Vsegs;S48Vb;R6R5R4R3A5S5aVE;A1R2A4S34Vsegs;S53R2S9S5S2aS33A2M0S4bVb;R6R3A3S7G0A1A3A4A3F_;Frho;FKc;FX;Fk;FA;").

End Contracts.
End WithSegs.

Definition malloc_init_contract_P : Prop := ltac2:(tb__ "0|0|
S78S51S71S56A3").
Definition malloc_init_contract_U : Prop := ltac2:(tb__ "0|0|
S78S52S72S57A3").
Definition malloc_init_ex_P (b : bool) : Prop := ltac2:(tb__ "0|0|
S79S51S71S56Vb;A4").
Definition malloc_init_ex_U (b : bool) : Prop := ltac2:(tb__ "0|0|
S79S52S72S57Vb;A4").
Definition malloc_big_ex_P (b : bool) : Prop := ltac2:(tb__ "0|0|
S77S51S71S56Vb;A4").
Definition malloc_big_ex_U (b : bool) : Prop := ltac2:(tb__ "0|0|
S77S52S72S57Vb;A4").
Definition free_drv_ex_P : Prop := ltac2:(tb__ "0|0|
S76S51S71S56A3").
Definition free_drv_ex_U : Prop := ltac2:(tb__ "0|0|
S76S52S72S57A3").
Definition malloc_payload_ex_P (b : bool) : Prop := ltac2:(tb__ "0|0|
S7aS51S71S56Vb;A4").
Definition malloc_payload_ex_U (b : bool) : Prop := ltac2:(tb__ "0|0|
S7aS52S72S57Vb;A4").

Lemma reserved_okb_P : ltac2:(tb__ "0|0|
S1S6S7bS67S51A1A1SaA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma reserved_okb_U : ltac2:(tb__ "0|0|
S1S6S7bS67S52A1A1SaA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma reserved_count_P : (length (segments_reserved segsP) <= 8)%nat.
Proof. vm_compute. repeat constructor. Qed.
Lemma reserved_count_U : (length (segments_reserved segsU) <= 8)%nat.
Proof. vm_compute. repeat constructor. Qed.
Lemma reserved_total_P : ltac2:(tb__ "0|1|
S12S6aS68S5S36Q40A1M0G0A2S5S3S3A2S6bS67S51A1A4A1S13Z2Z14A2A2").
Proof.
  assert (H : (FreeGap.total (map zpair (segments_reserved segsP)) <=? 2 ^ 20) = true) by (vm_cast_no_check (@eq_refl bool true)).
  apply Z.leb_le in H. exact H.
Qed.
Lemma reserved_total_U : ltac2:(tb__ "0|1|
S12S6aS68S5S36Q40A1M0G0A2S5S3S3A2S6bS67S52A1A4A1S13Z2Z14A2A2").
Proof.
  assert (H : (FreeGap.total (map zpair (segments_reserved segsU)) <=? 2 ^ 20) = true) by (vm_cast_no_check (@eq_refl bool true)).
  apply Z.leb_le in H. exact H.
Qed.

Theorem vm_room_init_P : forall (md : Model) (X : Z),
  vm_reserved (m_vmmaps md) = segments_reserved segsP ->
  vm_maps (m_vmmaps md) = [] -> m_vm_materialized md = [] ->
  0 <= X -> X + 2 ^ 20 <= vm_limit (m_vmmaps md) -> vm_limit (m_vmmaps md) <= 2 ^ 40 ->
  X + 2 ^ 16 <= 2 ^ 29 ->
  sp_window_lo <= bv_unsigned (vm_init_sp (m_vmmaps md)) ->
  vm_room md X.
Proof.
  intros md X Hres Hmaps Hmat HX Hlim Hlim' HXC Hsp. apply vm_room_init; auto.
  - rewrite Hres. exact reserved_count_P.
  - rewrite Hres. exact reserved_total_P.
  - unfold alloc_top, stack_max_size, sp_window_lo in *. lia.
Qed.

Theorem vm_room_init_U : forall (md : Model) (X : Z),
  vm_reserved (m_vmmaps md) = segments_reserved segsU ->
  vm_maps (m_vmmaps md) = [] -> m_vm_materialized md = [] ->
  0 <= X -> X + 2 ^ 20 <= vm_limit (m_vmmaps md) -> vm_limit (m_vmmaps md) <= 2 ^ 40 ->
  X + 2 ^ 16 <= 2 ^ 29 ->
  sp_window_lo <= bv_unsigned (vm_init_sp (m_vmmaps md)) ->
  vm_room md X.
Proof.
  intros md X Hres Hmaps Hmat HX Hlim Hlim' HXC Hsp. apply vm_room_init; auto.
  - rewrite Hres. exact reserved_count_U.
  - rewrite Hres. exact reserved_total_U.
  - unfold alloc_top, stack_max_size, sp_window_lo in *. lia.
Qed.

