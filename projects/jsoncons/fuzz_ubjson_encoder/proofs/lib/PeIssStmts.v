(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core
     PmLayout PeLayoutS PmModel PmStatics PmSpecs PeSpecsS PmStep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeIssStmts () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2InI47Corelib4Init9Datatypes4list00C56Stdlib5Arith8PeanoNat3Nat3eqbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC46Stdlib5Lists4List7existsbI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsI47Corelib4Init5Logic2eq00C56Stdlib5Arith8PeanoNat3Nat6eqb_eqC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7forallbI47Corelib4Init9Datatypes3nat00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeIssStmts4PMIS3CSKC13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMIS.
Import PMS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Definition SCR : Z := 20480.                       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition CSK : list nat := [3; 4; 24; 25; 26; 27]%nat.
Lemma CSK_in (KS : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) CSK = true -> forall k, In k CSK -> In k KS.
Proof.
ltac2:(KReplay.run1 (kr_t_PeIssStmts ()) [] "p'0h01xi001xh11Hh21kh32Hxh42KSh51Ah61Eh71fh81lh91mh:1nh;2H0h<2Hkh=5lemmap;1p;3p;2p;7p-1R0p10000p4p710p9P0g000\R0p4p710p8g0013j1;Tg001Sj1:j22TP0j35Tg0023j2?Tg002Lj3>Tg003=j3=Tg003`R0j39Tg004<R1j24Tg004WR2j27Tg0051j3<Tg005Tj36Tg005nj2BTg006Qj7ATg006mj3@Tg007IR3f1R4f0R539p=3g007hR69@35p=8g0096R7g009V765p=0A5345p=1%;3R8%:5R9/34X23#8#0A5356R:f4R;,39X23R<#8#0f6R=,39X23P4O1#0\:^03R>'?f5R?,39X23#8#0f7R@,39X23P4O1#0\:^03;>5W=A=3<6f2R<O2P>P5P<P4O2%:</3;#0P0p4p710R0P7\5R7%;4R>P1A9<45#0f3R6A5;5<P6P5O1#0'4X06'7[R:A5654P<P5O1#0'4X0<,7<A96<4#0R9[A5?56P;P5O1#0'4X0;,7;\9A<<45P4n2001000000120000000W8W7W5P:^8>^77^50P5P3%:;P=P4O4115@12?5#0'4X03,73P2P3f8R2,1512=5#0'4X0311=2P5f:R?,151225#0'4P1f;,14f9/24#0f<R2,1?P5f=,16122;#0P11245#0A63<4[R1A634512<4#0R2[A636<\21B45P4n2001000000120000000X93X:3P1^93^:3P5f>R1P=P4O3A631=P3f?R1fB,15fAR=fC'1]3X03111=P5W3P@P5P6FAb6b1W6W3P4P5O2n2001000000120000000W1X03P4P5O2n2001000000120100000b1b;b1b1W<X23W1X48P5O1X48P5O1W4o"). Qed.
Definition vstr_at := (PM.vstr_at RSEGS PMSP.T3).
Definition iss_at := (PM.iss_at RSEGS AD PMSP.T3).

Section Call.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet).
Variables (LB : list (Z * Z)) (cr : credit) (ois os sp r : Z) (s : PM.vstr) (b : bool).

Definition WF : list L5.range := (ois, 272) :: (if b then [] else PMSP.loc_W AD).
Definition cost : credit := PM.cost1 L (PM.vs_size s + 32).

(* [comment removed for export] *)
Definition pre : Prop :=
  hi_heap HI LB cr M0 (m_vmmaps model0) /\ PMSP.model_ok model0 /\ K [] /\ PMSP.entry AD L R0 M0 sp r 4
  /\ getr R0 (reg 10) = Z_to_bv 64 ois /\ getr R0 (reg 11) = Z_to_bv 64 os /\ getr R0 (reg 12) = Z_to_bv 64 8
  /\ sp <= ois /\ ois + 272 <= os /\ os + 24 <= hl_sptop L /\ ois mod 8 = 0 /\ os mod 8 = 0 /\ L5.defined M0 ois 272
  /\ vstr_at M0 os s /\ incl (PM.vs_own s) LB /\ PM.vs_size s < 2 ^ 26 /\ (forall c n p, s = PM.VLong c n p -> 23 <= n)
  /\ PMST.base_ok RSEGS AD M0 /\ PMST.loc_ok RSEGS AD M0 b
  /\ PMSP.credit_le cost cr.

(* [comment removed for export] *)
Definition kont : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PM.vstr) (sm : PM.strm) (cr' : credit),
    regs_preserved R0 R' -> iss_at M' ois s' sm -> PM.vs_size s' = PM.vs_size s ->
    PM.sm_g sm = PM.vs_data (ois + 80) s' -> PM.sm_st sm = 0 ->
    PMST.loc_ok RSEGS AD M' true ->
    L5C.hpres L LB sp (PMSP.pm_scr 4) WF M0 M' ->
    PMSP.credit_keep cr cr' cost PMSP.cr0 ->
    model_but_vm model0 model' -> hi_heap HI (PM.vs_own s' ++ LB) cr' M' (m_vmmaps model') ->
    srealizes RSEGS SCFG (PMSP.cfg RSEGS R' r M' model') K.

(* [comment removed for export] *)
Definition saves_iss (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (sp - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (sp - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (sp - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (sp - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (sp - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (sp - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (sp - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (sp - 64) (bv_unsigned (getr R0 (reg 22)))
  /\ L5.u64_at RSEGS M (sp - 72) (bv_unsigned (getr R0 (reg 23))).
Definition saves_sb (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (sp - 88) 216512 /\ L5.u64_at RSEGS M (sp - 96) ois /\ L5.u64_at RSEGS M (sp - 104) os
  /\ L5.u64_at RSEGS M (sp - 112) 8 /\ L5.u64_at RSEGS M (sp - 120) (ois + 16) /\ L5.u64_at RSEGS M (sp - 128) (ois + 120)
  /\ L5.u64_at RSEGS M (sp - 136) 745128.
(* [comment removed for export] *)
Definition head_cells (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M ois (pa_vp_iss AD) /\ L5.u64_at RSEGS M (ois + 24) (pa_classic_imp AD)
  /\ L5.u64_at RSEGS M (ois + 120) (pa_vp_iss_ios AD) /\ L5.u32_at RSEGS M (ois + 152) 0 /\ L5.u32_at RSEGS M (ois + 156) 0
  /\ L5.u64_at RSEGS M (ois + 160) (ois + 16) /\ L5.u64_at RSEGS M (ois + 168) (pa_classic_imp AD) /\ PM.zeros_at M (ois + 176) 80.

(* [comment removed for export] *)
Definition mid (R : bvmap 5 word) (M : word -> option byte) (model : Model) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 144) /\ getr R (reg 8) = Z_to_bv 64 (ois + 16) /\ getr R (reg 9) = Z_to_bv 64 (ois + 24)
  /\ getr R (reg 19) = Z_to_bv 64 8 /\ getr R (reg 20) = Z_to_bv 64 os /\ getr R (reg 21) = Z_to_bv 64 744704
  /\ (forall k, In k CSK -> getr R (reg k) = getr R0 (reg k))
  /\ saves_iss M /\ saves_sb M /\ head_cells M
  /\ L5.defined M ois 272 /\ vstr_at M os s /\ L5C.stk (hl_sptop L) M sp SCR
  /\ PMST.base_ok RSEGS AD M /\ PMST.loc_ok RSEGS AD M true
  /\ hi_heap HI LB cr M (m_vmmaps model) /\ PMSP.model_ok model /\ model_but_vm model0 model
  /\ PMK.ek L LB sp SCR WF M0 M /\ PMK.dk L LB sp SCR M0 M.

End Call.
End PMIS.
