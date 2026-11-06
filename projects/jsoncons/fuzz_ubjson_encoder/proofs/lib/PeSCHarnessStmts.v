(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface LibIface LibIfaceE L5Defs L5Core
     PmLayout PmModel PmStatics PmSpecs PmStep PeSpecsS PeCLayout PeCLayoutS PeCSink PeCModel PeCSpecs PeCSpecsS PeCStatics PeCTopS.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef UbjRefFacts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeSCHarnessStmts () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstI47Corelib4Init9Datatypes4list00C56Stdlib5Arith8PeanoNat3Nat3eqbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC46Stdlib5Lists4List7existsbI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsI47Corelib4Init5Logic2eq00C56Stdlib5Arith8PeanoNat3Nat6eqb_eqC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7forallbI47Corelib4Init9Datatypes3nat00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@PeSCHarnessStmts4PECH3CSKC13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECH.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation AD := PeCLayoutS.CADDR_S.
Abbreviation EE := PeCLayoutS.EADDR_S.

Definition FRAME : Z := 832.
Definition SCR : Z := 65536.                      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition SV : Z := 816.
(* [comment removed for export] *)
Definition CSK : list nat := [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma CSK_in (KS : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) CSK = true -> forall k, In k CSK -> In k KS.
Proof.
ltac2:(KReplay.run1 (kr_t_PeSCHarnessStmts ()) [] "p'0h01xi001xh11Hh21kh32Hxh41Ah51Eh62KSh71fh81lh91mh:1nh;2H0h<2Hkh=5lemmap;1p;3p;2p;7p-1R0p10000p4p710p9P0g000\R1p4p710p8P0p10013p4p710p8P0p1001OR2p4p710p8P0P2p4p7210p8g001lj1;Tg002Lj1:j22TP1j35Tg002lj2?Tg003Ej3>Tg0046j3=Tg004YR1j39Tg0055R2j24Tg005PR0j27Tg005jj3<Tg006Mj36Tg006gj2BTg007Jj7ATg007fj3@Tg008BR3f1R4f0R539p=3g008aR69@35p=8g00:5R7g00:U765p=0A5345p=1%;3R8%:5R9/34X23#8#0A5356R:f4R;,39X23R<#8#0f6R=,39X23P4O1#0\:^03R>'?f5R?,39X23#8#0f7R@,39X23P4O1#0\:^03;>5W=A=3<6f2R<O2P>P5P<P4O2%:</3;#0P1p4p710R1P7\5R7%;4R>P2A9<45#0f3R6A5;5<P6P5O1#0'4X06'7[R:A5654P<P5O1#0'4X0<,7<A96<4#0R9[A5?56P;P5O1#0'4X0;,7;\9A<<45P4n2001000000120000000W8W7W4P:^8>^77^41P5P3%:;P=P4O4115@12?5#0'4X03,73P0P3f8R0,1512=5#0'4X0311=0P5f:R?,151205#0'4P2f;,14f9/24#0f<R0,1?P5f=,16120;#0P21245#0A63<4[R2A634512<4#0R0[A636<\01B45P4n2001000000120000000X93X:3P2^93^:3P5f>R2P=P4O3A632=P3f?R2fB,15fAR=fC'1]3X03112=P5W3P@P5P6FAb5b1W5W3P4P5O2n2001000000120000000W1X03P4P5O2n2001000000120100000b1b;b1b1W<X23W1X68P5O1W6o"). Qed.
(* [comment removed for export] *)
Definition WF : list L5.range := map (fun iv => (fst iv, snd iv - fst iv)) (pm_foot AD).

Section Call.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Variable P : PESK.sink_policy.
Variable R0 : bvmap 5 word.
Variable M0 : word -> option byte.
Variable model0 : Model.
Variables (sp ptr ra : Z).
Variable payload : list byte.
Variable LB0 : list (Z * Z).
Variable cr0 : credit.
Variable g : PMST.st.

Definition n : Z := Z.of_nat (length payload).
Definition p : list Z := map bv_unsigned payload.
Definition fb : Z := sp - FRAME.
(* [comment removed for export] *)
Definition P0 : credit := PEC.credit_add (PM.pot_call L n) (PEC.credit_add (PEC.pot_estack L 0) (PESK.sink_pot P 0)).

#[local] Notation T3 := PMSP.T3.
#[local] Notation T4 := PMSP.T4.
Abbreviation vstr_at := (PM.vstr_at RSEGS T3).
Abbreviation iss_at := (PM.iss_at RSEGS AD T3).
Abbreviation parser_at := (PM.parser_at RSEGS AD T3 T4).
Abbreviation enc_at := (PEC.enc_at RSEGS EE L T3 T4).
Abbreviation sink_at := (PESK.sink_at RSEGS L T3 T4 P).

(* [comment removed for export] *)
Definition hcore (R : bvmap 5 word) (M : word -> option byte) (model : Model) : Prop :=
  getr R (reg 2) = Z_to_bv 64 fb
  /\ (forall k, In k CSK -> getr R (reg k) = getr R0 (reg k))
  /\ L5.u64_at RSEGS M (fb + 824) ra /\ L5.u64_at RSEGS M (fb + 816) (bv_unsigned (getr R0 (reg 8)))
  /\ L5C.stk (hl_sptop L) M fb (SCR - FRAME) /\ L5.defined M fb FRAME /\ sp <= hl_sptop L
  /\ PMK.ek L LB0 sp SCR WF M0 M /\ (forall b, In b LB0 -> fst b + snd b <= hl_ceil L)
  /\ PMST.base_ok RSEGS AD M
  /\ model_but_vm model0 model /\ PMSP.model_ok model.

(* [comment removed for export] *)
Definition hstat (M : word -> option byte) (bl bs be : bool) : Prop :=
  PMST.loc_ok RSEGS AD M bl /\ PMST.sys_ok RSEGS AD M bs /\ PEST.err_ok RSEGS AD EE M be.

Definition rest1 : credit := PEC.credit_add (PM.cost1 L (n + 32)) (PEC.credit_add (PM.credit_add (PM.cost1 L PM.CHUNK) (PM.cost1 L 32))
                               (PEC.credit_add (PM.pot_parser L (PMSP.pst_reset (PMSP.parser_init 0 0))) (PEC.credit_add (PEC.pot_estack L 0) (PESK.sink_pot P 0)))).
Definition rest2 : credit := PEC.credit_add (PM.credit_add (PM.cost1 L PM.CHUNK) (PM.cost1 L 32))
                               (PEC.credit_add (PM.pot_parser L (PMSP.pst_reset (PMSP.parser_init 0 0))) (PEC.credit_add (PEC.pot_estack L 0) (PESK.sink_pot P 0))).
Definition rest3 : credit := PEC.credit_add (PM.pot_parser L (PMSP.pst_reset (PMSP.parser_init 0 0))) (PEC.credit_add (PEC.pot_estack L 0) (PESK.sink_pot P 0)).

(* [comment removed for export] *)
Definition H1 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s : PM.vstr) : Prop :=
  hcore R M model /\ vstr_at M (fb + 792) s /\ PM.vs_size s = n /\ L5.bytes_at RSEGS M (PM.vs_data (fb + 792) s) p
  /\ hstat M (PMST.st_loc g) (PMST.st_sys g) (PMST.st_err g)
  /\ hi_heap HI (PM.vs_own s ++ LB0) cr M (m_vmmaps model) /\ PMSP.credit_keep cr0 cr P0 rest1
  /\ (forall c n' q, s = PM.VLong c n' q -> 23 <= n').

(* [comment removed for export] *)
Definition H2 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (sm : PM.strm) : Prop :=
  hcore R M model /\ vstr_at M (fb + 792) s /\ PM.vs_size s = n
  /\ iss_at M (fb + 520) s2 sm /\ PM.vs_size s2 = n /\ PM.sm_g sm = PM.vs_data (fb + 600) s2 /\ PM.sm_st sm = 0
  /\ L5.bytes_at RSEGS M (PM.vs_data (fb + 600) s2) p
  /\ hstat M true (PMST.st_sys g) (PMST.st_err g)
  /\ hi_heap HI (PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model) /\ PMSP.credit_keep cr0 cr P0 rest2.

(* [comment removed for export] *)
Definition H3 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (sm : PM.strm) (qc b : Z) : Prop :=
  hcore R M model /\ vstr_at M (fb + 792) s /\ PM.vs_size s = n
  /\ iss_at M (fb + 520) s2 sm /\ PM.vs_size s2 = n /\ PM.sm_g sm = PM.vs_data (fb + 600) s2 /\ PM.sm_st sm = 0
  /\ L5.bytes_at RSEGS M (PM.vs_data (fb + 600) s2) p
  /\ parser_at M (fb + 48) (fb + 520) (PMSP.parser_init qc b) /\ enc_at M (fb + 440) fb PEC.enc0 /\ sink_at M (fb + 496) PESK.sink0
  /\ hstat M true (PMST.st_sys g) (PMST.st_err g)
  /\ hi_heap HI (PM.parser_own (PMSP.parser_init qc b) ++ PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr P0 rest3.

(* [comment removed for export] *)
Definition H4 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (sm : PM.strm) (qc b : Z) : Prop :=
  hcore R M model /\ vstr_at M (fb + 792) s /\ PM.vs_size s = n
  /\ PEC.crun_pre RSEGS AD EE L T3 T4 P M fb p UbjRef.init (PMSP.pst_reset (PMSP.parser_init qc b)) s2 sm PEC.enc0 PESK.sink0 (PMST.st_err g) (pa_syscat_obj AD)
  /\ PM.vs_size s2 = n
  /\ hstat M true true (PMST.st_err g)
  /\ hi_heap HI (PEC.owned (PMSP.pst_reset (PMSP.parser_init qc b)) PEC.enc0 PESK.sink0 ++ PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr P0 rest3.

(* [comment removed for export] *)
Definition H5 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (sm : PM.strm)
           (s' : PM.pst) (en : PEC.enc) (k : PESK.sink) (be : bool) (nn : nat) : Prop :=
  hcore R M model /\ vstr_at M (fb + 792) s /\ PM.vs_size s = n
  /\ iss_at M (fb + 520) s2 sm /\ parser_at M (fb + 48) (fb + 520) s' /\ enc_at M (fb + 440) fb en /\ sink_at M (fb + 496) k /\ L5.defined M (fb + 16) 16
  /\ halted (run nn p UbjRef.init) = true /\ s_lo (run nn p UbjRef.init) <= PESK.sk_z k <= s_hi (run nn p UbjRef.init)
  /\ hstat M true true be /\ (PMST.st_err g = true -> be = true)
  /\ hi_heap HI (PEC.owned s' en k ++ PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr P0 (PESK.sink_pot P (PESK.sk_c k)).

(* [comment removed for export] *)
Definition H6 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (sm : PM.strm) (be : bool) : Prop :=
  hcore R M model /\ vstr_at M (fb + 792) s /\ PM.vs_size s = n
  /\ iss_at M (fb + 520) s2 sm
  /\ hstat M true true be /\ (PMST.st_err g = true -> be = true)
  /\ hi_heap HI (PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr P0 PMSP.cr0.

(* [comment removed for export] *)
Definition H7 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s : PM.vstr) (be : bool) : Prop :=
  hcore R M model /\ vstr_at M (fb + 792) s
  /\ hstat M true true be /\ (PMST.st_err g = true -> be = true)
  /\ hi_heap HI (PM.vs_own s ++ LB0) cr M (m_vmmaps model)
  /\ PMSP.credit_keep cr0 cr P0 PMSP.cr0.

(* [comment removed for export] *)
End Call.
End PECH.
