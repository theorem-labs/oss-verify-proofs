(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (segment 7's states per CONFIG_RSEQ, computed in the build from segment 6's computed exit through musl malloc(40) with its per-flag interface state; the exit then joined into one state for both values by a fixed rule: the auxv tail the CONFIG_RSEQ layout adds split off and dropped, and the cells the two values do not share forgotten). *)

Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_019.   (* [comment removed for export] *)
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "true"; "nil"; "bool"; "Some"; "list"; "option"; "false"; "prod"; "length"; "app"; "negb"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "sprop"; "SAlu"; "ss_objs"; "cell"; "SVar"; "sstate"; "SPUle"; "mkObj"; "SExt"; "DUnknown"; "ss_facts"; "DImage"; "ob_base"; "ob_hi"; "ob_lo"; "ss_next"; "swf"; "ob_dflt"; "odefault"; "ss_pc"; "ss_regs"; "SPAlign"; "ob_cells"; "DZero"; "mkCell"; "sprop_below"; "ss_fregs"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "sym_runA"; "entailsA"; "mkAX"; "mkLeafA"; "ax_setS"; "axwf"; "cell_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7States"; "C18e"; "JPC18"; "J18S"; "K18S"; "XB18"; "o18ssp"; "o18win"; "sJ18"; "C18"; "E18g"; "R18"; "SP18"; "T18c1"; "U18b"; "U18c"; "s18"; "AUXV18"; "C18a"; "C18b"; "C18c"; "C18d"; "C18d'"; "J18"; "L18a"; "T18b"; "T18c"; "myregs18"; "ogrp18c"; "I18af"; "I18bf"; "I18cf"; "L18b"; "L18c"; "X18"; "XE18"; "XL18"; "bytes18"; "o18errno"; "o18ssp_m"; "refact18"; "EV18"; "I18a"; "I18b"; "I18c"; "K18a"; "o18ssp_s"; "oarea18b"; "oarea18c"; "owin18"; "E18b"; "F18"; "odummy18"; "splits18"; "@Corelib.Lists.ListDef"; "nth"; "map"; "seq"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface"; "Pre_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "replace_obj_at"; "move_obj_last"; "obj_to_unknown"; "split_chain"; "@Stdlib.Lists.List"; "nth_error"; "existsb"; "forallb"; "filter"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_postA3"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.MuslMalloc40Post"; "P_null0"; "P_null1"; "P_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6bStates"; "E18"; "MALLOC_ENTRY"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init Code KxA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.MuslMalloc40Post.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartRegenS2c.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Relaunch.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.StartGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.Start6JStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6bStates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition AUXV18 : sv := ltac2:(tb__ "0|1|
S14S72S14S72S14S72S17P1A1S14S74S17P2A1S11Z3A1M0A3A3S14S74S17P3A1G0A3A3S11Z18A1A3").
Definition SP18 : sv := SAlu ALU_ADD (SVar 1%positive) (SLit (-240)).
Definition XB18 : sv := SVar 84%positive.
Definition XL18 : sv := SVar 85%positive.
Definition XE18 : sv := SAlu ALU_ADD XB18 XL18.
Definition F18 : list sprop := ltac2:(tb__ "0|4|
S0S13S28P54Z6M0A2S0S13S28P55G0A2S0S13S19S14S72S3eS11Z200A1A3S45A2S0S13S19S45S5cA2S0S13S19S3eS17P6A1M1A2S0S13S19S14S72G1S11Z10A1A3S5cA2S0S13S19S5dS11S81Z2M2Z28A2A1A2S0S13S19S11Z7fff7f000000A1S3eA2S0S13S19S3eS11S81G2Z30A2A1A2S0S13S19S5cS11S81G2Z2fA2M3A1A2S0S13S19S14S72S45S11Z140A1A3G1A2S0S13S19S14S72S45S11Z40A1A3S4aA2S0S13S19S11Z7fff80000000A1S4aA2S0S13S19S4aS11S82G3S81G2Z16A2A2A1A2S4S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition X18 : list (sv * sv) := ltac2:(tb__ "0|1|
S0SaS10S10A2M0S2S10S10S3eS5dA4S4G0A1A3").

(* LPS 727298f3: segment 7 per CONFIG_RSEQ [r], from segment 6's computed exit [Start6R.E18 r]
   (A/StartRegenS2c.v).  Each state the recorded module computed with [Eval vm_compute] is computed for
   [r = false] ([X_0]) and [r = true] ([X_1]) by the same definition, [X r] selecting between them; a
   state written as a term of earlier states is that term over the per-flag ones.  The per-flag exit is
   [K18Sr r] / [K18r r]; the exit both values share, [K18S] / [K18], is made at the end by a fixed rule
   (the auxv object's tail the CONFIG_RSEQ layout adds split off and dropped, then the cells the two
   values do not share forgotten); A/StartRegen3.v proves it a weakening of [K18r r]. *)
Definition E18r (r : bool) : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartRegenS2c.Start6R.E18 r.

Definition E18b_0 : sstate := Eval vm_compute in
  (let St := ax_S (E18r false) in mkSS (ss_pc St) (ss_regs St) (ss_fregs St) (ss_fcsr St) (ss_resv St) (ss_objs St) (ss_facts St) 86%positive (ss_lenient St)).
Definition E18b_1 : sstate := Eval vm_compute in
  (let St := ax_S (E18r true) in mkSS (ss_pc St) (ss_regs St) (ss_fregs St) (ss_fcsr St) (ss_resv St) (ss_objs St) (ss_facts St) 86%positive (ss_lenient St)).
Definition E18b (r : bool) : sstate := if r then E18b_1 else E18b_0.
Definition E18g_0 : sstate := Eval vm_compute in
  (let St := ax_S (E18r false) in mkSS (ss_pc St) (ss_regs St) (ss_fregs St) (ss_fcsr St) (ss_resv St) (ss_objs St) (F18 ++ ss_facts St) 86%positive (ss_lenient St)).
Definition E18g_1 : sstate := Eval vm_compute in
  (let St := ax_S (E18r true) in mkSS (ss_pc St) (ss_regs St) (ss_fregs St) (ss_fcsr St) (ss_resv St) (ss_objs St) (F18 ++ ss_facts St) 86%positive (ss_lenient St)).
Definition E18g (r : bool) : sstate := if r then E18g_1 else E18g_0.
Lemma sd18 : forall r : bool,
  state_diff (E18b r) (E18g r) = Some ([], F18) /\ swf (E18g r) = true /\ ss_next (E18g r) = 86%positive.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition splits18 : list (nat * sv) := ltac2:(tb__ "0|4|
S0SaS1S10A2M0S2S1S10U16M1S11Nbf0A1A4S0G0S2S1S10U17M2S11Nf0A1A4S0G0S2S1S10UeS11Z624514A1A4S0G0S2S1S10UfS11Z624518A1A4S0G0S2S1S10U10S11Z6445f8A1A4S0G0S2S1S10U11S11Z644600A1A4S0G0S2S1S10U12S11Z64484bA1A4S0G0S2S1S10U13S11Z64484cA1A4S0G0S2S1S10U14S11Z644850A1A4S0G0S2S1S10U15S11Z644858A1A4S0G0S2S1S10G1S11Z644878A1A4S0G0S2S1S10G2S11Z644880A1A4S0G0S2S1S10U18S11Z6448c0A1A4S0G0S2S1S10U19S11Z644c68A1A4S0G0S2S1S10U1aS11Z645510A1A4S0G0S2S1S10U1bS11Z645518A1A4S0G0S2S1S10U1cS11Z645dd8A1A4S0G0S2S1S10U1dS11Z645de8A1A4S0G0S2S1S10UaM3S11Zf20d8A1A4S0G0S2S1S10UbS11Zf20daA1A4S0G0S2S1S10U9S11Ze9ac8A1A4S0G0S2S1S10G3S11Ze9af8A1A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition C18a_0 : sstate := Eval vm_compute in (match split_chain (E18g false) splits18 with Some St => St | None => E18g false end).
Definition C18a_1 : sstate := Eval vm_compute in (match split_chain (E18g true) splits18 with Some St => St | None => E18g true end).
Definition C18a (r : bool) : sstate := if r then C18a_1 else C18a_0.
Lemma split18_ok : forall r : bool, split_chain (E18g r) splits18 = Some (C18a r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition odummy18 : sobj := ltac2:(tb__ "0|1|
S1aS11Z0A1M0G0G0S4S16A1S2aA5").
Definition ob18 (St : sstate) (i : nat) : sobj := ltac2:(tb__ "0|0|
S6fS12Vi;S15VSt;A1S6dA4").

Definition o18errno_0 : sobj := Eval vm_compute in ob18 (C18a false) 19.
Definition o18errno_1 : sobj := Eval vm_compute in ob18 (C18a true) 19.
Definition o18errno (r : bool) : sobj := if r then o18errno_1 else o18errno_0.
Definition C18b_0 : sstate := Eval vm_compute in replace_obj_at (C18a false) 19 (obj_to_unknown (o18errno false)).
Definition C18b_1 : sstate := Eval vm_compute in replace_obj_at (C18a true) 19 (obj_to_unknown (o18errno true)).
Definition C18b (r : bool) : sstate := if r then C18b_1 else C18b_0.
Lemma C18b_facts : forall r : bool,
  nth_error (ss_objs (C18a r)) 19 = Some (o18errno r) /\ ob_dflt (o18errno r) = DImage
  /\ same_but_objs (C18a r) (replace_obj_at (C18a r) 19 (obj_to_unknown (o18errno r))) = true
  /\ replace_obj_at (C18a r) 19 (obj_to_unknown (o18errno r)) = C18b r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition o18ssp_0 : sobj := Eval vm_compute in ob18 (C18b false) 21.
Definition o18ssp_1 : sobj := Eval vm_compute in ob18 (C18b true) 21.
Definition o18ssp (r : bool) : sobj := if r then o18ssp_1 else o18ssp_0.
Definition es18 : list sv := ltac2:(tb__ "0|2|
S0S10S1bS9Q8M0S17P9A1M1A3S0S10S11Z0A1S0S10S1bS9G0S14S73G1S11Z10A1A3A3S0S10S1bS9G0S14S73G1S11Z18A1A3A3S0S10S1bS9G0S14S73G1S11Z20A1A3A3S0S10S1bS9G0S14S73G1S11Z28A1A3A3S0S10S1bS9G0S14S73G1S11Z30A1A3A3S0S10S14S73G1S11Z38A1A3S4S10A1A3A3A3A3A3A3A3A3").
Definition bytes18 : list cell := byte_cells 0x6445f8 es18.
Definition EV18 : sv := SAlu ALU_AND (SVar 9%positive) (SLit 18446744073709486335).
Definition o18ssp_s : sobj := ltac2:(tb__ "0|0|
S1aS11Z0A1S11Z6445f8A1S11Z644600A1S5eS1eA5").
Definition C18c_0 : sstate := Eval vm_compute in replace_obj_at (C18b false) 21 o18ssp_s.
Definition C18c_1 : sstate := Eval vm_compute in replace_obj_at (C18b true) 21 o18ssp_s.
Definition C18c (r : bool) : sstate := if r then C18c_1 else C18c_0.
Definition o18ssp_m : sobj := ltac2:(tb__ "0|1|
S1aS11Z0A1S11Z6445f8A1M0S11Z644600A1S0S16S2bG0Z8S62A3S4S16A1A3S1eA5").
Definition C18d_0 : sstate := Eval vm_compute in replace_obj_at (C18c false) 21 o18ssp_m.
Definition C18d_1 : sstate := Eval vm_compute in replace_obj_at (C18c true) 21 o18ssp_m.
Definition C18d (r : bool) : sstate := if r then C18d_1 else C18d_0.
Definition C18d'_0 : sstate := Eval vm_compute in replace_obj_at (C18d false) 21 (obj_to_unknown o18ssp_m).
Definition C18d'_1 : sstate := Eval vm_compute in replace_obj_at (C18d true) 21 (obj_to_unknown o18ssp_m).
Definition C18d' (r : bool) : sstate := if r then C18d'_1 else C18d'_0.
Lemma C18c_facts : forall r : bool,
  nth_error (ss_objs (C18b r)) 21 = Some (o18ssp r) /\ ob_base (o18ssp r) = SLit 0
  /\ ob_lo (o18ssp r) = SLit 6571512 /\ ob_hi (o18ssp r) = SLit 6571520 /\ ob_dflt (o18ssp r) = DImage
  /\ forallb (fun c : cell => existsb (cell_eqb c) bytes18) (ob_cells (o18ssp r)) = true
  /\ forallb (fun c : cell => existsb (cell_eqb c) (ob_cells (o18ssp r))) bytes18 = true
  /\ same_but_objs (C18b r) (replace_obj_at (C18b r) 21 o18ssp_s) = true
  /\ replace_obj_at (C18b r) 21 o18ssp_s = C18c r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma C18d_facts : forall r : bool,
  nth_error (ss_objs (C18c r)) 21 = Some o18ssp_s
  /\ same_but_objs (C18c r) (replace_obj_at (C18c r) 21 o18ssp_m) = true
  /\ replace_obj_at (C18c r) 21 o18ssp_m = C18d r
  /\ nth_error (ss_objs (C18d r)) 21 = Some o18ssp_m
  /\ same_but_objs (C18d r) (replace_obj_at (C18d r) 21 (obj_to_unknown o18ssp_m)) = true
  /\ replace_obj_at (C18d r) 21 (obj_to_unknown o18ssp_m) = C18d' r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition o18win_0 : sobj := Eval vm_compute in ob18 (C18d' false) 43.
Definition o18win_1 : sobj := Eval vm_compute in ob18 (C18d' true) 43.
Definition o18win (r : bool) : sobj := if r then o18win_1 else o18win_0.
Definition owin18 : sobj := ltac2:(tb__ "0|0|
S1aS17P1A1S11Nbf0A1S11Nf0A1S4S16A1S1cA5").
Definition C18e_0 : sstate := Eval vm_compute in replace_obj_at (C18d' false) 43 owin18.
Definition C18e_1 : sstate := Eval vm_compute in replace_obj_at (C18d' true) 43 owin18.
Definition C18e (r : bool) : sstate := if r then C18e_1 else C18e_0.
Lemma C18e_facts : forall r : bool,
  nth_error (ss_objs (C18d' r)) 43 = Some (o18win r) /\ ob_dflt (o18win r) = DUnknown
  /\ mkObj (ob_base (o18win r)) (ob_lo (o18win r)) (ob_hi (o18win r)) (List.filter (fun _ : cell => false) (ob_cells (o18win r))) (ob_dflt (o18win r)) = owin18
  /\ same_but_objs (C18d' r) (replace_obj_at (C18d' r) 43 owin18) = true
  /\ replace_obj_at (C18d' r) 43 owin18 = C18e r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition C18 (r : bool) : axst := mkAX (C18e r) X18 (SLit SHB).
Lemma C18_at : forall r : bool,
  ss_pc (C18e r) = MALLOC_ENTRY /\ ss_next (C18e r) = 86%positive /\ length (ss_objs (C18e r)) = 48%nat
  /\ swf (C18e r) = true /\ ss_facts (C18e r) = ss_facts (E18g r) /\ ss_regs (C18e r) = ss_regs (ax_S (E18r r)).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma C18e_facts_below : forall r : bool, forallb (sprop_below 86%positive) (ss_facts (C18e r)) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition myregs18 (r : bool) : list sv := ss_regs (C18e r).
(* The call's substitution, as recorded, over the per-flag registers (the caller's registers that are not
   arguments go to interface variables 20+r, its float registers to 60+r). *)
Definition s18 (r : bool) : wsub :=
  [(10%positive, SP18); (11%positive, nth 1 (myregs18 r) (SLit 0)); (13%positive, nth 11 (myregs18 r) (SLit 0));
   (14%positive, nth 12 (myregs18 r) (SLit 0)); (15%positive, EV18); (16%positive, AUXV18);
   (17%positive, SVar 6%positive); (18%positive, SVar 7%positive); (19%positive, SVar 8%positive);
   (52%positive, XB18); (53%positive, XL18); (54%positive, SVar 9%positive); (55%positive, SVar 10%positive)]
  ++ (List.map (fun k : nat => (Pos.of_nat (20 + k)%nat, nth k (myregs18 r) (SLit 0)))
        (List.filter (fun k : nat => negb (existsb (Nat.eqb k) [1; 2; 10; 11; 12]%nat)) (List.seq 0 32))
      ++ List.map (fun k : nat => (Pos.of_nat (60 + k)%nat, nth k (ss_fregs (C18e r)) (SLit 0))) (List.seq 0 32)).
Definition R18_0 : list sobj := Eval vm_compute in (match entails_frA (C18 false) (Pre_M false) (s18 false) with Some R => R | None => [] end).
Definition R18_1 : list sobj := Eval vm_compute in (match entails_frA (C18 true) (Pre_M true) (s18 true) with Some R => R | None => [] end).
Definition R18 (r : bool) : list sobj := if r then R18_1 else R18_0.
Lemma ent18 : forall r : bool, entails_frA (C18 r) (Pre_M r) (s18 r) = Some (R18 r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk18 : forall r : bool, call_checkPA (C18 r) (Pre_M r) (s18 r) (R18 r) [P_null0 r; P_null1 r; P_ok r] = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R18_len : forall r : bool, length (R18 r) = 34%nat.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition I18a_0 : axst := Eval vm_compute in (import_postA3 (s18 false) (Pre_M false) (P_null0 false) (C18 false) (R18 false) []).
Definition I18a_1 : axst := Eval vm_compute in (import_postA3 (s18 true) (Pre_M true) (P_null0 true) (C18 true) (R18 true) []).
Definition I18a (r : bool) : axst := if r then I18a_1 else I18a_0.
Definition I18b_0 : axst := Eval vm_compute in (import_postA3 (s18 false) (Pre_M false) (P_null1 false) (C18 false) (R18 false) []).
Definition I18b_1 : axst := Eval vm_compute in (import_postA3 (s18 true) (Pre_M true) (P_null1 true) (C18 true) (R18 true) []).
Definition I18b (r : bool) : axst := if r then I18b_1 else I18b_0.
Definition I18c_0 : axst := Eval vm_compute in (import_postA3 (s18 false) (Pre_M false) (P_ok false) (C18 false) (R18 false) []).
Definition I18c_1 : axst := Eval vm_compute in (import_postA3 (s18 true) (Pre_M true) (P_ok true) (C18 true) (R18 true) []).
Definition I18c (r : bool) : axst := if r then I18c_1 else I18c_0.
Lemma I18_eq : forall r : bool,
  import_postA3 (s18 r) (Pre_M r) (P_null0 r) (C18 r) (R18 r) [] = I18a r
  /\ import_postA3 (s18 r) (Pre_M r) (P_null1 r) (C18 r) (R18 r) [] = I18b r
  /\ import_postA3 (s18 r) (Pre_M r) (P_ok r) (C18 r) (R18 r) [] = I18c r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition refact18 (r : bool) (A : axst) : axst := ax_with_facts A (ss_facts (ax_S A) ++ ss_facts (C18e r)).
Definition I18af_0 : axst := Eval vm_compute in refact18 false (I18a false).
Definition I18af_1 : axst := Eval vm_compute in refact18 true (I18a true).
Definition I18af (r : bool) : axst := if r then I18af_1 else I18af_0.
Definition I18bf_0 : axst := Eval vm_compute in refact18 false (I18b false).
Definition I18bf_1 : axst := Eval vm_compute in refact18 true (I18b true).
Definition I18bf (r : bool) : axst := if r then I18bf_1 else I18bf_0.
Definition I18cf_0 : axst := Eval vm_compute in refact18 false (I18c false).
Definition I18cf_1 : axst := Eval vm_compute in refact18 true (I18c true).
Definition I18cf (r : bool) : axst := if r then I18cf_1 else I18cf_0.
Lemma I18f_eq : forall r : bool,
  refact18 r (I18a r) = I18af r /\ refact18 r (I18b r) = I18bf r /\ refact18 r (I18c r) = I18cf r.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition JPC18 : Z := 0x657dc.
Definition L18a_0 : axst := Eval vm_compute in leaf1 (I18af false) (sym_runA segsA 3000%nat [JPC18] (I18af false) true).
Definition L18a_1 : axst := Eval vm_compute in leaf1 (I18af true) (sym_runA segsA 3000%nat [JPC18] (I18af true) true).
Definition L18a (r : bool) : axst := if r then L18a_1 else L18a_0.
Definition L18b_0 : axst := Eval vm_compute in leaf1 (I18bf false) (sym_runA segsA 3000%nat [JPC18] (I18bf false) true).
Definition L18b_1 : axst := Eval vm_compute in leaf1 (I18bf true) (sym_runA segsA 3000%nat [JPC18] (I18bf true) true).
Definition L18b (r : bool) : axst := if r then L18b_1 else L18b_0.
Definition L18c_0 : axst := Eval vm_compute in leaf1 (I18cf false) (sym_runA segsA 3000%nat [JPC18] (I18cf false) true).
Definition L18c_1 : axst := Eval vm_compute in leaf1 (I18cf true) (sym_runA segsA 3000%nat [JPC18] (I18cf true) true).
Definition L18c (r : bool) : axst := if r then L18c_1 else L18c_0.
Lemma run18a : forall r : bool, sym_runA segsA 3000%nat [JPC18] (I18af r) true = Some [mkLeafA (L18a r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run18b : forall r : bool, sym_runA segsA 3000%nat [JPC18] (I18bf r) true = Some [mkLeafA (L18b r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run18c : forall r : bool, sym_runA segsA 3000%nat [JPC18] (I18cf r) true = Some [mkLeafA (L18c r) RsCut].
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition T18b_0 : sstate := Eval vm_compute in move_obj_last (ax_S (L18b false)) 14.
Definition T18b_1 : sstate := Eval vm_compute in move_obj_last (ax_S (L18b true)) 14.
Definition T18b (r : bool) : sstate := if r then T18b_1 else T18b_0.
Definition U18b_0 : axst := Eval vm_compute in ax_setS (L18b false) (set_objs (T18b false) (firstn 48 (ss_objs (T18b false)))).
Definition U18b_1 : axst := Eval vm_compute in ax_setS (L18b true) (set_objs (T18b true) (firstn 48 (ss_objs (T18b true)))).
Definition U18b (r : bool) : axst := if r then U18b_1 else U18b_0.
Definition oarea18b_0 : sobj := Eval vm_compute in nth 48 (ss_objs (T18b false)) odummy18.
Definition oarea18b_1 : sobj := Eval vm_compute in nth 48 (ss_objs (T18b true)) odummy18.
Definition oarea18b (r : bool) : sobj := if r then oarea18b_1 else oarea18b_0.
Lemma T18b_facts : forall r : bool,
  move_obj_last (ax_S (L18b r)) 14 = T18b r /\ same_but_objs (ax_S (L18b r)) (T18b r) = true
  /\ length (ss_objs (ax_S (L18b r))) = 49%nat /\ ss_objs (T18b r) = ss_objs (ax_S (U18b r)) ++ [oarea18b r]
  /\ ax_setS (L18b r) (set_objs (T18b r) (ss_objs (ax_S (U18b r)))) = U18b r
  /\ oarea18b r = mkObj (SAlu ALU_ADD (SVar 148%positive) (SLit 4096)) (SLit 0) (SLit 4096) [] DUnknown.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T18c1_0 : sstate := Eval vm_compute in move_obj_last (ax_S (L18c false)) 14.
Definition T18c1_1 : sstate := Eval vm_compute in move_obj_last (ax_S (L18c true)) 14.
Definition T18c1 (r : bool) : sstate := if r then T18c1_1 else T18c1_0.
Definition T18c_0 : sstate := Eval vm_compute in move_obj_last (T18c1 false) 14.
Definition T18c_1 : sstate := Eval vm_compute in move_obj_last (T18c1 true) 14.
Definition T18c (r : bool) : sstate := if r then T18c_1 else T18c_0.
Definition U18c_0 : axst := Eval vm_compute in ax_setS (L18c false) (set_objs (T18c false) (firstn 48 (ss_objs (T18c false)))).
Definition U18c_1 : axst := Eval vm_compute in ax_setS (L18c true) (set_objs (T18c true) (firstn 48 (ss_objs (T18c true)))).
Definition U18c (r : bool) : axst := if r then U18c_1 else U18c_0.
Definition oarea18c_0 : sobj := Eval vm_compute in nth 48 (ss_objs (T18c false)) odummy18.
Definition oarea18c_1 : sobj := Eval vm_compute in nth 48 (ss_objs (T18c true)) odummy18.
Definition oarea18c (r : bool) : sobj := if r then oarea18c_1 else oarea18c_0.
Definition ogrp18c_0 : sobj := Eval vm_compute in nth 49 (ss_objs (T18c false)) odummy18.
Definition ogrp18c_1 : sobj := Eval vm_compute in nth 49 (ss_objs (T18c true)) odummy18.
Definition ogrp18c (r : bool) : sobj := if r then ogrp18c_1 else ogrp18c_0.
Lemma T18c_facts : forall r : bool,
  move_obj_last (ax_S (L18c r)) 14 = T18c1 r /\ same_but_objs (ax_S (L18c r)) (T18c1 r) = true
  /\ length (ss_objs (ax_S (L18c r))) = 50%nat /\ move_obj_last (T18c1 r) 14 = T18c r
  /\ same_but_objs (T18c1 r) (T18c r) = true /\ length (ss_objs (T18c1 r)) = 50%nat
  /\ ss_objs (T18c r) = ss_objs (ax_S (U18c r)) ++ [oarea18c r; ogrp18c r]
  /\ ax_setS (L18c r) (set_objs (T18c r) (ss_objs (ax_S (U18c r)))) = U18c r
  /\ oarea18c r = mkObj (SAlu ALU_ADD (SVar 148%positive) (SLit 4096)) (SLit 0) (SLit 4096) [] DUnknown
  /\ ob_base (ogrp18c r) = SVar 149%positive /\ ob_lo (ogrp18c r) = SLit 0 /\ ob_hi (ogrp18c r) = SLit 4096.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition ounk18 (o : sobj) : sobj := ltac2:(tb__ "0|0|
S1aS1fVo;A1S21Vo;A1S20Vo;A1S4S16A1S1cA5").
Definition J18objs2_of (L : axst) : list sobj :=
  (let l := ss_objs (ax_S L) in
   let o i := nth i l odummy18 in
   [o 14; o 12; o 13; o 15; o 16; o 8; o 17; o 9; o 18;
    o 19; o 11; o 20; o 21; o 10; o 22; o 23; o 24; o 25;
    o 26; o 6; o 27; o 5; o 28; o 2; o 29; o 3; o 30; o 4; o 31; o 1; o 32; ounk18 (o 33); o 34; o 7; o 35;
    o 36; o 37; o 38; o 39; o 40; o 41; o 42;
    o 43; owin18; o 44;
    o 45; o 46; o 47]%nat).
Definition J18objs2_0 : list sobj := Eval vm_compute in J18objs2_of (L18a false).
Definition J18objs2_1 : list sobj := Eval vm_compute in J18objs2_of (L18a true).
Definition J18objs2 (r : bool) : list sobj := if r then J18objs2_1 else J18objs2_0.
Definition J18S_of (r : bool) : sstate :=
  (let St := ax_S (L18a r) in
   mkSS JPC18 (list_set (list_set (list_set (ss_regs St) 10 (SVar 156%positive)) 11 (SVar 157%positive)) 13 (SVar 158%positive))
        (ss_fregs St) (ss_fcsr St) (ss_resv St) (J18objs2 r) (ss_facts (C18e r)) 159%positive (ss_lenient St)).
Definition J18S_0 : sstate := Eval vm_compute in J18S_of false.
Definition J18S_1 : sstate := Eval vm_compute in J18S_of true.
Definition J18S (r : bool) : sstate := if r then J18S_1 else J18S_0.
Definition J18 (r : bool) : axst := mkAX (J18S r) X18 (SLit SHB).
Definition sJ18 (L : axst) : wsub := ltac2:(tb__ "0|3|
S0SaS2eS10A2M0S2S2eS10P9cS6fS10UaS27S32VL;A1A1M1S11Z0A1M2A4A4S0G0S2S2eS10P9dS6fS10UbG1G2A4A4S0G0S2S2eS10P9eS6fS10UdG1G2A4A4S4G0A1A3A3A3").
Lemma entJ18a : forall r : bool, entailsA (L18a r) (J18 r) (sJ18 (L18a r)) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma entJ18b : forall r : bool, entailsA (U18b r) (J18 r) (sJ18 (U18b r)) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma entJ18c : forall r : bool, entailsA (U18c r) (J18 r) (sJ18 (U18c r)) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sJ18_id : forall r : bool,
  wsub_id_below (sJ18 (L18a r)) 156%positive = true /\ wsub_id_below (sJ18 (U18b r)) 156%positive = true
  /\ wsub_id_below (sJ18 (U18c r)) 156%positive = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma J18_at : forall r : bool,
  ss_pc (J18S r) = JPC18 /\ ss_next (J18S r) = 159%positive /\ length (ss_objs (J18S r)) = 48%nat
  /\ swf (J18S r) = true /\ axwf (J18 r) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition K18a_0 : sstate := Eval vm_compute in (match merge_objs_at (J18S false) 42 with Some St => St | None => J18S false end).
Definition K18a_1 : sstate := Eval vm_compute in (match merge_objs_at (J18S true) 42 with Some St => St | None => J18S true end).
Definition K18a (r : bool) : sstate := if r then K18a_1 else K18a_0.
Definition K18Sr_0 : sstate := Eval vm_compute in (match merge_objs_at (K18a false) 42 with Some St => St | None => K18a false end).
Definition K18Sr_1 : sstate := Eval vm_compute in (match merge_objs_at (K18a true) 42 with Some St => St | None => K18a true end).
Definition K18Sr (r : bool) : sstate := if r then K18Sr_1 else K18Sr_0.
Lemma K18_eq : forall r : bool,
  merge_objs_at (J18S r) 42 = Some (K18a r) /\ merge_objs_at (K18a r) 42 = Some (K18Sr r).
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition K18r (r : bool) : axst := mkAX (K18Sr r) X18 (SLit SHB).
Lemma K18r_at : forall r : bool,
  ss_pc (K18Sr r) = JPC18 /\ ss_next (K18Sr r) = 159%positive /\ length (ss_objs (K18Sr r)) = 46%nat /\ swf (K18Sr r) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

(* The join (LPS 727298f3): one exit for both CONFIG_RSEQ values, after malloc(40) has walked the auxv.
   The auxv object (based at [AUXV18], from 0) is [ob_hi (O_auxv r)] bytes long: 432, or 464 with
   CONFIG_RSEQ.  For [r = true] it is split at the [r = false] length [MID18], its tail moved last and
   dropped ([K18S1]); then [K18S] keeps, object by object, what [K18Sr false] and [K18S1] share (an object
   that differs keeps the cells both hold, default unknown) and the facts both hold.  Malloc's posts
   already forgot the auxv cells (A/e9.v [O_auxvF]).  A/StartRegen3.v proves [K18] a weakening of each
   [K18r r]; the entailments below check it. *)
Fixpoint idx_of (p : sobj -> bool) (l : list sobj) (i : nat) : nat :=
  match l with
  | [] => i
  | o :: l' => if p o then i else idx_of p l' (Datatypes.S i)
  end.
Definition is_aux18 (o : sobj) : bool := sv_eqb (ob_base o) AUXV18 && sv_eqb (ob_lo o) (SLit 0).
Definition is_rand18 (o : sobj) : bool := sv_eqb (ob_base o) (SVar 6%positive) && sv_eqb (ob_lo o) (SLit 0).
Definition aux_at (St : sstate) : nat := idx_of is_aux18 (ss_objs St) 0.
Definition rand_at (St : sstate) : nat := idx_of is_rand18 (ss_objs St) 0.
Definition MID18 : sv := ob_hi (O_auxv false).
Definition K18S1s : sstate := Eval vm_compute in
  (match split_obj_at (K18Sr true) (aux_at (K18Sr true)) MID18 with Some St => St | None => K18Sr true end).
Definition K18S1m : sstate := Eval vm_compute in move_obj_last K18S1s (Datatypes.S (aux_at (K18Sr true))).
Definition otail18 : sobj := Eval vm_compute in List.last (ss_objs K18S1m) odummy18.
Definition K18S1 : sstate := Eval vm_compute in set_objs K18S1m (List.removelast (ss_objs K18S1m)).
Lemma K18S1_facts :
  split_obj_at (K18Sr true) (aux_at (K18Sr true)) MID18 = Some K18S1s
  /\ Nat.ltb (Datatypes.S (aux_at (K18Sr true))) (length (ss_objs K18S1s)) = true
  /\ same_but_objs K18S1s (move_obj_last K18S1s (Datatypes.S (aux_at (K18Sr true)))) = true
  /\ move_obj_last K18S1s (Datatypes.S (aux_at (K18Sr true))) = K18S1m
  /\ ss_objs K18S1m = ss_objs K18S1 ++ [otail18]
  /\ set_objs K18S1m (ss_objs K18S1) = K18S1
  /\ ob_base otail18 = AUXV18 /\ ob_lo otail18 = MID18 /\ ob_hi otail18 = ob_hi (O_auxv true).
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
(* What the tail's range lemma reads in [K18Sr true]: the auxv object (whole, before the split) and the
   random bytes' object, and the fact that puts the auxv above the shadow band. *)
Lemma K18_auxrand :
  nth_error (ss_objs (K18Sr true)) (aux_at (K18Sr true))
    = Some (mkObj AUXV18 (SLit 0) (ob_hi (O_auxv true)) [] DUnknown)
  /\ ob_base (nth (rand_at (K18Sr true)) (ss_objs (K18Sr true)) odummy18) = SVar 6%positive
  /\ ob_lo (nth (rand_at (K18Sr true)) (ss_objs (K18Sr true)) odummy18) = SLit 0
  /\ ob_hi (nth (rand_at (K18Sr true)) (ss_objs (K18Sr true)) odummy18) = SLit 16
  /\ Nat.ltb (rand_at (K18Sr true)) (length (ss_objs (K18Sr true))) = true
  /\ Nat.eqb (rand_at (K18Sr true)) (aux_at (K18Sr true)) = false
  /\ ob_hi (O_auxv false) = SLit 432 /\ ob_hi (O_auxv true) = SLit 464
  /\ existsb (sprop_eqb (SPUle (SLit 140735340871680) AUXV18)) (ss_facts (K18Sr true)) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition join_cells18 (a b : list cell) : list cell := List.filter (fun c => existsb (cell_eqb c) b) a.
Definition join_obj18 (o p : sobj) : sobj :=
  if OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.Relaunch.rl_obj_eqb o p then o
  else mkObj (ob_base o) (ob_lo o) (ob_hi o) (join_cells18 (ob_cells o) (ob_cells p)) DUnknown.
Fixpoint join_objs18 (l k : list sobj) : list sobj :=
  match l, k with
  | o :: l', p :: k' => join_obj18 o p :: join_objs18 l' k'
  | _, _ => l
  end.
Definition join_st18 (A B : sstate) : sstate :=
  mkSS (ss_pc A) (ss_regs A) (ss_fregs A) (ss_fcsr A) (ss_resv A) (join_objs18 (ss_objs A) (ss_objs B))
       (List.filter (fun p => existsb (sprop_eqb p) (ss_facts B)) (ss_facts A))
       (Pos.max (ss_next A) (ss_next B)) (ss_lenient A).
Definition K18S : sstate := Eval vm_compute in join_st18 (K18Sr false) K18S1.
Definition K18 : axst := mkAX K18S X18 (SLit SHB).
Lemma K18_join_ent :
  entailsA (K18r false) K18 [] = true /\ entailsA (mkAX K18S1 X18 (SLit SHB)) K18 [] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma K18_at : ss_pc K18S = JPC18 /\ ss_next K18S = 159%positive /\ length (ss_objs K18S) = 46%nat /\ swf K18S = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
