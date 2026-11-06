(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  Hoare RefExitBase RefStdioDefs RefExit RefPrintfBufBase LibTail StepTac WalkTac Spec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe1Z04cons03nil03nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~kb7scripts04boolkb3SCRkb4exprkb6kentrykb4EVarkb5KWordkb2SAkb4ELitkb6KRangehe4Npos35stdpp9bitvectorbdefinitionstb2bv3h5LinuxProcessSemantics5Riscv7Preludevd5bvmap03app69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~hj09junk_valskb3envhj08blobs_evkb3Env69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~hp07vals_ev37Corelib4Init5Logicht42eq06lengthht43and37Corelib4Init3Nathvd3sub37Corelib4Init5Peanoih62leih62lt69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ij64getr79OSSVerify6Proofsaboost_jsonafuzz_parse3libbRefMainExit8MainExit~~~~~~in93ENVin96x_valskb2ev46Stdlib6ZArith6BinInt1Zit66of_nattb7Z_to_bv01S37Corelib5Lists7ListDefjg53nth06optionht41Iin9amain_frame69OSSVerify6Proofsaboost_jsonafuzz_parse3libbRefMainExit~~~~~~jje4x_sr79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~jo47regs_oktb2BVtb4BvWfjje4x_knjo47know_ok69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~jv3floaded_segments3h5LinuxProcessSemanticsfLinuxProcessSem3Runkjc5mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statekn14m_fsij64mkstij67seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefStdioDefs~~~~~~kra8exit_pre69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~lg5dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~lkd8realizeslkd6t_emitlkd6t_exit69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~lq81Wit63addtb6bv_andtbbbv_unsignedkn15Model" s.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition STOPSX : ltac2:(zQ "20!h8!j7@1$0$1") := ltac2:(zQ "30!j7!jb!k1@3$1$0+tqnrc@1$2$0").
Definition FUELX : nat := 100.
Definition scr0 : ltac2:(zQ "10!oa$0") := ltac2:(zQ "40!k1!p4!pa!q0@3$2@1$0$1@1$0$3@1$0$1").

(* [comment removed for export] *)
Definition x_sr : list expr :=
  Eval cbv in (map (fun i => match i with 0 => ELit 0%Z | 2 => EVar 0 | _ => EVar (9 + i) end)%nat (seq 0 32)).

Definition x_kn : ltac2:(zQ "20!h8!q7@1$0$1") := ltac2:(zQ "80!r0!q7!jb!r7!rf!k1!s4!sb@3$2$1@3$7@1$0N0+hgg0+nvvvvvvvvvvf@3$2$1@3$3@2$4@1$0N0+8N8@1$0N1@3$2$1@3$3@2$4@1$0N0+h0N8@1$0N2@3$2$1@3$3@2$4@1$0N0+h8N8@1$0N3@3$2$1@3$3@2$4@1$0N0+i0N8@1$0N4@3$2$1@3$3@2$4@1$0N0+i8N8@1$0N5@3$2$1@3$3@2$4@1$0N0+j0N8@1$0N6@3$2$1@3$3@2$4@1$0N0+j8N8@1$0N7@3$2$1@3$3@2$4@1$0N0+k0N8@1$0N8@3$2$1@3$3@2$4@1$0N0+k8N8@1$6+tqgsc@1$5$1").

Definition x_r := Eval vm_compute in (sym_exec RSEGS FUELX true STOPSX scr0 (SS 0x475cc x_sr [] x_kn 41) []).
Definition x_c := Eval vm_compute in (carry (s_log (fst (fst x_r))) x_kn []).
Definition x_srF : list expr := Eval vm_compute in (s_regs (fst (fst x_r))).

End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MainExit.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable model : ltac2:(zQ "10!mg2$0").

  (* [comment removed for export] *)
  Record main_frame (mem : word -> option byte) (sp : word) (slots : list word) : Prop := MF {
    mf_len : length slots = 8%nat;
    mf_slots : forall i, (i < 8)%nat ->
        rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp + 8 + 8 * Z.of_nat i)) 8 = Some (word_to_le_bytes 8 (nth i slots (Z_to_bv 64 0)));
    mf_ra : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp + 72)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xda0cc));
    mf_lo : (0x1000 <= bv_unsigned sp)%Z;
    mf_hi : (bv_unsigned sp <= 0x7fffffffffff)%Z }.

  Definition x_vals : ltac2:(zQ "40!t4!v8!h8!hi3>4regs@2$3@1$0#5@1$1@1$0#k0>2sp@1$1@1$0#k0>5slots@1$2@1$1@1$0#k0@1$2@1$1@1$0#k0") := ltac2:(zQ "80!t4!v8!hib!jb!h8!k1!hi3!hmb\4regs@2$6@1$0#5@1$1@1$0#k0\2sp@1$1@1$0#k0\5slots@1$4@1$1@1$0#k0@3$2@1$1@1$0#k0@3$3@1$1@1$0#k0^2@1$5@1$1@1$0#k0@3$2@1$1@1$0#k0^1@1$7^3").

  Definition ENV : ltac2:(zQ "40!h8!t4!hn8!v8>4vals@1$0@1$3@1$1#k0$2") := ltac2:(zQ "70!h8!t4!v8!k1!hne!hoa!hs9\4vals@1$0@1$2@1$1#k0@2$5@1$6^1@1$4@1$3@1$0@1$2@1$1#8").

  Lemma x_ev_junk : ltac2:(zQ "h10!t4!v8!k6!hu8!hue!h8!hv6!igf!iia!ij0!hi3!in1!is0!is7!it1!iue!iv8>4regs@2$a@1$0#5@1$1@1$0#k0>2sp@1$1@1$0#k0>5slots@1$5@1$1@1$0#k0>1i$2>0@3$3$2@2$4@1$1@1$0#k0^2N8>0@2$6@2$8N9^2@2$9^2Ni9@3$3@1$1@1$0#k0@2$e@1$c@3$d^6^5^4^3@2$b^6@2$h0@1$0#5@1$f@2$7^3N9").
  Proof.
    intros regs sp slots i HL Hi. unfold ENV, x_vals. cbn [ev]. unfold vals_ev.
    rewrite app_assoc.
    replace i with (length ([sp] ++ slots) + (i - 9))%nat at 1 by (rewrite length_app, HL; cbn; lia).
    rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
  Qed.

  Lemma x_ev_slot : ltac2:(zQ "e0!t4!v8!k6!hu8!jg2!hue!h8!ij0!jhc!hi3!is0!is7!it1!iv8>4regs@2$9@1$0#5@1$1@1$0#k0>2sp@1$1@1$0#k0>5slots@1$6@1$1@1$0#k0>1i$2>0@3$3$2@2$5@1$1@1$0#k0^2N8>0@2$7^2N8@3$3@1$1@1$0#k0@2$c@1$a@3$b^6^5^4@1$4^3@4$8@1$1@1$0#k0^3^4@2$d@1$0#k0Z").
  Proof.
    intros regs sp slots i HL Hi. unfold ENV, x_vals. cbn [ev]. unfold vals_ev.
    change ([sp] ++ slots ++ junk_vals regs) with (sp :: (slots ++ junk_vals regs)). cbn [nth].
    rewrite app_nth1 by (rewrite HL; exact Hi). apply nth_indep. rewrite HL; exact Hi.
  Qed.

  Lemma x_regs_ok : ltac2:(zQ "f0!t4!v8!h8!ji3!jib!hu8!hi3!in1!is0!jj0!is7!jnc!js9!jt4!jt9>4regs@2$6@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>2sp@1$1@1$0#k0>5slots@1$2@1$1@1$0#k0>0@3$5@1$1@1$0#k0@2$7^4@3$d@1$0#5+2Kv$4@2$e@1$0#5+2^2>0@3$9^4^3^2@3$c@1$8@3$a^6^4^3$b^6").
  Proof.
    intros regs mem sp slots Hsp MFH. destruct MFH as [HL _ _ _ _].
    apply regs_ok_by_idx. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth x_sr allregs32 edenot].
    1: apply getr_zero.
    2: cbn [ev ENV]; exact Hsp.
    all: rewrite x_ev_junk by (exact HL || lia); f_equal; apply bv_eq; reflexivity.
  Qed.

  Lemma x_know_ok : ltac2:(zQ "b0!t4!v8!h8!ji3!hi3!is0!jj0!is7!ju0!ju8!ki9>4regs@2$4@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>2sp@1$1@1$0#k0>5slots@1$2@1$1@1$0#k0>0@3$6^3^2^1@4$9$a@1$5@3$7^5^3^2^4$8").
  Proof.
    intros regs mem sp slots MFH. destruct MFH as [HL HS HRA Hlo Hhi]. pose proof (u64_range sp) as Hsp.
    assert (E0 : ev (ENV (x_vals regs sp slots)) 0 = sp) by reflexivity.
    unfold x_kn. repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply krange_intro. cbn [edenot]. rewrite E0. lia.
    - eapply (kword_intro RSEGS _ mem (EVar 0) sp); [exact E0 | cbn [edenot]; apply (x_ev_slot regs sp slots 0 HL); lia | lia | lia | lia | lia
        | replace (bv_unsigned sp + 8)%Z with (bv_unsigned sp + 8 + 8 * Z.of_nat 0)%Z by lia; apply HS; lia].
    - eapply (kword_intro RSEGS _ mem (EVar 0) sp); [exact E0 | cbn [edenot]; apply (x_ev_slot regs sp slots 1 HL); lia | lia | lia | lia | lia
        | replace (bv_unsigned sp + 16)%Z with (bv_unsigned sp + 8 + 8 * Z.of_nat 1)%Z by lia; apply HS; lia].
    - eapply (kword_intro RSEGS _ mem (EVar 0) sp); [exact E0 | cbn [edenot]; apply (x_ev_slot regs sp slots 2 HL); lia | lia | lia | lia | lia
        | replace (bv_unsigned sp + 24)%Z with (bv_unsigned sp + 8 + 8 * Z.of_nat 2)%Z by lia; apply HS; lia].
    - eapply (kword_intro RSEGS _ mem (EVar 0) sp); [exact E0 | cbn [edenot]; apply (x_ev_slot regs sp slots 3 HL); lia | lia | lia | lia | lia
        | replace (bv_unsigned sp + 32)%Z with (bv_unsigned sp + 8 + 8 * Z.of_nat 3)%Z by lia; apply HS; lia].
    - eapply (kword_intro RSEGS _ mem (EVar 0) sp); [exact E0 | cbn [edenot]; apply (x_ev_slot regs sp slots 4 HL); lia | lia | lia | lia | lia
        | replace (bv_unsigned sp + 40)%Z with (bv_unsigned sp + 8 + 8 * Z.of_nat 4)%Z by lia; apply HS; lia].
    - eapply (kword_intro RSEGS _ mem (EVar 0) sp); [exact E0 | cbn [edenot]; apply (x_ev_slot regs sp slots 5 HL); lia | lia | lia | lia | lia
        | replace (bv_unsigned sp + 48)%Z with (bv_unsigned sp + 8 + 8 * Z.of_nat 5)%Z by lia; apply HS; lia].
    - eapply (kword_intro RSEGS _ mem (EVar 0) sp); [exact E0 | cbn [edenot]; apply (x_ev_slot regs sp slots 6 HL); lia | lia | lia | lia | lia
        | replace (bv_unsigned sp + 56)%Z with (bv_unsigned sp + 8 + 8 * Z.of_nat 6)%Z by lia; apply HS; lia].
    - eapply (kword_intro RSEGS _ mem (EVar 0) sp); [exact E0 | cbn [edenot]; apply (x_ev_slot regs sp slots 7 HL); lia | lia | lia | lia | lia
        | replace (bv_unsigned sp + 64)%Z with (bv_unsigned sp + 8 + 8 * Z.of_nat 7)%Z by lia; apply HS; lia].
    - eapply (kword_intro RSEGS _ mem (EVar 0) sp); [exact E0 | reflexivity | lia | lia | lia | lia | exact HRA].
  Qed.

  (* [comment removed for export] *)
  Theorem main_return_exit : ltac2:(zQ "ha2!t4!v8!jib!in1!jt4!jt9!hu8!iv8!h8!hi3!ki9!ji3!km8!kpf!kq7!kqf!jj0!kv9!ljc!lo8!lp4!lpe!ltf!lu4!lub!lv4&@3$4@1$0#5+2Kv$2@2$5@1$0#5+2&@3$4@1$0#5+4Kv$2@2$5@1$0#5+4>4regs@2$9@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$b@1$1@1$0#8>2sp@1$1@1$0#k0>6status@1$1@1$0#k0>5slots@1$8@1$1@1$0#k0>7pending@1$8@1$1@1$0#8>0@3$6@1$1@1$0#k0@2$3^6~0^4>0@3$6@1$1@1$0#k0@2$3^7@3$4@1$0#5+8Kv$2@2$5@1$0#5+8^4>0@3$h0^7^6^4>0>5regs'@2$9@1$0#5@1$1@1$0#k0>0@3$6@1$1@1$0#k0@2$3^1~0@2$7@1$0#k0@2$h7@2$h9@1$0#k0^8+l0>0@3$6@1$1@1$0#k0@2$3^2~1@2$3^b~1>0@3$6@1$1@1$0#k0@2$3^3@3$4@1$0#5+aKv$2@2$5@1$0#5+a^9@5$h1^4^c?5model^a^8@4$h3$a$h2@2$c@5$e?2fx^a@2$7@1$0#k0+knlsc^9@1$f$a?5model@2$h4@2$h6+1^5@2$h5@3$h8@1$0#k0^7@2$7@1$0#k0+vf@1$d?5model").
  Proof.
    intros regs mem sp status slots pending Hsp Hs0 MFH HPRE.
    pose proof (x_regs_ok regs mem sp slots Hsp MFH) as HR.
    pose proof (x_know_ok regs mem sp slots MFH) as HK.
    destruct MFH as [HL _ _ Hlo Hhi]. pose proof (u64_range sp) as Hspr.
    (* [comment removed for export] *)
    ndestruct (HPRE (regupd (regupd (regupd regs 2 (Z_to_bv 64 (bv_unsigned sp + 80))) 4 (getr regs 4)) 10 status))
      as (sp' & tp' & tid & wp2 & rp2 & _ & Hh & Hlazy & _); [gres; reflexivity | gres; reflexivity | gres; reflexivity |].
    eapply (rz_run RSEGS FUELX STOPSX scr0 0x475cc x_sr x_kn 41 (fst (fst x_r)) (snd (fst x_r)) (snd x_r)
              (fst (fst x_c)) (snd (fst x_c)) (snd x_c) (ENV (x_vals regs sp slots)) mem (seg_rom RSEGS) regs model);
      [ vm_cast_no_check (@eq_refl _ x_r) | vm_cast_no_check (@eq_refl _ x_c)
      | exact HR | exact HK | apply Forall_nil | apply Forall_nil | exact Hh | exact Hlazy | ].
    clear HR HK. intros R' M' HR HK EQM.
    change (s_pc (fst (fst x_r))) with 0xda7bc%Z. change (s_regs (fst (fst x_r))) with x_srF in HR.
    assert (EM : M' = mem) by (rewrite EQM; reflexivity). rewrite EM. clear EQM EM.
    apply ref_exit_Z. apply HPRE.
    - regv HR (2 : reg). cbn [edenot ev ENV]. rewrite alu_add, vadd_wZ. reflexivity.
    - regv HR (4 : reg). cbn [edenot]. rewrite (x_ev_junk regs sp slots 13 HL) by lia. f_equal; apply bv_eq; reflexivity.
    - regv HR (10 : reg). cbn [edenot]. rewrite (x_ev_junk regs sp slots 17 HL) by lia. rewrite <- Hs0. f_equal; apply bv_eq; reflexivity.
  Qed.
End MainExit.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
