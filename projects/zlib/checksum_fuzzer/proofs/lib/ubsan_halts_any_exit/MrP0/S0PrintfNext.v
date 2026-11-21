(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import
  WsegFast PropExec CatExec CatSim SeqExec StoreOk Frame StreamSim SymExec SymExec2 SymExec2Sound SymRun SymDrive
  RefMemcpyLib AgentLib.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import SymAux RefPrintfLib LibTail.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require S0PrintfBufBase Spec.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.MrP0 Require Import S0SoDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Src_zlib_checksum_fuzzer_repro.M.loaded_segments.


Definition PF_FR : Z := 1200.


Record pfH2 {RCa1 : RunCtx}  (mem : word -> option byte) (sp : word) (w can : Z) : Prop := PFH2 {
  Psp16  : bv_unsigned sp mod 16 = 0;
  PspLo  : 4294967296 + 1200 <= bv_unsigned sp;
  PspHi  : bv_unsigned sp <= 0x7fffffffffff;
  Pstk   : stk_ok (run_segments RSEGS rc_inp rc_sp rc_mb) mem sp PF_FR;
  Pimg1  : forall i, 0x10000 <= i < 0x1e780 -> mem (Z_to_bv 64 i) = None;
  Pimg2  : forall i, 0x1e788 <= i < 0x1f000 -> mem (Z_to_bv 64 i) = None;
  Pgot   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1e780) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x4fd70));
  Pflags : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1f8b0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  Pwend  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1f8d0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x505d8));
  Pwpos  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1f8d8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 w));
  Pw     : 0x501d8 <= w <= 0x505d6;
  Pbsz   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1f910) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
  Plock  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1f93c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  Plbf   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1f940) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  Pcan   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fd70) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
  Pcan64 : 0 <= can < 2 ^ 64 }.
Arguments PFH2 {RCa1}.


Definition pf_vals (regs : bvmap 5 word) (sp : word) (w can : Z) : list word :=
  [sp; Z_to_bv 64 w; Z_to_bv 64 can] ++ junk_vals regs.

Definition pfE (regs : bvmap 5 word) (sp : word) (w can : Z) : env :=
  Env (vals_ev (pf_vals regs sp w can)) (blobs_ev []).

Definition pf_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0 | 1 => ELit 0x140fc | 2 => EVar 0 | 11 => ELit 0
                          | _ => EVar (3 + i) end)%nat (seq 0 32)).

Definition pf_kn : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) (4294967296 + 1200) 0x7fffffffffff;
   KWr (SA (EVar 0) (-1200)) 1200;
   KImg 0x10000 0x1e780; KImg 0x1e788 0x1f000;
   KWord (SA (ELit 0) 0x1e780) 8 (ELit 0x4fd70);
   KWord (SA (ELit 0) 0x1f8b0) 4 (ELit 5);
   KWord (SA (ELit 0) 0x1f8d0) 8 (ELit 0x505d8);
   KWord (SA (ELit 0) 0x1f8d8) 8 (EVar 1);
   KRange (EVar 1) 0x501d8 0x505d6;
   KWord (SA (ELit 0) 0x1f910) 8 (ELit 1024);
   KWord (SA (ELit 0) 0x1f93c) 4 (ELit 4294967295);
   KWord (SA (ELit 0) 0x1f940) 4 (ELit 4294967295);
   KWord (SA (ELit 0) 0x4fd70) 8 (EVar 2);
   KWr (SA (ELit 0) 0x1f000) 0x32000;
   KWr (SA (EVar 1) 0) 2].


Section Entry.
Context {RCa1 : RunCtx}.
  Variables (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (w can : Z).
  Hypothesis PH : pfH2 mem sp w can.
  Hypothesis R1 : getr regs 1 = Z_to_bv 64 0x140fc.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 0.

  Let E := pfE regs sp w can.

  Lemma ev_junk : forall i, (3 <= i < 35)%nat -> ev E i = getr regs (Z_to_bv 5 (Z.of_nat (i - 3))).
  Proof.
    intros i Hi. unfold E, pfE, pf_vals. cbn [ev]. unfold vals_ev.
    replace i with (length [sp; Z_to_bv 64 w; Z_to_bv 64 can] + (i - 3))%nat at 1 by (cbn; lia).
    rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
  Qed.

  Lemma ev0 : ev E 0 = sp. Proof. reflexivity. Qed.
  Lemma ev1 : ev E 1 = Z_to_bv 64 w. Proof. reflexivity. Qed.
  Lemma ev2 : ev E 2 = Z_to_bv 64 can. Proof. reflexivity. Qed.

  Lemma pf_regs_ok : regs_ok E pf_sr regs.
  Proof.
    apply S0PrintfBufBase.regs_ok_by_idx. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth pf_sr S0PrintfBufBase.allregs32 edenot].
    1: apply getr_zero.
    1: exact R1.
    1: exact R2.
    9: exact R11.
    all: rewrite ev_junk by lia; f_equal; apply bv_eq; reflexivity.
  Qed.

  Lemma wseg_data : wseg_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (Z_to_bv 64 0x1f000) 204800 = true.
  Proof. exact S0PrintfBufBase.wseg_data. Qed.

  Lemma data_store_ok : forall m a n,
    0x1f000 <= a -> a + Z.of_nat n <= 0x51000 -> store_ok (run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 a) n = true.
  Proof.
    exact S0PrintfBufBase.data_store_ok.
  Qed.

  Lemma pf_know_ok : know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E mem pf_kn.
  Proof.
    destruct PH. pose proof (u64_range sp) as Hsp.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    unfold pf_kn. repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot]. rewrite ev0. assumption.
    - apply krange_intro. cbn [edenot]. rewrite ev0. lia.
    - apply (kwr_of_stk_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E mem (EVar 0) sp 1200); [apply ev0 | exact Pstk0 | unfold PF_FR; lia].
    - apply kimg_intro; [lia | lia | exact Pimg3].
    - apply kimg_intro; [lia | lia | exact Pimg4].
    - eapply (kword_intro (run_segments RSEGS rc_inp rc_sp rc_mb) E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pgot0].
    - eapply (kword_intro (run_segments RSEGS rc_inp rc_sp rc_mb) E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pflags0].
    - eapply (kword_intro (run_segments RSEGS rc_inp rc_sp rc_mb) E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pwend0].
    - eapply (kword_intro (run_segments RSEGS rc_inp rc_sp rc_mb) E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | apply ev1 | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pwpos0].
    - apply krange_intro. cbn [edenot]. rewrite ev1, u64_lit by lia. lia.
    - eapply (kword_intro (run_segments RSEGS rc_inp rc_sp rc_mb) E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pbsz0].
    - eapply (kword_intro (run_segments RSEGS rc_inp rc_sp rc_mb) E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Plock0].
    - eapply (kword_intro (run_segments RSEGS rc_inp rc_sp rc_mb) E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Plbf0].
    - eapply (kword_intro (run_segments RSEGS rc_inp rc_sp rc_mb) E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | apply ev2 | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pcan0].
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
      split; [lia|]. intros d m Hd Hm. apply data_store_ok; lia.
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite ev1, u64_lit by lia.
      split; [lia|]. intros d m Hd Hm. apply data_store_ok; lia.
  Qed.
End Entry.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition pf_stops : list Z := [0x140fc].
Definition pf_fuel : nat := 3000.

Definition pf_regions : list sregion :=
  [(SA (EVar 0) (-1056), 1056); (SA (ELit 0) 0x1f8b0, 4); (SA (ELit 0) 0x1f8d8, 8); (SA (EVar 1) 0, 2)].

Definition pf_post {RCa1 : RunCtx}  (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w : Z) : Prop :=
  exists regs' mem',
    msteps (run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (Z_to_bv 64 0x141a8) mem rom) (mkst regs' (Z_to_bv 64 0x140fc) mem' rom)
    /\ keeps_cs regs regs'
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0x1f8b0, 4);
                          (Z_to_bv 64 0x1f8d8, 8); (Z_to_bv 64 w, 2)]
    /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem' (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]
    /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem' (Z_to_bv 64 0x1f8d8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 2)))
    /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem' (Z_to_bv 64 0x1f8b0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)).


Section Package.
Context {RCa1 : RunCtx}.
  Variables (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w can : Z).
  Hypothesis PH : pfH2 mem sp w can.
  Hypothesis R1 : getr regs 1 = Z_to_bv 64 0x140fc.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 0.

  Let E := pfE regs sp w can.

  Lemma adenot_lit0 : forall k, 0 <= k < 2 ^ 64 -> adenot E (SA (ELit 0) k) = Z_to_bv 64 k.
  Proof.
    intros k Hk. unfold adenot. cbn [a_base a_off edenot]. unfold v_addi.
    rewrite u64_lit by lia. f_equal; lia.
  Qed.

  Lemma adenot_var1 : forall k, adenot E (SA (EVar 1) k) = Z_to_bv 64 (w + k).
  Proof.
    intros k. destruct PH. unfold adenot. cbn [a_base a_off edenot].
    change (ev E 1) with (Z_to_bv 64 w). unfold v_addi. rewrite u64_lit by lia. reflexivity.
  Qed.

  Lemma pf_case : forall dirs ss' scs scr' kn' hs',
    sym_exec (run_segments RSEGS rc_inp rc_sp rc_mb) pf_fuel true pf_stops (SCR dirs [] []) (SS 0x141a8 pf_sr [] pf_kn 40) [] = (ss', scs, scr') ->
    s_pc ss' = 0x140fc ->
    log_covered pf_regions (s_log ss') = true ->
    same_regs pf_sr (s_regs ss') callee_saved = true ->
    carry (s_log ss') pf_kn [] = (kn', [], hs') ->
    kread (run_segments RSEGS rc_inp rc_sp rc_mb) kn' (ELit 0) 0x1f8d8 8 = Some (EAlu ALU_ADD (EVar 1) (ELit 2)) ->
    kread (run_segments RSEGS rc_inp rc_sp rc_mb) kn' (ELit 0) 0x1f8b0 4 = Some (ELit 5) ->
    kread (run_segments RSEGS rc_inp rc_sp rc_mb) kn' (EVar 1) 0 1 = Some (ELit 48) ->
    kread (run_segments RSEGS rc_inp rc_sp rc_mb) kn' (EVar 1) 1 1 = Some (ELit 10) ->
    scs_denot (run_segments RSEGS rc_inp rc_sp rc_mb) mem E scs ->
    pf_post regs mem rom sp w.
  Proof.
    intros dirs ss' scs scr' kn' hs' Hrun Hpc Hcov Hsame Hcarry K1 K2 K3 K4 Hsc.
    pose proof (pf_regs_ok regs sp w can R1 R2 R11) as HR.
    pose proof (pf_know_ok regs mem sp w can PH) as HK.
    fold E in HR, HK.
    destruct (run_sound (run_segments RSEGS rc_inp rc_sp rc_mb) pf_fuel pf_stops (SCR dirs [] []) 0x141a8 pf_sr pf_kn 40 ss' scs scr' E mem rom regs
                Hrun HR HK Hsc) as (R' & HR' & Hlf & Hms).
    rewrite Hpc in Hms.
    assert (HK' : know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E (mem_denot E mem (s_log ss')) kn').
    { eapply carry_after; [exact Hcarry | exact Hlf | exact HK | constructor]. }
    destruct PH. pose proof (u64_range sp) as Hsp.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    assert (Hw1 : ev E 1 = Z_to_bv 64 w) by reflexivity.
    exists R', (mem_denot E mem (s_log ss')).
    split; [exact Hms|]. split; [|split; [|split; [|split]]].
    - eapply (keeps_cs_of_same E); eassumption.
    - replace [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0x1f8b0, 4);
               (Z_to_bv 64 0x1f8d8, 8); (Z_to_bv 64 w, 2)]
        with (map (rdenot E) pf_regions).
      2:{ unfold pf_regions, rdenot, estart. cbn [map fst snd a_base a_off edenot].
          change (ev E 0) with sp. rewrite Hw1, Z0, (u64_lit w) by lia.
          repeat (f_equal; [try (f_equal; lia)..]). all: f_equal; lia. }
      apply log_covered_frame; [exact Hcov | | exact Hlf].
      intros r Hr. unfold pf_regions in Hr. cbn [In] in Hr.
      unfold flat, estart.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd a_base a_off edenot];
        try change (ev E 0) with sp; rewrite ?Hw1, ?Z0, ?(u64_lit w) by lia; lia.
    - pose proof (kread_rdn (run_segments RSEGS rc_inp rc_sp rc_mb) E _ kn' (EVar 1) 0 1 _ HK' K3 ltac:(lia) ltac:(lia)) as B0.
      pose proof (kread_rdn (run_segments RSEGS rc_inp rc_sp rc_mb) E _ kn' (EVar 1) 1 1 _ HK' K4 ltac:(lia) ltac:(lia)) as B1.
      rewrite adenot_var1 in B0, B1.
      apply rdn_2.
      + rewrite u64_lit by lia. lia.
      + rewrite Z.add_0_r in B0. apply B0.
        unfold flat, estart. cbn [a_base a_off edenot]. rewrite Hw1, (u64_lit w) by lia. lia.
      + rewrite u64_lit by lia. apply B1.
        unfold flat, estart. cbn [a_base a_off edenot]. rewrite Hw1, (u64_lit w) by lia. lia.
    - pose proof (kread_rdn (run_segments RSEGS rc_inp rc_sp rc_mb) E _ kn' (ELit 0) 0x1f8d8 8 _ HK' K1 ltac:(lia) ltac:(lia)) as B.
      rewrite adenot_lit0 in B by lia. cbn [edenot] in B. rewrite Hw1, alu_add_Z in B.
      apply B. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0. lia.
    - pose proof (kread_rdn (run_segments RSEGS rc_inp rc_sp rc_mb) E _ kn' (ELit 0) 0x1f8b0 4 _ HK' K2 ltac:(lia) ltac:(lia)) as B.
      rewrite adenot_lit0 in B by lia. cbn [edenot] in B.
      apply B. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0. lia.
  Qed.
End Package.


Ltac sc_bool :=
  match goal with
  | Hw4 : ?w mod 4 = ?r |- _ =>
      first [ rewrite (mod4_shift w _ r Hw4); reflexivity
            | rewrite Hw4; reflexivity ]
  end.

Ltac sc_pf :=
  cbn [sc_denot edenot ev pfE vals_ev pf_vals nth app];
  first
    [ rewrite lin_neg1_val, u64_lit by lia; first [ apply bt_geu_Z; lia | apply bt_geu_Z_false; lia ]
    | apply bt_and3; [lia | cbv beta iota; sc_bool]
    | apply bt_and3_0; [lia | cbv beta iota; sc_bool] ].


Definition pf_run {RCa1 : RunCtx}  (dirs : list bool) :=
  sym_exec (run_segments RSEGS rc_inp rc_sp rc_mb) pf_fuel true pf_stops (SCR dirs [] []) (SS 0x141a8 pf_sr [] pf_kn 40) [].

Definition dirsA : list bool := [false; false; false; true; false].
Definition dirsB : list bool := [true; true; true; true; true].

Definition dirsC : list bool := [true; true; true; true; false].
Definition dirsD : list bool := [true; true; true; false; false].

Definition resA {RCa1 : RunCtx}  := Eval vm_compute in (pf_run dirsA).
Definition carA {RCa1 : RunCtx}  := Eval vm_compute in (carry (s_log (fst (fst resA))) pf_kn []).
Definition resB {RCa1 : RunCtx}  := Eval vm_compute in (pf_run dirsB).
Definition carB {RCa1 : RunCtx}  := Eval vm_compute in (carry (s_log (fst (fst resB))) pf_kn []).
Definition resC {RCa1 : RunCtx}  := Eval vm_compute in (pf_run dirsC).
Definition carC {RCa1 : RunCtx}  := Eval vm_compute in (carry (s_log (fst (fst resC))) pf_kn []).
Definition resD {RCa1 : RunCtx}  := Eval vm_compute in (pf_run dirsD).
Definition carD {RCa1 : RunCtx}  := Eval vm_compute in (carry (s_log (fst (fst resD))) pf_kn []).

Ltac run_case dirs res car :=
  lazymatch goal with
  | PH : pfH2 ?mem ?sp ?w ?can, R1 : getr ?regs 1 = _, R2 : getr _ 2 = _, R11 : getr _ 11 = _ |- pf_post _ _ ?rom _ _ =>
      eapply (pf_case regs mem rom sp w can PH R1 R2 R11 dirs
                (fst (fst res)) (snd (fst res)) (snd res) (fst (fst car)) (snd car));
      [ vm_compute; reflexivity
      | reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | let v := eval vm_compute in (snd (fst res)) in
        change (snd (fst res)) with v;
        destruct PH; split_scs; sc_pf ]
  end.

Lemma pf_caseA {RCa1 : RunCtx}  : forall regs mem rom sp w can,
  pfH2 mem sp w can -> w mod 4 = 0 ->
  getr regs 1 = Z_to_bv 64 0x140fc -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsA resA carA. Qed.

Lemma pf_caseB {RCa1 : RunCtx}  : forall regs mem rom sp w can,
  pfH2 mem sp w can -> w mod 4 = 2 ->
  getr regs 1 = Z_to_bv 64 0x140fc -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsB resB carB. Qed.

Lemma pf_caseC {RCa1 : RunCtx}  : forall regs mem rom sp w can,
  pfH2 mem sp w can -> w mod 4 = 1 ->
  getr regs 1 = Z_to_bv 64 0x140fc -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsC resC carC. Qed.

Lemma pf_caseD {RCa1 : RunCtx}  : forall regs mem rom sp w can,
  pfH2 mem sp w can -> w mod 4 = 3 ->
  getr regs 1 = Z_to_bv 64 0x140fc -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  pf_post regs mem rom sp w.
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsD resD carD. Qed.


Theorem printf0_buffered2 {RCa1 : RunCtx}  : forall regs mem rom (sp : word) (w can : Z),
  pfH2 mem sp w can ->
  getr regs 1 = Z_to_bv 64 0x140fc -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  exists regs' mem',
    msteps (run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (Z_to_bv 64 0x141a8) mem rom) (mkst regs' (Z_to_bv 64 0x140fc) mem' rom)
    /\ keeps_cs regs regs'
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0x1f8b0, 4);
                          (Z_to_bv 64 0x1f8d8, 8); (Z_to_bv 64 w, 2)]
    /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem' (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]
    /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem' (Z_to_bv 64 0x1f8d8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 2)))
    /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem' (Z_to_bv 64 0x1f8b0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)).
Proof.
  intros regs mem rom sp w can PH R1 R2 R11.
  destruct (mod4_cases w) as [H0|[H1|[H2|H3]]].
  - exact (pf_caseA regs mem rom sp w can PH H0 R1 R2 R11).
  - exact (pf_caseC regs mem rom sp w can PH H1 R1 R2 R11).
  - exact (pf_caseB regs mem rom sp w can PH H2 R1 R2 R11).
  - exact (pf_caseD regs mem rom sp w can PH H3 R1 R2 R11).
Qed.



Lemma zero_lines_snoc : forall k, Spec.zero_lines (S k) = Spec.zero_lines k ++ [Z_to_bv 8 48; Z_to_bv 8 10].
Proof.
  induction k as [|k IH]; [reflexivity|].
  change (Spec.zero_lines (S (S k))) with (Z_to_bv 8 48 :: Z_to_bv 8 10 :: Spec.zero_lines (S k)).
  rewrite IH at 1. reflexivity.
Qed.

Theorem printf0_next {RCa1 : RunCtx}  : printf0_next_stmt.
Proof.
  intros regs mem rom sp can k PP SO Hk R1 R2 R11.
  destruct PP as [P16 Plo Phi Pstk Pimg Pgot Pcan Pcan64]. unfold PF1_FR in *.
  destruct SO as [Sk F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 FB].
  pose proof (u64_range sp) as Hsp.
  set (w := 0x501d8 + 2 * Z.of_nat k) in *.
  assert (Hw : 0x501d8 <= w <= 0x505d6) by (subst w; lia).
  assert (PH : pfH2 mem sp w can).
  { constructor; try assumption; try lia.
    - intros i Hi. apply Pimg. lia.
    - intros i Hi. apply Pimg. lia. }
  destruct (printf0_buffered2 regs mem rom sp w can PH R1 R2 R11) as (regs' & mem' & Hms & Hcs & Hfm & Hb & Hwp & Hfl).
  exists regs', mem'. split; [exact Hms|]. split; [exact Hcs|].
  assert (OUT : forall a : word, outside a (so_regions sp) ->
                  outside a [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0x1f8b0, 4);
                             (Z_to_bv 64 0x1f8d8, 8); (Z_to_bv 64 w, 2)]).
  { intros a Ha. unfold so_regions, PF1_FR in Ha. cbn [outside] in Ha |- *. unfold in_rng in *.
    rewrite !u64_lit in Ha by lia. rewrite !u64_lit by lia. lia. }
  split; [eapply frame_mod_weaken; [exact OUT | exact Hfm]|].
  assert (KEEP : forall a n bs, rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 a) n = Some bs ->
                   0x1f8b0 <= a -> a + Z.of_nat n <= 0x505d8 ->
                   (a + Z.of_nat n <= 0x1f8b0 \/ 0x1f8b4 <= a) -> (a + Z.of_nat n <= 0x1f8d8 \/ 0x1f8e0 <= a) ->
                   (a + Z.of_nat n <= w \/ w + 2 <= a) ->
                   rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem' (Z_to_bv 64 a) n = Some bs).
  { intros a n bs Hr A1 A2 A3 A4 A5. rewrite <- Hr. apply (frame_mod_rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem mem' _ n (Z_to_bv 64 a) Hfm).
    - intros i Hi. rewrite u64_lit by lia. cbn [outside]. unfold in_rng. rewrite !u64_lit by lia. lia.
    - rewrite u64_lit by lia. lia. }
  constructor.
  - lia.
  - exact Hfl.
  - apply KEEP; [exact F2 | cbn; lia ..].
  - apply KEEP; [exact F3 | cbn; lia ..].
  - apply KEEP; [exact F4 | cbn; lia ..].
  - rewrite Hwp. do 3 f_equal. subst w. lia.
  - apply KEEP; [exact F6 | cbn; lia ..].
  - apply KEEP; [exact F7 | cbn; lia ..].
  - apply KEEP; [exact F8 | cbn; lia ..].
  - apply KEEP; [exact F9 | cbn; lia ..].
  - apply KEEP; [exact F10 | cbn; lia ..].
  - apply KEEP; [exact F11 | cbn; lia ..].
  - apply KEEP; [exact F12 | cbn; lia ..].
  - apply KEEP; [exact F13 | cbn; lia ..].
  - rewrite zero_lines_snoc, length_app. cbn [length].
    apply rdn_app_Z; [ | | lia | rewrite zero_lines_length; lia].
    + apply KEEP; [exact FB | lia | rewrite zero_lines_length; lia ..].
    + rewrite zero_lines_length. replace (0x501d8 + Z.of_nat (2 * k)) with w by (subst w; lia). exact Hb.
Qed.

Theorem printf0_next_rz {RCa1 : RunCtx}  : printf0_next_rz_stmt.
Proof. exact (printf0_next_rz_of printf0_next). Qed.
