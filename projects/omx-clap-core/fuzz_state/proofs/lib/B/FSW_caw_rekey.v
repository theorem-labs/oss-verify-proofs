(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_caw_rekey.v (a working branch),
   the same names over B's own states, plus the re-key B's second scan exit needs (caw_rekey_break).
   rule 24: proves no function (kind: segment lemma; check_as_written, B 0x8164c, CONFIRM by a Theorem Labs lane). *)
(* check_as_written over fs.asan-ubsan (B 0x8164c): the RE-KEYS at the scan loop's two exits.
   - caw_rekey_tail: from the NUL exit state (FSW_caw_scan.v caw_ssX at 0x81804: regions [caw_stk], atom facts 2 30
     32 33 34 35 38 39) to the state the tail segment and the accept arms take (FSW_caw_tail.v cawt_ss 0 3145728:
     atom 40 six + m with the alias six + m, atom 43 six[m - 1]; the scratch registers t0 t1 t2 a1 a2 a5 a6 a7 t4 t5
     t6 s5 on the fresh atoms 50 .. 61).
   - caw_rekey_break: from the refused-character exit state (FSW_caw_scan.v caw_ssB at 0x81a78, s5 = SIZE_MAX) to
     the common exit state FSW_caw_accept.v caa_xss with the answer n = SIZE_MAX in atom 49 (A had no such exit:
     its scan left at one pc for both).
   No instruction runs: the machine state is the same on both sides, only the env changes.
   Method: YL09.st_ok_reabs (registers and regions), then YP06.st_ok_facts (the tail's facts); for the break, the
   accept file's caa_exit_st with the env extension of caa_mkexit.
   Section hypotheses: none. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP05 YL01 YL02 YL07 YL09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w FSH_Base FSH_Rt FSW_K
FSW_caw_defs FSW_caw_model FSW_caw_scan FSW_caw_tail FSW_caw_emit FSW_caw_accept.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- the env of the tail state: atoms 40 (six + m), 43 (six[m - 1]) and the twelve scratch registers t0 t1 t2 a1
   a2 a5 a6 a7 t4 t5 t6 s5 on 50 .. 61; every other atom is kept ---- *)
Definition cawr_P (n : nat) : bool :=
  negb (Nat.eqb n 40 || Nat.eqb n 43 || ((49 <? n)%nat && (n <? 62)%nat)).
Definition cawr_env (E : env) (regs : bvmap 5 word) (q40 b43 : word) : env :=
  havoc (havoc (havoc E 40 [q40]) 43 [b43]) 50
    [getr regs 5%bv; getr regs 6%bv; getr regs 7%bv; getr regs 11%bv; getr regs 12%bv;
     getr regs 15%bv; getr regs 16%bv; getr regs 17%bv;
     getr regs 29%bv; getr regs 30%bv; getr regs 31%bv; getr regs 21%bv].

Lemma cawr_havoc_out : forall E k ws i, (i < k \/ k + length ws <= i)%nat -> ew (havoc E k ws) i = ew E i.
Proof.
intros E k ws i [H|H]; [apply ew_havoc_old; exact H|].
unfold havoc. cbn [ew]. destruct (Nat.ltb i k); [reflexivity|]. apply nth_overflow. lia.
Qed.
Lemma cawr_env_old : forall E regs q l n, cawr_P n = true -> ew (cawr_env E regs q l) n = ew E n.
Proof.
intros E regs q l n. unfold cawr_P.
destruct (Nat.eqb_spec n 40); destruct (Nat.eqb_spec n 43);
  destruct (Nat.ltb_spec 49 n); destruct (Nat.ltb_spec n 62); cbn [orb andb negb]; intros Hn; try discriminate;
  unfold cawr_env; rewrite !cawr_havoc_out by (cbn [length]; lia); reflexivity.
Qed.
Lemma cawr_env_40 : forall E regs q l, ew (cawr_env E regs q l) 40 = q.
Proof. reflexivity. Qed.
Lemma cawr_env_43 : forall E regs q l, ew (cawr_env E regs q l) 43 = l.
Proof. reflexivity. Qed.
Lemma cawr_agree : forall E regs q l, env_agree_pd cawr_P PT E (cawr_env E regs q l).
Proof. intros E regs q l. split; [intros n Hn; apply cawr_env_old; exact Hn | intros d _; reflexivity]. Qed.
(* the register obligations of the re-key: the twelve scratch registers are the atoms 50 .. 61 *)
Lemma cawr_obl : forall E regs q l,
  Forall (fun rj : bv 5 * nat => ew (cawr_env E regs q l) (snd rj) = getr regs (fst rj)) (reabs_obl cawr_P cawt_regs).
Proof.
intros E regs q l.
match goal with |- Forall _ ?l => let l' := eval vm_compute in l in change l with l' end.
repeat constructor.
Qed.
(* a kept atom keeps its facts; the registers on kept atoms are equal in caw_regs1 and cawt_regs, the twelve scratch
   slots are fresh atoms, and the target facts are empty (the tail's facts go on with st_ok_facts) *)
Lemma cawr_keep : forall E regs q l n f, cawr_P n = true -> afact_ok E n f -> afact_ok (cawr_env E regs q l) n f.
Proof. intros E regs q l n f Hn Hf. unfold afact_ok in *. rewrite (cawr_env_old E regs q l n Hn). exact Hf. Qed.
Lemma cawr_check : reabs_check cawr_P caw_ssX cawt_regs (mkFacts [] [] []) = true.
Proof. vm_compute. reflexivity. Qed.

(* the register obligations of a re-key onto caa_xss: every atom from 44 up is set by the extension list
   (FSW_caw_accept.v's caa_lk is Section-local there, so it is restated here) *)
Ltac cawr_lk EL LD :=
  lazymatch goal with
  | |- ew _ ?j = _ =>
      let jj := eval compute in (Nat.sub j 44) in
      change j with (44 + jj)%nat; rewrite (EL jj ltac:(lia)); unfold LD; cbn [nth]; reflexivity
  end.

Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* the scan loop's NUL exit state at 0x81804, re-keyed into the tail's state at 0x81804 *)
Lemma caw_rekey_tail : forall (W : world tfibsegs) (E : env) (ms : machine_state) (six m lastv : Z),
  st_ok tfibsegs E caw_ssX (restrict (w_H W) ms) ->
  ew E 33 = Z_to_bv 64 six -> ew E 38 = Z_to_bv 64 m ->
  0 <= m -> 4096 <= six -> six + m <= CAW_CEIL ->
  0 <= lastv <= 63 ->
  st_ok tfibsegs (cawr_env E (ms_regs ms) (Z_to_bv 64 (six + m)) (Z_to_bv 64 lastv))
        (cawt_ss 0 3145728) (restrict (w_H W) ms).
Proof.
intros W E ms six m lastv HS E33 E38 Hm Hsix Hce Hlv.
assert (CC : CAW_CEIL < 2 ^ 64) by (unfold CAW_CEIL; lia).
pose proof (st_ok_facts_ok tfibsegs E caw_ssX _ HS) as (HA0 & _ & _).
unfold caw_ssX, caw_ssXp, caw_factsX in HA0. cbn [ss_facts f_atoms atoms_ok] in HA0.
destruct HA0 as (F2 & F30 & F32 & F33 & F34 & F35 & F38 & F39 & _).
set (E2 := cawr_env E (ms_regs ms) (Z_to_bv 64 (six + m)) (Z_to_bv 64 lastv)).
assert (EK : forall n, cawr_P n = true -> ew E2 n = ew E n) by (intros n Hn; unfold E2; apply cawr_env_old; exact Hn).
assert (KP : forall n f, cawr_P n = true -> afact_ok E n f -> afact_ok E2 n f) by (intros n f; unfold E2; apply cawr_keep).
assert (E40' : ew E2 40 = Z_to_bv 64 (six + m)) by reflexivity.
assert (E43' : ew E2 43 = Z_to_bv 64 lastv) by reflexivity.
assert (E33' : ew E2 33 = Z_to_bv 64 six) by (rewrite (EK 33%nat eq_refl); exact E33).
assert (E38' : ew E2 38 = Z_to_bv 64 m) by (rewrite (EK 38%nat eq_refl); exact E38).
assert (HA : env_agree_pd cawr_P PT E E2) by (unfold E2; apply cawr_agree).
(* the region: the frame from the exit state *)
assert (HM : mem_ok tfibsegs E2 (ms_mem (restrict (w_H W) ms)) [caw_stk]).
{ split; [vm_compute; reflexivity|]. split.
  - constructor; [|constructor].
    pose proof (fsw_region_nth E caw_ssX (restrict (w_H W) ms) 0 caw_stk HS eq_refl) as R0.
    assert (HP : region_atoms_pd cawr_P PT caw_stk = true) by (vm_compute; reflexivity).
    exact (region_ok_agree_pd tfibsegs cawr_P PT E E2 (ms_mem (restrict (w_H W) ms)) caw_stk HA HP R0).
  - cbn [pairwise_disjoint all_disjoint]. split; exact I. }
assert (HFO : Forall (fun nf : nat * afact => afact_ok E2 (fst nf) (snd nf)) (fact_obls cawr_P (mkFacts [] [] [])))
  by (cbn; apply Forall_nil).
pose proof (st_ok_reabs tfibsegs cawr_P E E2 caw_ssX (restrict (w_H W) ms) cawt_regs [caw_stk]
  (mkFacts [] [] []) HS HA cawr_check
  (cawr_obl E (ms_regs ms) (Z_to_bv 64 (six + m)) (Z_to_bv 64 lastv)) HFO HM) as HS'.
(* the tail's facts: the kept atoms from the exit state, 40 43 and the alias six + m from the premises *)
assert (HF : facts_ok E2 (cawt_facts 0 3145728)).
{ unfold facts_ok, cawt_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I | split; [|exact I]]].
  - split; [exact (KP 39%nat _ eq_refl F39)|].
    split; [exact (KP 2%nat _ eq_refl F2)|].
    split; [exact (KP 30%nat _ eq_refl F30)|].
    split; [exact (KP 32%nat _ eq_refl F32)|].
    split; [exact (KP 33%nat _ eq_refl F33)|].
    split; [exact (KP 34%nat _ eq_refl F34)|].
    split; [exact (KP 35%nat _ eq_refl F35)|].
    split; [exact (KP 38%nat _ eq_refl F38)|].
    split.
    { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E40', unsigned_lit_small by lia.
      rewrite Z.pow_0_r, Z.mod_1_r. lia. }
    split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E43', unsigned_lit_small by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. lia.
  - cbn [sv_denot]. rewrite E33', E38', E40', !unsigned_lit_small by lia. rewrite !Z.add_0_r.
    apply alu_add_small; unfold M64; lia. }
exact (st_ok_facts tfibsegs E2 _ _ (cawt_facts 0 3145728) HS' HF).
Qed.

(* the scan loop's refused-character exit state at 0x81a78 (s5 = SIZE_MAX), re-keyed into the common exit state
   caa_xss with the answer n = SIZE_MAX in atom 49 *)
Lemma caw_rekey_break : forall (W : world tfibsegs) (E : env) (ms : machine_state),
  st_ok tfibsegs E caw_ssB (restrict (w_H W) ms) ->
  exists E2, env_agree 44 E E2 /\ st_ok tfibsegs E2 caa_xss (restrict (w_H W) ms)
             /\ ew E2 49 = Z_to_bv 64 SIZE_MAXZ.
Proof.
intros W E ms HS.
set (LD := [getr (ms_regs ms) 11%bv; getr (ms_regs ms) 12%bv; getr (ms_regs ms) 19%bv;
            getr (ms_regs ms) 22%bv; Z_to_bv 64 0; getr (ms_regs ms) 21%bv;
            getr (ms_regs ms) 5%bv; getr (ms_regs ms) 6%bv; getr (ms_regs ms) 7%bv;
            Z_to_bv 64 0; Z_to_bv 64 0;
            getr (ms_regs ms) 15%bv; getr (ms_regs ms) 16%bv; getr (ms_regs ms) 17%bv;
            getr (ms_regs ms) 28%bv; getr (ms_regs ms) 29%bv; getr (ms_regs ms) 30%bv;
            getr (ms_regs ms) 31%bv]).
set (E2 := extK E 44 LD).
assert (EL : forall j, (j < 18)%nat -> ew E2 (44 + j) = nth j LD (Z_to_bv 64 0))
  by (intros j Hj; unfold E2; apply cae_ext_lookup; unfold LD; cbn [length]; lia).
exists E2.
split; [unfold E2; apply env_agree_extK|].
split.
{ apply (caa_exit_st W E E2 ms caw_ssB HS); [reflexivity | reflexivity | vm_compute; reflexivity
  | unfold E2; apply env_agree_extK |].
  apply Forall_forall. intros rj Hin. vm_compute in Hin.
  repeat (destruct Hin as [<-|Hin]); [..|destruct Hin]; cbn [fst snd]; cawr_lk EL LD. }
change 49%nat with (44 + 5)%nat. rewrite (EL 5%nat ltac:(lia)). unfold LD. cbn [nth].
exact (fsw_reg_lit (w_H W) E caw_ssB ms 21%bv SIZE_MAXZ HS ltac:(vm_compute; reflexivity)
         ltac:(unfold SIZE_MAXZ; lia)).
Qed.

End R.
