(* check_as_written (fs.asan 0x81590): the RE-KEY at the scan loop's exit 0x81724, from the scan loop's exit state
   (FSW_caw_scan.v caw_ssX: regions [caw_stk], atom facts 2 32 33 34 35 38 39) to the state the tail segment and the
   accept arms take (FSW_caw_tail.v cawt_ss 0 255 0 2147483647: regions [caw_stk; cawt_txt]; atom 37 the byte at the
   text pointer, atom 40 six + m with the alias six + m, atom 43 six[m - 1]; the scratch registers t0 t1 t2 a1 a2 a5 a6
   a7 t3 t4 t5 t6 on the fresh atoms 50 .. 61) and its shadow entry (FSW_caw_tail.v cawt_SH, the byte at the text
   pointer).
   No instruction runs: the machine state is the same on both sides, only the env changes (cawr_env: atoms 37, 40,
   43 and 50 .. 61 are set, every other atom is kept, cawr_env_old).
   Method: YL09.st_ok_reabs (registers and regions, with no facts), then YP06.st_ok_facts (the tail's facts).
   Two premises come from the scan loop's caw_static (FSW_caw_scan.v), not from caw_ssX: `4096 <= txt` (the text
   pointer is a true unsigned value, so cawt_txt's base is txt) and `txt + 1 <= bv_unsigned (ew E 2) - 48` (cawt_txt
   is disjoint from the frame caw_stk; caw_static gives t + |tb| + 8 <= alloc_ceiling <= spE - 48).
   rule 24: no function proved here (no instruction runs). Section hypotheses: none. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YL02 YL09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AF0l FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSW_K FSW_caw_defs FSW_caw_model FSW_caw_scan
FSW_caw_tail.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the env of the tail state: atoms 37 (the byte at the text pointer), 40 (six + m), 43 (six[m - 1]) and the
   twelve scratch registers t0 t1 t2 a1 a2 a5 a6 a7 t3 t4 t5 t6 on 50 .. 61; every other atom is kept ---- *)
Definition cawr_P (n : nat) : bool :=
  negb (Nat.eqb n 37 || Nat.eqb n 40 || Nat.eqb n 43 || ((49 <? n)%nat && (n <? 62)%nat)).
Definition cawr_env (E : env) (regs : bvmap 5 word) (b37 q40 b43 : word) : env :=
  havoc (havoc (havoc (havoc E 37 [b37]) 40 [q40]) 43 [b43]) 50
    [getr regs 5%bv; getr regs 6%bv; getr regs 7%bv; getr regs 11%bv; getr regs 12%bv;
     getr regs 15%bv; getr regs 16%bv; getr regs 17%bv;
     getr regs 28%bv; getr regs 29%bv; getr regs 30%bv; getr regs 31%bv].

Lemma cawr_havoc_out : forall E k ws i, (i < k \/ k + length ws <= i)%nat -> ew (havoc E k ws) i = ew E i.
Proof.
intros E k ws i [H|H]; [apply ew_havoc_old; exact H|].
unfold havoc. cbn [ew]. destruct (Nat.ltb i k); [reflexivity|]. apply nth_overflow. lia.
Qed.
Lemma cawr_env_old : forall E regs b q l n, cawr_P n = true -> ew (cawr_env E regs b q l) n = ew E n.
Proof.
intros E regs b q l n. unfold cawr_P.
destruct (Nat.eqb_spec n 37); destruct (Nat.eqb_spec n 40); destruct (Nat.eqb_spec n 43);
  destruct (Nat.ltb_spec 49 n); destruct (Nat.ltb_spec n 62); cbn [orb andb negb]; intros Hn; try discriminate;
  unfold cawr_env; rewrite !cawr_havoc_out by (cbn [length]; lia); reflexivity.
Qed.
Lemma cawr_env_37 : forall E regs b q l, ew (cawr_env E regs b q l) 37 = b.
Proof. reflexivity. Qed.
Lemma cawr_env_40 : forall E regs b q l, ew (cawr_env E regs b q l) 40 = q.
Proof. reflexivity. Qed.
Lemma cawr_env_43 : forall E regs b q l, ew (cawr_env E regs b q l) 43 = l.
Proof. reflexivity. Qed.
Lemma cawr_agree : forall E regs b q l, env_agree_pd cawr_P PT E (cawr_env E regs b q l).
Proof. intros E regs b q l. split; [intros n Hn; apply cawr_env_old; exact Hn | intros d _; reflexivity]. Qed.
(* the register obligations of the re-key: the twelve scratch registers are the atoms 50 .. 61 *)
Lemma cawr_obl : forall E regs b q l,
  Forall (fun rj : bv 5 * nat => ew (cawr_env E regs b q l) (snd rj) = getr regs (fst rj)) (reabs_obl cawr_P cawt_regs).
Proof.
intros E regs b q l.
match goal with |- Forall _ ?l => let l' := eval vm_compute in l in change l with l' end.
repeat constructor.
Qed.
(* a kept atom keeps its facts; the registers on kept atoms are equal in caw_regs1 and cawt_regs, the twelve scratch
   slots are fresh atoms, and the target facts are empty (the tail's facts go on with st_ok_facts) *)
Lemma cawr_keep : forall E regs b q l n f, cawr_P n = true -> afact_ok E n f -> afact_ok (cawr_env E regs b q l) n f.
Proof. intros E regs b q l n f Hn Hf. unfold afact_ok in *. rewrite (cawr_env_old E regs b q l n Hn). exact Hf. Qed.
Lemma cawr_check : reabs_check cawr_P caw_ssX cawt_regs (mkFacts [] [] []) = true.
Proof. vm_compute. reflexivity. Qed.

Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* the scan loop's exit state at 0x81724, re-keyed into the tail's state at 0x81724 and its shadow entry *)
Lemma caw_rekey_tail : forall (W : world tfibsegs) (E : env) (ms : machine_state) (six m txt byt lastv : Z),
  st_ok tfibsegs E caw_ssX (restrict (w_H W) ms) ->
  ew E 33 = Z_to_bv 64 six -> ew E 35 = Z_to_bv 64 txt -> ew E 38 = Z_to_bv 64 m ->
  0 <= m -> 4096 <= six -> six + m <= CAW_CEIL ->
  0 <= byt <= 255 -> 0 <= lastv <= 63 ->
  4096 <= txt -> txt + 1 <= bv_unsigned (ew E 2) - 48 ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) txt 1 byt ->
  range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms))) SHADOW_OFF txt 1 ->
  (forall x, txt <= x < txt + 1 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) ->
  st_ok tfibsegs (cawr_env E (ms_regs ms) (Z_to_bv 64 byt) (Z_to_bv 64 (six + m)) (Z_to_bv 64 lastv))
        (cawt_ss 0 255 0 2147483647) (restrict (w_H W) ms) /\
  sh_ok tfibsegs caw_Bx cawt_SH (cawr_env E (ms_regs ms) (Z_to_bv 64 byt) (Z_to_bv 64 (six + m)) (Z_to_bv 64 lastv))
        (mrestrict (w_H W) (ms_mem ms)).
Proof.
intros W E ms six m txt byt lastv HS E33 E35 E38 Hm Hsix Hce Hbyt Hlv Htx0 Hdis VB RA Hsep.
assert (CC : CAW_CEIL < 2 ^ 64) by (unfold CAW_CEIL; lia).
pose proof (st_ok_facts_ok tfibsegs E caw_ssX _ HS) as (HA0 & _ & _).
unfold caw_ssX, caw_factsX in HA0. cbn [ss_facts f_atoms atoms_ok] in HA0.
destruct HA0 as (F2 & F32 & F33 & F34 & F35 & F38 & F39 & _).
pose proof F2 as (Hsp & _). cbn [af_lo af_hi] in Hsp.
pose proof F32 as (H32 & _). cbn [af_lo af_hi] in H32.
set (E2 := cawr_env E (ms_regs ms) (Z_to_bv 64 byt) (Z_to_bv 64 (six + m)) (Z_to_bv 64 lastv)).
assert (EK : forall n, cawr_P n = true -> ew E2 n = ew E n) by (intros n Hn; unfold E2; apply cawr_env_old; exact Hn).
assert (KP : forall n f, cawr_P n = true -> afact_ok E n f -> afact_ok E2 n f) by (intros n f; unfold E2; apply cawr_keep).
assert (E37' : ew E2 37 = Z_to_bv 64 byt) by reflexivity.
assert (E40' : ew E2 40 = Z_to_bv 64 (six + m)) by reflexivity.
assert (E43' : ew E2 43 = Z_to_bv 64 lastv) by reflexivity.
assert (E2' : ew E2 2 = ew E 2) by (apply EK; reflexivity).
assert (E33' : ew E2 33 = Z_to_bv 64 six) by (rewrite (EK 33%nat eq_refl); exact E33).
assert (E35' : ew E2 35 = Z_to_bv 64 txt) by (rewrite (EK 35%nat eq_refl); exact E35).
assert (E38' : ew E2 38 = Z_to_bv 64 m) by (rewrite (EK 38%nat eq_refl); exact E38).
assert (U32 : bv_unsigned (ew E2 32) = SHADOW_OFF) by (rewrite (EK 32%nat eq_refl); lia).
assert (U35 : bv_unsigned (ew E2 35) = txt) by (rewrite E35'; apply unsigned_lit_small; lia).
assert (HA : env_agree_pd cawr_P PT E E2) by (unfold E2; apply cawr_agree).
(* the regions: the frame from the exit state, the byte at the text pointer from the premise *)
assert (HM : mem_ok tfibsegs E2 (ms_mem (restrict (w_H W) ms)) [caw_stk; cawt_txt]).
{ split; [vm_compute; reflexivity|]. split.
  - constructor; [|constructor; [|constructor]].
    + pose proof (fsw_region_nth E caw_ssX (restrict (w_H W) ms) 0 caw_stk HS eq_refl) as R0.
      assert (HP : region_atoms_pd cawr_P PT caw_stk = true) by (vm_compute; reflexivity).
      exact (region_ok_agree_pd tfibsegs cawr_P PT E E2 (ms_mem (restrict (w_H W) ms)) caw_stk HA HP R0).
    + unfold region_ok, cawt_txt. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U35. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val tfibsegs E2 _ txt 0 1%N (SOff 37 0) byt);
        [rewrite fsw_SOff0; exact E37' | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact VB.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, caw_stk, cawt_txt.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E2', U35. split; [split; [right; lia | exact I] | split; exact I]. }
assert (HFO : Forall (fun nf : nat * afact => afact_ok E2 (fst nf) (snd nf)) (fact_obls cawr_P (mkFacts [] [] [])))
  by (cbn; apply Forall_nil).
pose proof (st_ok_reabs tfibsegs cawr_P E E2 caw_ssX (restrict (w_H W) ms) cawt_regs [caw_stk; cawt_txt]
  (mkFacts [] [] []) HS HA cawr_check
  (cawr_obl E (ms_regs ms) (Z_to_bv 64 byt) (Z_to_bv 64 (six + m)) (Z_to_bv 64 lastv)) HFO HM) as HS'.
(* the tail's facts: the kept atoms from the exit state, 37 40 43 and the alias six + m from the premises *)
assert (HF : facts_ok E2 (cawt_facts 0 255 0 2147483647)).
{ unfold facts_ok, cawt_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I | split; [|exact I]]].
  - split.
    { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E37', unsigned_lit_small by lia.
      rewrite Z.pow_0_r, Z.mod_1_r. lia. }
    split; [exact (KP 39%nat _ eq_refl F39)|].
    split; [exact (KP 2%nat _ eq_refl F2)|].
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
split.
- exact (st_ok_facts tfibsegs E2 _ _ (cawt_facts 0 255 0 2147483647) HS' HF).
- unfold sh_ok, cawt_SH. constructor; [|constructor].
  assert (UB : U E2 caw_Bx = SHADOW_OFF) by (unfold U, caw_Bx; rewrite fsw_SOff0; exact U32).
  assert (UT : U E2 (SOff 35 0) = txt) by (unfold U; rewrite fsw_SOff0; exact U35).
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite UB, UT. split.
  + rewrite Z.add_0_r, Z.sub_0_r. exact RA.
  + intros a Ha. apply Hsep. lia.
Qed.

End R.
